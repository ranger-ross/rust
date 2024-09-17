#![allow(unused_imports)]
// ignore-tidy-filelength
//! "Late resolution" is the pass that resolves most of names in a crate beside imports and macros.
//! It runs when the crate is fully expanded and its module structure is fully built.
//! So it just walks through the crate and resolves all the expressions, types, etc.
//!
//! If you wonder why there's no `early.rs`, that's because it's split into three files -
//! `build_reduced_graph.rs`, `macros.rs` and `imports.rs`.

use std::assert_matches::debug_assert_matches;
use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::BTreeSet;
use std::mem::{replace, swap, take};

use rustc_ast::ptr::P;
use rustc_ast::visit::{visit_opt, walk_list, AssocCtxt, BoundKind, FnCtxt, FnKind, Visitor};
use rustc_ast::*;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_errors::codes::*;
use rustc_errors::{Applicability, DiagArgValue, IntoDiagArg, StashKey};
use rustc_hir::def::Namespace::{self, *};
use rustc_hir::def::{self, CtorKind, DefKind, LifetimeRes, NonMacroAttrKind, PartialRes, PerNS};
use rustc_hir::def_id::{DefId, LocalDefId, CRATE_DEF_ID, LOCAL_CRATE};
use rustc_hir::{MissingLifetimeKind, PrimTy, TraitCandidate};
use rustc_middle::middle::resolve_bound_vars::Set1;
use rustc_middle::ty::DelegationFnSig;
use rustc_middle::{bug, span_bug};
use rustc_session::config::{CrateType, ResolveDocLinks};
use rustc_session::lint::{self, BuiltinLintDiag};
use rustc_session::parse::feature_err;
use rustc_span::source_map::{respan, Spanned};
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::{BytePos, Span, SyntaxContext};
use smallvec::{smallvec, SmallVec};
use tracing::{debug, instrument, trace};
use visitor::LateResolutionVisitor;

use crate::{
    errors, path_names_to_string, rustdoc, BindingError, BindingKey, Finalize, LexicalScopeBinding,
    Module, ModuleOrUniformRoot, NameBinding, ParentScope, PathResult, ResolutionError, Resolver,
    Segment, TyCtxt, UseError, Used,
};

mod diagnostics;
mod util;
mod visitor;

type Res = def::Res<NodeId>;

type IdentMap<T> = FxHashMap<Ident, T>;

use diagnostics::{ElisionFnParameter, LifetimeElisionCandidate, MissingLifetime};

#[derive(Copy, Clone, Debug)]
struct BindingInfo {
    span: Span,
    annotation: BindingMode,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum PatternSource {
    Match,
    Let,
    For,
    FnParam,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum IsRepeatExpr {
    No,
    Yes,
}

struct IsNeverPattern;

/// Describes whether an `AnonConst` is a type level const arg or
/// some other form of anon const (i.e. inline consts or enum discriminants)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum AnonConstKind {
    EnumDiscriminant,
    InlineConst,
    ConstArg(IsRepeatExpr),
}

impl PatternSource {
    fn descr(self) -> &'static str {
        match self {
            PatternSource::Match => "match binding",
            PatternSource::Let => "let binding",
            PatternSource::For => "for binding",
            PatternSource::FnParam => "function parameter",
        }
    }
}

impl IntoDiagArg for PatternSource {
    fn into_diag_arg(self) -> DiagArgValue {
        DiagArgValue::Str(Cow::Borrowed(self.descr()))
    }
}

/// Denotes whether the context for the set of already bound bindings is a `Product`
/// or `Or` context. This is used in e.g., `fresh_binding` and `resolve_pattern_inner`.
/// See those functions for more information.
#[derive(PartialEq)]
enum PatBoundCtx {
    /// A product pattern context, e.g., `Variant(a, b)`.
    Product,
    /// An or-pattern context, e.g., `p_0 | ... | p_n`.
    Or,
}

/// Does this the item (from the item rib scope) allow generic parameters?
#[derive(Copy, Clone, Debug)]
pub(crate) enum HasGenericParams {
    Yes(Span),
    No,
}

/// May this constant have generics?
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConstantHasGenerics {
    Yes,
    No(NoConstantGenericsReason),
}

impl ConstantHasGenerics {
    fn force_yes_if(self, b: bool) -> Self {
        if b { Self::Yes } else { self }
    }
}

/// Reason for why an anon const is not allowed to reference generic parameters
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum NoConstantGenericsReason {
    /// Const arguments are only allowed to use generic parameters when:
    /// - `feature(generic_const_exprs)` is enabled
    /// or
    /// - the const argument is a sole const generic parameter, i.e. `foo::<{ N }>()`
    ///
    /// If neither of the above are true then this is used as the cause.
    NonTrivialConstArg,
    /// Enum discriminants are not allowed to reference generic parameters ever, this
    /// is used when an anon const is in the following position:
    ///
    /// ```rust,compile_fail
    /// enum Foo<const N: isize> {
    ///     Variant = { N }, // this anon const is not allowed to use generics
    /// }
    /// ```
    IsEnumDiscriminant,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConstantItemKind {
    Const,
    Static,
}

impl ConstantItemKind {
    pub(crate) fn as_str(&self) -> &'static str {
        match self {
            Self::Const => "const",
            Self::Static => "static",
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum RecordPartialRes {
    Yes,
    No,
}

/// The rib kind restricts certain accesses,
/// e.g. to a `Res::Local` of an outer item.
#[derive(Copy, Clone, Debug)]
pub(crate) enum RibKind<'ra> {
    /// No restriction needs to be applied.
    Normal,

    /// We passed through an impl or trait and are now in one of its
    /// methods or associated types. Allow references to ty params that impl or trait
    /// binds. Disallow any other upvars (including other ty params that are
    /// upvars).
    AssocItem,

    /// We passed through a function, closure or coroutine signature. Disallow labels.
    FnOrCoroutine,

    /// We passed through an item scope. Disallow upvars.
    Item(HasGenericParams, DefKind),

    /// We're in a constant item. Can't refer to dynamic stuff.
    ///
    /// The item may reference generic parameters in trivial constant expressions.
    /// All other constants aren't allowed to use generic params at all.
    ConstantItem(ConstantHasGenerics, Option<(Ident, ConstantItemKind)>),

    /// We passed through a module.
    Module(Module<'ra>),

    /// We passed through a `macro_rules!` statement
    MacroDefinition(DefId),

    /// All bindings in this rib are generic parameters that can't be used
    /// from the default of a generic parameter because they're not declared
    /// before said generic parameter. Also see the `visit_generics` override.
    ForwardGenericParamBan,

    /// We are inside of the type of a const parameter. Can't refer to any
    /// parameters.
    ConstParamTy,

    /// We are inside a `sym` inline assembly operand. Can only refer to
    /// globals.
    InlineAsmSym,
}

impl RibKind<'_> {
    /// Whether this rib kind contains generic parameters, as opposed to local
    /// variables.
    pub(crate) fn contains_params(&self) -> bool {
        match self {
            RibKind::Normal
            | RibKind::FnOrCoroutine
            | RibKind::ConstantItem(..)
            | RibKind::Module(_)
            | RibKind::MacroDefinition(_)
            | RibKind::ConstParamTy
            | RibKind::InlineAsmSym => false,
            RibKind::AssocItem | RibKind::Item(..) | RibKind::ForwardGenericParamBan => true,
        }
    }

    /// This rib forbids referring to labels defined in upwards ribs.
    fn is_label_barrier(self) -> bool {
        match self {
            RibKind::Normal | RibKind::MacroDefinition(..) => false,

            RibKind::AssocItem
            | RibKind::FnOrCoroutine
            | RibKind::Item(..)
            | RibKind::ConstantItem(..)
            | RibKind::Module(..)
            | RibKind::ForwardGenericParamBan
            | RibKind::ConstParamTy
            | RibKind::InlineAsmSym => true,
        }
    }
}

/// A single local scope.
///
/// A rib represents a scope names can live in. Note that these appear in many places, not just
/// around braces. At any place where the list of accessible names (of the given namespace)
/// changes or a new restrictions on the name accessibility are introduced, a new rib is put onto a
/// stack. This may be, for example, a `let` statement (because it introduces variables), a macro,
/// etc.
///
/// Different [rib kinds](enum@RibKind) are transparent for different names.
///
/// The resolution keeps a separate stack of ribs as it traverses the AST for each namespace. When
/// resolving, the name is looked up from inside out.
#[derive(Debug)]
pub(crate) struct Rib<'ra, R = Res> {
    pub bindings: IdentMap<R>,
    pub kind: RibKind<'ra>,
}

impl<'ra, R> Rib<'ra, R> {
    fn new(kind: RibKind<'ra>) -> Rib<'ra, R> {
        Rib { bindings: Default::default(), kind }
    }
}

#[derive(Clone, Copy, Debug)]
enum LifetimeUseSet {
    One { use_span: Span, use_ctxt: visit::LifetimeCtxt },
    Many,
}

#[derive(Copy, Clone, Debug)]
enum LifetimeRibKind {
    // -- Ribs introducing named lifetimes
    //
    /// This rib declares generic parameters.
    /// Only for this kind the `LifetimeRib::bindings` field can be non-empty.
    Generics { binder: NodeId, span: Span, kind: LifetimeBinderKind },

    // -- Ribs introducing unnamed lifetimes
    //
    /// Create a new anonymous lifetime parameter and reference it.
    ///
    /// If `report_in_path`, report an error when encountering lifetime elision in a path:
    /// ```compile_fail
    /// struct Foo<'a> { x: &'a () }
    /// async fn foo(x: Foo) {}
    /// ```
    ///
    /// Note: the error should not trigger when the elided lifetime is in a pattern or
    /// expression-position path:
    /// ```
    /// struct Foo<'a> { x: &'a () }
    /// async fn foo(Foo { x: _ }: Foo<'_>) {}
    /// ```
    AnonymousCreateParameter { binder: NodeId, report_in_path: bool },

    /// Replace all anonymous lifetimes by provided lifetime.
    Elided(LifetimeRes),

    // -- Barrier ribs that stop lifetime lookup, or continue it but produce an error later.
    //
    /// Give a hard error when either `&` or `'_` is written. Used to
    /// rule out things like `where T: Foo<'_>`. Does not imply an
    /// error on default object bounds (e.g., `Box<dyn Foo>`).
    AnonymousReportError,

    /// Resolves elided lifetimes to `'static` if there are no other lifetimes in scope,
    /// otherwise give a warning that the previous behavior of introducing a new early-bound
    /// lifetime is a bug and will be removed (if `emit_lint` is enabled).
    StaticIfNoLifetimeInScope { lint_id: NodeId, emit_lint: bool },

    /// Signal we cannot find which should be the anonymous lifetime.
    ElisionFailure,

    /// This rib forbids usage of generic parameters inside of const parameter types.
    ///
    /// While this is desirable to support eventually, it is difficult to do and so is
    /// currently forbidden. See rust-lang/project-const-generics#28 for more info.
    ConstParamTy,

    /// Usage of generic parameters is forbidden in various positions for anon consts:
    /// - const arguments when `generic_const_exprs` is not enabled
    /// - enum discriminant values
    ///
    /// This rib emits an error when a lifetime would resolve to a lifetime parameter.
    ConcreteAnonConst(NoConstantGenericsReason),

    /// This rib acts as a barrier to forbid reference to lifetimes of a parent item.
    Item,
}

#[derive(Copy, Clone, Debug)]
enum LifetimeBinderKind {
    BareFnType,
    PolyTrait,
    WhereBound,
    Item,
    ConstItem,
    Function,
    Closure,
    ImplBlock,
}

impl LifetimeBinderKind {
    fn descr(self) -> &'static str {
        use LifetimeBinderKind::*;
        match self {
            BareFnType => "type",
            PolyTrait => "bound",
            WhereBound => "bound",
            Item | ConstItem => "item",
            ImplBlock => "impl block",
            Function => "function",
            Closure => "closure",
        }
    }
}

#[derive(Debug)]
struct LifetimeRib {
    kind: LifetimeRibKind,
    // We need to preserve insertion order for async fns.
    bindings: FxIndexMap<Ident, (NodeId, LifetimeRes)>,
}

impl LifetimeRib {
    fn new(kind: LifetimeRibKind) -> LifetimeRib {
        LifetimeRib { bindings: Default::default(), kind }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum AliasPossibility {
    No,
    Maybe,
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum PathSource<'a> {
    // Type paths `Path`.
    Type,
    // Trait paths in bounds or impls.
    Trait(AliasPossibility),
    // Expression paths `path`, with optional parent context.
    Expr(Option<&'a Expr>),
    // Paths in path patterns `Path`.
    Pat,
    // Paths in struct expressions and patterns `Path { .. }`.
    Struct,
    // Paths in tuple struct patterns `Path(..)`.
    TupleStruct(Span, &'a [Span]),
    // `m::A::B` in `<T as m::A>::B::C`.
    TraitItem(Namespace),
    // Paths in delegation item
    Delegation,
}

impl<'a> PathSource<'a> {
    fn namespace(self) -> Namespace {
        match self {
            PathSource::Type | PathSource::Trait(_) | PathSource::Struct => TypeNS,
            PathSource::Expr(..)
            | PathSource::Pat
            | PathSource::TupleStruct(..)
            | PathSource::Delegation => ValueNS,
            PathSource::TraitItem(ns) => ns,
        }
    }

    fn defer_to_typeck(self) -> bool {
        match self {
            PathSource::Type
            | PathSource::Expr(..)
            | PathSource::Pat
            | PathSource::Struct
            | PathSource::TupleStruct(..) => true,
            PathSource::Trait(_) | PathSource::TraitItem(..) | PathSource::Delegation => false,
        }
    }

    fn descr_expected(self) -> &'static str {
        match &self {
            PathSource::Type => "type",
            PathSource::Trait(_) => "trait",
            PathSource::Pat => "unit struct, unit variant or constant",
            PathSource::Struct => "struct, variant or union type",
            PathSource::TupleStruct(..) => "tuple struct or tuple variant",
            PathSource::TraitItem(ns) => match ns {
                TypeNS => "associated type",
                ValueNS => "method or associated constant",
                MacroNS => bug!("associated macro"),
            },
            PathSource::Expr(parent) => match parent.as_ref().map(|p| &p.kind) {
                // "function" here means "anything callable" rather than `DefKind::Fn`,
                // this is not precise but usually more helpful than just "value".
                Some(ExprKind::Call(call_expr, _)) => match &call_expr.kind {
                    // the case of `::some_crate()`
                    ExprKind::Path(_, path)
                        if let [segment, _] = path.segments.as_slice()
                            && segment.ident.name == kw::PathRoot =>
                    {
                        "external crate"
                    }
                    ExprKind::Path(_, path) => {
                        let mut msg = "function";
                        if let Some(segment) = path.segments.iter().last() {
                            if let Some(c) = segment.ident.to_string().chars().next() {
                                if c.is_uppercase() {
                                    msg = "function, tuple struct or tuple variant";
                                }
                            }
                        }
                        msg
                    }
                    _ => "function",
                },
                _ => "value",
            },
            PathSource::Delegation => "function",
        }
    }

    fn is_call(self) -> bool {
        matches!(self, PathSource::Expr(Some(&Expr { kind: ExprKind::Call(..), .. })))
    }

    pub(crate) fn is_expected(self, res: Res) -> bool {
        match self {
            PathSource::Type => matches!(
                res,
                Res::Def(
                    DefKind::Struct
                        | DefKind::Union
                        | DefKind::Enum
                        | DefKind::Trait
                        | DefKind::TraitAlias
                        | DefKind::TyAlias
                        | DefKind::AssocTy
                        | DefKind::TyParam
                        | DefKind::OpaqueTy
                        | DefKind::ForeignTy,
                    _,
                ) | Res::PrimTy(..)
                    | Res::SelfTyParam { .. }
                    | Res::SelfTyAlias { .. }
            ),
            PathSource::Trait(AliasPossibility::No) => matches!(res, Res::Def(DefKind::Trait, _)),
            PathSource::Trait(AliasPossibility::Maybe) => {
                matches!(res, Res::Def(DefKind::Trait | DefKind::TraitAlias, _))
            }
            PathSource::Expr(..) => matches!(
                res,
                Res::Def(
                    DefKind::Ctor(_, CtorKind::Const | CtorKind::Fn)
                        | DefKind::Const
                        | DefKind::Static { .. }
                        | DefKind::Fn
                        | DefKind::AssocFn
                        | DefKind::AssocConst
                        | DefKind::ConstParam,
                    _,
                ) | Res::Local(..)
                    | Res::SelfCtor(..)
            ),
            PathSource::Pat => {
                res.expected_in_unit_struct_pat()
                    || matches!(res, Res::Def(DefKind::Const | DefKind::AssocConst, _))
            }
            PathSource::TupleStruct(..) => res.expected_in_tuple_struct_pat(),
            PathSource::Struct => matches!(
                res,
                Res::Def(
                    DefKind::Struct
                        | DefKind::Union
                        | DefKind::Variant
                        | DefKind::TyAlias
                        | DefKind::AssocTy,
                    _,
                ) | Res::SelfTyParam { .. }
                    | Res::SelfTyAlias { .. }
            ),
            PathSource::TraitItem(ns) => match res {
                Res::Def(DefKind::AssocConst | DefKind::AssocFn, _) if ns == ValueNS => true,
                Res::Def(DefKind::AssocTy, _) if ns == TypeNS => true,
                _ => false,
            },
            PathSource::Delegation => matches!(res, Res::Def(DefKind::Fn | DefKind::AssocFn, _)),
        }
    }

    fn error_code(self, has_unexpected_resolution: bool) -> ErrCode {
        match (self, has_unexpected_resolution) {
            (PathSource::Trait(_), true) => E0404,
            (PathSource::Trait(_), false) => E0405,
            (PathSource::Type, true) => E0573,
            (PathSource::Type, false) => E0412,
            (PathSource::Struct, true) => E0574,
            (PathSource::Struct, false) => E0422,
            (PathSource::Expr(..), true) | (PathSource::Delegation, true) => E0423,
            (PathSource::Expr(..), false) | (PathSource::Delegation, false) => E0425,
            (PathSource::Pat | PathSource::TupleStruct(..), true) => E0532,
            (PathSource::Pat | PathSource::TupleStruct(..), false) => E0531,
            (PathSource::TraitItem(..), true) => E0575,
            (PathSource::TraitItem(..), false) => E0576,
        }
    }
}

/// At this point for most items we can answer whether that item is exported or not,
/// but some items like impls require type information to determine exported-ness, so we make a
/// conservative estimate for them (e.g. based on nominal visibility).
#[derive(Clone, Copy)]
enum MaybeExported<'a> {
    Ok(NodeId),
    Impl(Option<DefId>),
    ImplItem(Result<DefId, &'a Visibility>),
    NestedUse(&'a Visibility),
}

impl MaybeExported<'_> {
    fn eval(self, r: &Resolver<'_, '_>) -> bool {
        let def_id = match self {
            MaybeExported::Ok(node_id) => Some(r.local_def_id(node_id)),
            MaybeExported::Impl(Some(trait_def_id)) | MaybeExported::ImplItem(Ok(trait_def_id)) => {
                trait_def_id.as_local()
            }
            MaybeExported::Impl(None) => return true,
            MaybeExported::ImplItem(Err(vis)) | MaybeExported::NestedUse(vis) => {
                return vis.kind.is_pub();
            }
        };
        def_id.map_or(true, |def_id| r.effective_visibilities.is_exported(def_id))
    }
}

/// Used for recording UnnecessaryQualification.
#[derive(Debug)]
pub(crate) struct UnnecessaryQualification<'ra> {
    pub binding: LexicalScopeBinding<'ra>,
    pub node_id: NodeId,
    pub path_span: Span,
    pub removal_span: Span,
}

#[derive(Default)]
struct DiagMetadata<'ast> {
    /// The current trait's associated items' ident, used for diagnostic suggestions.
    current_trait_assoc_items: Option<&'ast [P<AssocItem>]>,

    /// The current self type if inside an impl (used for better errors).
    current_self_type: Option<Ty>,

    /// The current self item if inside an ADT (used for better errors).
    current_self_item: Option<NodeId>,

    /// The current trait (used to suggest).
    current_item: Option<&'ast Item>,

    /// When processing generic arguments and encountering an unresolved ident not found,
    /// suggest introducing a type or const param depending on the context.
    currently_processing_generic_args: bool,

    /// The current enclosing (non-closure) function (used for better errors).
    current_function: Option<(FnKind<'ast>, Span)>,

    /// A list of labels as of yet unused. Labels will be removed from this map when
    /// they are used (in a `break` or `continue` statement)
    unused_labels: FxHashMap<NodeId, Span>,

    /// Only used for better errors on `let x = { foo: bar };`.
    /// In the case of a parse error with `let x = { foo: bar, };`, this isn't needed, it's only
    /// needed for cases where this parses as a correct type ascription.
    current_block_could_be_bare_struct_literal: Option<Span>,

    /// Only used for better errors on `let <pat>: <expr, not type>;`.
    current_let_binding: Option<(Span, Option<Span>, Option<Span>)>,

    current_pat: Option<&'ast Pat>,

    /// Used to detect possible `if let` written without `let` and to provide structured suggestion.
    in_if_condition: Option<&'ast Expr>,

    /// Used to detect possible new binding written without `let` and to provide structured suggestion.
    in_assignment: Option<&'ast Expr>,
    is_assign_rhs: bool,

    /// If we are setting an associated type in trait impl, is it a non-GAT type?
    in_non_gat_assoc_type: Option<bool>,

    /// Used to detect possible `.` -> `..` typo when calling methods.
    in_range: Option<(&'ast Expr, &'ast Expr)>,

    /// If we are currently in a trait object definition. Used to point at the bounds when
    /// encountering a struct or enum.
    current_trait_object: Option<&'ast [ast::GenericBound]>,

    /// Given `where <T as Bar>::Baz: String`, suggest `where T: Bar<Baz = String>`.
    current_where_predicate: Option<&'ast WherePredicate>,

    current_type_path: Option<&'ast Ty>,

    /// The current impl items (used to suggest).
    current_impl_items: Option<&'ast [P<AssocItem>]>,

    /// When processing impl trait
    currently_processing_impl_trait: Option<(TraitRef, Ty)>,

    /// Accumulate the errors due to missed lifetime elision,
    /// and report them all at once for each function.
    current_elision_failures: Vec<MissingLifetime>,
}

/// Walks the whole crate in DFS order, visiting each item, counting the declared number of
/// lifetime generic parameters and function parameters.
struct ItemInfoCollector<'a, 'ra, 'tcx> {
    r: &'a mut Resolver<'ra, 'tcx>,
}

impl ItemInfoCollector<'_, '_, '_> {
    fn collect_fn_info(&mut self, sig: &FnSig, id: NodeId) {
        let sig = DelegationFnSig {
            header: sig.header,
            param_count: sig.decl.inputs.len(),
            has_self: sig.decl.has_self(),
            c_variadic: sig.decl.c_variadic(),
        };
        self.r.delegation_fn_sigs.insert(self.r.local_def_id(id), sig);
    }
}

impl<'ast> Visitor<'ast> for ItemInfoCollector<'_, '_, '_> {
    fn visit_item(&mut self, item: &'ast Item) {
        match &item.kind {
            ItemKind::TyAlias(box TyAlias { ref generics, .. })
            | ItemKind::Const(box ConstItem { ref generics, .. })
            | ItemKind::Fn(box Fn { ref generics, .. })
            | ItemKind::Enum(_, ref generics)
            | ItemKind::Struct(_, ref generics)
            | ItemKind::Union(_, ref generics)
            | ItemKind::Impl(box Impl { ref generics, .. })
            | ItemKind::Trait(box Trait { ref generics, .. })
            | ItemKind::TraitAlias(ref generics, _) => {
                if let ItemKind::Fn(box Fn { ref sig, .. }) = &item.kind {
                    self.collect_fn_info(sig, item.id);
                }

                let def_id = self.r.local_def_id(item.id);
                let count = generics
                    .params
                    .iter()
                    .filter(|param| matches!(param.kind, ast::GenericParamKind::Lifetime { .. }))
                    .count();
                self.r.item_generics_num_lifetimes.insert(def_id, count);
            }

            ItemKind::Mod(..)
            | ItemKind::ForeignMod(..)
            | ItemKind::Static(..)
            | ItemKind::Use(..)
            | ItemKind::ExternCrate(..)
            | ItemKind::MacroDef(..)
            | ItemKind::GlobalAsm(..)
            | ItemKind::MacCall(..)
            | ItemKind::DelegationMac(..) => {}
            ItemKind::Delegation(..) => {
                // Delegated functions have lifetimes, their count is not necessarily zero.
                // But skipping the delegation items here doesn't mean that the count will be considered zero,
                // it means there will be a panic when retrieving the count,
                // but for delegation items we are never actually retrieving that count in practice.
            }
        }
        visit::walk_item(self, item)
    }

    fn visit_assoc_item(&mut self, item: &'ast AssocItem, ctxt: AssocCtxt) {
        if let AssocItemKind::Fn(box Fn { ref sig, .. }) = &item.kind {
            self.collect_fn_info(sig, item.id);
        }
        visit::walk_assoc_item(self, item, ctxt);
    }
}

impl<'ra, 'tcx> Resolver<'ra, 'tcx> {
    pub(crate) fn late_resolve_crate(&mut self, krate: &Crate) {
        visit::walk_crate(&mut ItemInfoCollector { r: self }, krate);
        let mut late_resolution_visitor = LateResolutionVisitor::new(self);
        late_resolution_visitor.resolve_doc_links(&krate.attrs, MaybeExported::Ok(CRATE_NODE_ID));
        visit::walk_crate(&mut late_resolution_visitor, krate);
        for (id, span) in late_resolution_visitor.diag_metadata.unused_labels.iter() {
            self.lint_buffer.buffer_lint(
                lint::builtin::UNUSED_LABELS,
                *id,
                *span,
                BuiltinLintDiag::UnusedLabel,
            );
        }
    }
}

/// Check if definition matches a path
fn def_id_matches_path(tcx: TyCtxt<'_>, mut def_id: DefId, expected_path: &[&str]) -> bool {
    let mut path = expected_path.iter().rev();
    while let (Some(parent), Some(next_step)) = (tcx.opt_parent(def_id), path.next()) {
        if !tcx.opt_item_name(def_id).map_or(false, |n| n.as_str() == *next_step) {
            return false;
        }
        def_id = parent;
    }
    true
}
