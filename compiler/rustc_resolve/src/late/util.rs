#![allow(unused_imports, unreachable_pub)]

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

use super::*;
use crate::{
    errors, path_names_to_string, rustdoc, BindingError, BindingKey, Finalize, LexicalScopeBinding,
    Module, ModuleOrUniformRoot, NameBinding, ParentScope, PathResult, ResolutionError, Resolver,
    Segment, TyCtxt, UseError, Used,
};

impl<'a, 'ast, 'ra: 'ast, 'tcx> LateResolutionVisitor<'a, 'ast, 'ra, 'tcx> {
    // AST resolution
    //
    // We maintain a list of value ribs and type ribs.
    //
    // Simultaneously, we keep track of the current position in the module
    // graph in the `parent_scope.module` pointer. When we go to resolve a name in
    // the value or type namespaces, we first look through all the ribs and
    // then query the module graph. When we resolve a name in the module
    // namespace, we can skip all the ribs (since nested modules are not
    // allowed within blocks in Rust) and jump straight to the current module
    // graph node.
    //
    // Named implementations are handled separately. When we find a method
    // call, we consult the module node to find all of the implementations in
    // scope. This information is lazily cached in the module node. We then
    // generate a fake "implementation scope" containing all the
    // implementations thus found, for compatibility with old resolve pass.

    /// Do some `work` within a new innermost rib of the given `kind` in the given namespace (`ns`).
    pub fn with_rib<T>(
        &mut self,
        ns: Namespace,
        kind: RibKind<'ra>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.ribs[ns].push(Rib::new(kind));
        let ret = work(self);
        self.ribs[ns].pop();
        ret
    }

    pub fn with_scope<T>(&mut self, id: NodeId, f: impl FnOnce(&mut Self) -> T) -> T {
        if let Some(module) = self.r.get_module(self.r.local_def_id(id).to_def_id()) {
            // Move down in the graph.
            let orig_module = replace(&mut self.parent_scope.module, module);
            self.with_rib(ValueNS, RibKind::Module(module), |this| {
                this.with_rib(TypeNS, RibKind::Module(module), |this| {
                    let ret = f(this);
                    this.parent_scope.module = orig_module;
                    ret
                })
            })
        } else {
            f(self)
        }
    }

    pub fn with_label_rib(&mut self, kind: RibKind<'ra>, f: impl FnOnce(&mut Self)) {
        self.label_ribs.push(Rib::new(kind));
        f(self);
        self.label_ribs.pop();
    }

    pub fn with_static_rib(&mut self, def_kind: DefKind, f: impl FnOnce(&mut Self)) {
        let kind = RibKind::Item(HasGenericParams::No, def_kind);
        self.with_rib(ValueNS, kind, |this| this.with_rib(TypeNS, kind, f))
    }

    #[instrument(level = "debug", skip(self, work))]
    pub fn with_lifetime_rib<T>(
        &mut self,
        kind: LifetimeRibKind,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.lifetime_ribs.push(LifetimeRib::new(kind));
        let outer_elision_candidates = self.lifetime_elision_candidates.take();
        let ret = work(self);
        self.lifetime_elision_candidates = outer_elision_candidates;
        self.lifetime_ribs.pop();
        ret
    }

    // HACK(min_const_generics, generic_const_exprs): We
    // want to keep allowing `[0; std::mem::size_of::<*mut T>()]`
    // with a future compat lint for now. We do this by adding an
    // additional special case for repeat expressions.
    //
    // Note that we intentionally still forbid `[0; N + 1]` during
    // name resolution so that we don't extend the future
    // compat lint to new cases.
    #[instrument(level = "debug", skip(self, f))]
    pub fn with_constant_rib(
        &mut self,
        is_repeat: IsRepeatExpr,
        may_use_generics: ConstantHasGenerics,
        item: Option<(Ident, ConstantItemKind)>,
        f: impl FnOnce(&mut Self),
    ) {
        let f = |this: &mut Self| {
            this.with_rib(ValueNS, RibKind::ConstantItem(may_use_generics, item), |this| {
                this.with_rib(
                    TypeNS,
                    RibKind::ConstantItem(
                        may_use_generics.force_yes_if(is_repeat == IsRepeatExpr::Yes),
                        item,
                    ),
                    |this| {
                        this.with_label_rib(RibKind::ConstantItem(may_use_generics, item), f);
                    },
                )
            })
        };

        if let ConstantHasGenerics::No(cause) = may_use_generics {
            self.with_lifetime_rib(LifetimeRibKind::ConcreteAnonConst(cause), f)
        } else {
            f(self)
        }
    }

    pub fn with_current_self_type<T>(
        &mut self,
        self_type: &Ty,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        // Handle nested impls (inside fn bodies)
        let previous_value =
            replace(&mut self.diag_metadata.current_self_type, Some(self_type.clone()));
        let result = f(self);
        self.diag_metadata.current_self_type = previous_value;
        result
    }

    pub fn with_current_self_item<T>(
        &mut self,
        self_item: &Item,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous_value = replace(&mut self.diag_metadata.current_self_item, Some(self_item.id));
        let result = f(self);
        self.diag_metadata.current_self_item = previous_value;
        result
    }

    /// This is called to resolve a trait reference from an `impl` (i.e., `impl Trait for Foo`).
    pub fn with_optional_trait_ref<T>(
        &mut self,
        opt_trait_ref: Option<&TraitRef>,
        self_type: &'ast Ty,
        f: impl FnOnce(&mut Self, Option<DefId>) -> T,
    ) -> T {
        let mut new_val = None;
        let mut new_id = None;
        if let Some(trait_ref) = opt_trait_ref {
            let path: Vec<_> = Segment::from_path(&trait_ref.path);
            self.diag_metadata.currently_processing_impl_trait =
                Some((trait_ref.clone(), self_type.clone()));
            let res = self.smart_resolve_path_fragment(
                &None,
                &path,
                PathSource::Trait(AliasPossibility::No),
                Finalize::new(trait_ref.ref_id, trait_ref.path.span),
                RecordPartialRes::Yes,
            );
            self.diag_metadata.currently_processing_impl_trait = None;
            if let Some(def_id) = res.expect_full_res().opt_def_id() {
                new_id = Some(def_id);
                new_val = Some((self.r.expect_module(def_id), trait_ref.clone()));
            }
        }
        let original_trait_ref = replace(&mut self.current_trait_ref, new_val);
        let result = f(self, new_id);
        self.current_trait_ref = original_trait_ref;
        result
    }

    pub fn with_self_rib_ns(&mut self, ns: Namespace, self_res: Res, f: impl FnOnce(&mut Self)) {
        let mut self_type_rib = Rib::new(RibKind::Normal);

        // Plain insert (no renaming, since types are not currently hygienic)
        self_type_rib.bindings.insert(Ident::with_dummy_span(kw::SelfUpper), self_res);
        self.ribs[ns].push(self_type_rib);
        f(self);
        self.ribs[ns].pop();
    }

    pub fn with_self_rib(&mut self, self_res: Res, f: impl FnOnce(&mut Self)) {
        self.with_self_rib_ns(TypeNS, self_res, f)
    }

    pub(super) fn with_resolved_label(
        &mut self,
        label: Option<Label>,
        id: NodeId,
        f: impl FnOnce(&mut Self),
    ) {
        if let Some(label) = label {
            if label.ident.as_str().as_bytes()[1] != b'_' {
                self.diag_metadata.unused_labels.insert(id, label.ident.span);
            }

            if let Ok((_, orig_span)) = self.resolve_label(label.ident) {
                diagnostics::signal_label_shadowing(self.r.tcx.sess, orig_span, label.ident)
            }

            self.with_label_rib(RibKind::Normal, |this| {
                let ident = label.ident.normalize_to_macro_rules();
                this.label_ribs.last_mut().unwrap().bindings.insert(ident, id);
                f(this);
            });
        } else {
            f(self);
        }
    }

    pub(super) fn with_generic_param_rib<'c, F>(
        &'c mut self,
        params: &'c [GenericParam],
        kind: RibKind<'ra>,
        lifetime_kind: LifetimeRibKind,
        f: F,
    ) where
        F: FnOnce(&mut Self),
    {
        debug!("with_generic_param_rib");
        let LifetimeRibKind::Generics { binder, span: generics_span, kind: generics_kind, .. } =
            lifetime_kind
        else {
            panic!()
        };

        let mut function_type_rib = Rib::new(kind);
        let mut function_value_rib = Rib::new(kind);
        let mut function_lifetime_rib = LifetimeRib::new(lifetime_kind);

        // Only check for shadowed bindings if we're declaring new params.
        if !params.is_empty() {
            let mut seen_bindings = FxHashMap::default();
            // Store all seen lifetimes names from outer scopes.
            let mut seen_lifetimes = FxHashSet::default();

            // We also can't shadow bindings from associated parent items.
            for ns in [ValueNS, TypeNS] {
                for parent_rib in self.ribs[ns].iter().rev() {
                    // Break at mod level, to account for nested items which are
                    // allowed to shadow generic param names.
                    if matches!(parent_rib.kind, RibKind::Module(..)) {
                        break;
                    }

                    seen_bindings
                        .extend(parent_rib.bindings.keys().map(|ident| (*ident, ident.span)));
                }
            }

            // Forbid shadowing lifetime bindings
            for rib in self.lifetime_ribs.iter().rev() {
                seen_lifetimes.extend(rib.bindings.iter().map(|(ident, _)| *ident));
                if let LifetimeRibKind::Item = rib.kind {
                    break;
                }
            }

            for param in params {
                let ident = param.ident.normalize_to_macros_2_0();
                debug!("with_generic_param_rib: {}", param.id);

                if let GenericParamKind::Lifetime = param.kind
                    && let Some(&original) = seen_lifetimes.get(&ident)
                {
                    diagnostics::signal_lifetime_shadowing(self.r.tcx.sess, original, param.ident);
                    // Record lifetime res, so lowering knows there is something fishy.
                    self.record_lifetime_param(param.id, LifetimeRes::Error);
                    continue;
                }

                match seen_bindings.entry(ident) {
                    Entry::Occupied(entry) => {
                        let span = *entry.get();
                        let err = ResolutionError::NameAlreadyUsedInParameterList(ident.name, span);
                        self.report_error(param.ident.span, err);
                        let rib = match param.kind {
                            GenericParamKind::Lifetime => {
                                // Record lifetime res, so lowering knows there is something fishy.
                                self.record_lifetime_param(param.id, LifetimeRes::Error);
                                continue;
                            }
                            GenericParamKind::Type { .. } => &mut function_type_rib,
                            GenericParamKind::Const { .. } => &mut function_value_rib,
                        };

                        // Taint the resolution in case of errors to prevent follow up errors in typeck
                        self.r.record_partial_res(param.id, PartialRes::new(Res::Err));
                        rib.bindings.insert(ident, Res::Err);
                        continue;
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(param.ident.span);
                    }
                }

                if param.ident.name == kw::UnderscoreLifetime {
                    self.r
                        .dcx()
                        .emit_err(errors::UnderscoreLifetimeIsReserved { span: param.ident.span });
                    // Record lifetime res, so lowering knows there is something fishy.
                    self.record_lifetime_param(param.id, LifetimeRes::Error);
                    continue;
                }

                if param.ident.name == kw::StaticLifetime {
                    self.r.dcx().emit_err(errors::StaticLifetimeIsReserved {
                        span: param.ident.span,
                        lifetime: param.ident,
                    });
                    // Record lifetime res, so lowering knows there is something fishy.
                    self.record_lifetime_param(param.id, LifetimeRes::Error);
                    continue;
                }

                let def_id = self.r.local_def_id(param.id);

                // Plain insert (no renaming).
                let (rib, def_kind) = match param.kind {
                    GenericParamKind::Type { .. } => (&mut function_type_rib, DefKind::TyParam),
                    GenericParamKind::Const { .. } => {
                        (&mut function_value_rib, DefKind::ConstParam)
                    }
                    GenericParamKind::Lifetime => {
                        let res = LifetimeRes::Param { param: def_id, binder };
                        self.record_lifetime_param(param.id, res);
                        function_lifetime_rib.bindings.insert(ident, (param.id, res));
                        continue;
                    }
                };

                let res = match kind {
                    RibKind::Item(..) | RibKind::AssocItem => {
                        Res::Def(def_kind, def_id.to_def_id())
                    }
                    RibKind::Normal => {
                        // FIXME(non_lifetime_binders): Stop special-casing
                        // const params to error out here.
                        if self.r.tcx.features().non_lifetime_binders
                            && matches!(param.kind, GenericParamKind::Type { .. })
                        {
                            Res::Def(def_kind, def_id.to_def_id())
                        } else {
                            Res::Err
                        }
                    }
                    _ => span_bug!(param.ident.span, "Unexpected rib kind {:?}", kind),
                };
                self.r.record_partial_res(param.id, PartialRes::new(res));
                rib.bindings.insert(ident, res);
            }
        }

        self.lifetime_ribs.push(function_lifetime_rib);
        self.ribs[ValueNS].push(function_value_rib);
        self.ribs[TypeNS].push(function_type_rib);

        f(self);

        self.ribs[TypeNS].pop();
        self.ribs[ValueNS].pop();
        let function_lifetime_rib = self.lifetime_ribs.pop().unwrap();

        // Do not account for the parameters we just bound for function lifetime elision.
        if let Some(ref mut candidates) = self.lifetime_elision_candidates {
            for (_, res) in function_lifetime_rib.bindings.values() {
                candidates.retain(|(r, _)| r != res);
            }
        }

        if let LifetimeBinderKind::BareFnType
        | LifetimeBinderKind::WhereBound
        | LifetimeBinderKind::Function
        | LifetimeBinderKind::ImplBlock = generics_kind
        {
            self.maybe_report_lifetime_uses(generics_span, params)
        }
    }

    /// Build a map from pattern identifiers to binding-info's, and check the bindings are
    /// consistent when encountering or-patterns and never patterns.
    /// This is done hygienically: this could arise for a macro that expands into an or-pattern
    /// where one 'x' was from the user and one 'x' came from the macro.
    ///
    /// A never pattern by definition indicates an unreachable case. For example, matching on
    /// `Result<T, &!>` could look like:
    /// ```rust
    /// # #![feature(never_type)]
    /// # #![feature(never_patterns)]
    /// # fn bar(_x: u32) {}
    /// let foo: Result<u32, &!> = Ok(0);
    /// match foo {
    ///     Ok(x) => bar(x),
    ///     Err(&!),
    /// }
    /// ```
    /// This extends to product types: `(x, !)` is likewise unreachable. So it doesn't make sense to
    /// have a binding here, and we tell the user to use `_` instead.
    pub(super) fn compute_and_check_binding_map(
        &mut self,
        pat: &Pat,
    ) -> Result<FxIndexMap<Ident, BindingInfo>, IsNeverPattern> {
        let mut binding_map = FxIndexMap::default();
        let mut is_never_pat = false;

        pat.walk(&mut |pat| {
            match pat.kind {
                PatKind::Ident(annotation, ident, ref sub_pat)
                    if sub_pat.is_some() || self.is_base_res_local(pat.id) =>
                {
                    binding_map.insert(ident, BindingInfo { span: ident.span, annotation });
                }
                PatKind::Or(ref ps) => {
                    // Check the consistency of this or-pattern and
                    // then add all bindings to the larger map.
                    match self.compute_and_check_or_pat_binding_map(ps) {
                        Ok(bm) => binding_map.extend(bm),
                        Err(IsNeverPattern) => is_never_pat = true,
                    }
                    return false;
                }
                PatKind::Never => is_never_pat = true,
                _ => {}
            }

            true
        });

        if is_never_pat {
            for (_, binding) in binding_map {
                self.report_error(binding.span, ResolutionError::BindingInNeverPattern);
            }
            Err(IsNeverPattern)
        } else {
            Ok(binding_map)
        }
    }

    pub(super) fn is_base_res_local(&self, nid: NodeId) -> bool {
        matches!(
            self.r.partial_res_map.get(&nid).map(|res| res.expect_full_res()),
            Some(Res::Local(..))
        )
    }

    /// Compute the binding map for an or-pattern. Checks that all of the arms in the or-pattern
    /// have exactly the same set of bindings, with the same binding modes for each.
    /// Returns the computed binding map and a boolean indicating whether the pattern is a never
    /// pattern.
    ///
    /// A never pattern by definition indicates an unreachable case. For example, destructuring a
    /// `Result<T, &!>` could look like:
    /// ```rust
    /// # #![feature(never_type)]
    /// # #![feature(never_patterns)]
    /// # fn foo() -> Result<bool, &'static !> { Ok(true) }
    /// let (Ok(x) | Err(&!)) = foo();
    /// # let _ = x;
    /// ```
    /// Because the `Err(&!)` branch is never reached, it does not need to have the same bindings as
    /// the other branches of the or-pattern. So we must ignore never pattern when checking the
    /// bindings of an or-pattern.
    /// Moreover, if all the subpatterns are never patterns (e.g. `Ok(!) | Err(!)`), then the
    /// pattern as a whole counts as a never pattern (since it's definitionallly unreachable).
    pub(super) fn compute_and_check_or_pat_binding_map(
        &mut self,
        pats: &[P<Pat>],
    ) -> Result<FxIndexMap<Ident, BindingInfo>, IsNeverPattern> {
        let mut missing_vars = FxIndexMap::default();
        let mut inconsistent_vars = FxIndexMap::default();

        // 1) Compute the binding maps of all arms; we must ignore never patterns here.
        let not_never_pats = pats
            .iter()
            .filter_map(|pat| {
                let binding_map = self.compute_and_check_binding_map(pat).ok()?;
                Some((binding_map, pat))
            })
            .collect::<Vec<_>>();

        // 2) Record any missing bindings or binding mode inconsistencies.
        for (map_outer, pat_outer) in not_never_pats.iter() {
            // Check against all arms except for the same pattern which is always self-consistent.
            let inners = not_never_pats
                .iter()
                .filter(|(_, pat)| pat.id != pat_outer.id)
                .flat_map(|(map, _)| map);

            for (key, binding_inner) in inners {
                let name = key.name;
                match map_outer.get(key) {
                    None => {
                        // The inner binding is missing in the outer.
                        let binding_error =
                            missing_vars.entry(name).or_insert_with(|| BindingError {
                                name,
                                origin: BTreeSet::new(),
                                target: BTreeSet::new(),
                                could_be_path: name.as_str().starts_with(char::is_uppercase),
                            });
                        binding_error.origin.insert(binding_inner.span);
                        binding_error.target.insert(pat_outer.span);
                    }
                    Some(binding_outer) => {
                        if binding_outer.annotation != binding_inner.annotation {
                            // The binding modes in the outer and inner bindings differ.
                            inconsistent_vars
                                .entry(name)
                                .or_insert((binding_inner.span, binding_outer.span));
                        }
                    }
                }
            }
        }

        // 3) Report all missing variables we found.
        for (name, mut v) in missing_vars {
            if inconsistent_vars.contains_key(&name) {
                v.could_be_path = false;
            }
            self.report_error(
                *v.origin.iter().next().unwrap(),
                ResolutionError::VariableNotBoundInPattern(v, self.parent_scope),
            );
        }

        // 4) Report all inconsistencies in binding modes we found.
        for (name, v) in inconsistent_vars {
            self.report_error(v.0, ResolutionError::VariableBoundWithDifferentMode(name, v.1));
        }

        // 5) Bubble up the final binding map.
        if not_never_pats.is_empty() {
            // All the patterns are never patterns, so the whole or-pattern is one too.
            Err(IsNeverPattern)
        } else {
            let mut binding_map = FxIndexMap::default();
            for (bm, _) in not_never_pats {
                binding_map.extend(bm);
            }
            Ok(binding_map)
        }
    }

    /// Check the consistency of bindings wrt or-patterns and never patterns.
    pub(super) fn check_consistent_bindings(&mut self, pat: &'ast Pat) {
        let mut is_or_or_never = false;
        pat.walk(&mut |pat| match pat.kind {
            PatKind::Or(..) | PatKind::Never => {
                is_or_or_never = true;
                false
            }
            _ => true,
        });
        if is_or_or_never {
            let _ = self.compute_and_check_binding_map(pat);
        }
    }

    /// List all the lifetimes that appear in the provided type.
    pub fn find_lifetime_for_self(&self, ty: &'ast Ty) -> Set1<LifetimeRes> {
        /// Visits a type to find all the &references, and determines the
        /// set of lifetimes for all of those references where the referent
        /// contains Self.
        struct FindReferenceVisitor<'a, 'ra, 'tcx> {
            r: &'a Resolver<'ra, 'tcx>,
            impl_self: Option<Res>,
            lifetime: Set1<LifetimeRes>,
        }

        impl<'ra> Visitor<'ra> for FindReferenceVisitor<'_, '_, '_> {
            fn visit_ty(&mut self, ty: &'ra Ty) {
                trace!("FindReferenceVisitor considering ty={:?}", ty);
                if let TyKind::Ref(lt, _) = ty.kind {
                    // See if anything inside the &thing contains Self
                    let mut visitor =
                        SelfVisitor { r: self.r, impl_self: self.impl_self, self_found: false };
                    visitor.visit_ty(ty);
                    trace!("FindReferenceVisitor: SelfVisitor self_found={:?}", visitor.self_found);
                    if visitor.self_found {
                        let lt_id = if let Some(lt) = lt {
                            lt.id
                        } else {
                            let res = self.r.lifetimes_res_map[&ty.id];
                            let LifetimeRes::ElidedAnchor { start, .. } = res else { bug!() };
                            start
                        };
                        let lt_res = self.r.lifetimes_res_map[&lt_id];
                        trace!("FindReferenceVisitor inserting res={:?}", lt_res);
                        self.lifetime.insert(lt_res);
                    }
                }
                visit::walk_ty(self, ty)
            }

            // A type may have an expression as a const generic argument.
            // We do not want to recurse into those.
            fn visit_expr(&mut self, _: &'ra Expr) {}
        }

        /// Visitor which checks the referent of a &Thing to see if the
        /// Thing contains Self
        struct SelfVisitor<'a, 'ra, 'tcx> {
            r: &'a Resolver<'ra, 'tcx>,
            impl_self: Option<Res>,
            self_found: bool,
        }

        impl SelfVisitor<'_, '_, '_> {
            // Look for `self: &'a Self` - also desugared from `&'a self`
            fn is_self_ty(&self, ty: &Ty) -> bool {
                match ty.kind {
                    TyKind::ImplicitSelf => true,
                    TyKind::Path(None, _) => {
                        let path_res = self.r.partial_res_map[&ty.id].full_res();
                        if let Some(Res::SelfTyParam { .. } | Res::SelfTyAlias { .. }) = path_res {
                            return true;
                        }
                        self.impl_self.is_some() && path_res == self.impl_self
                    }
                    _ => false,
                }
            }
        }

        impl<'ra> Visitor<'ra> for SelfVisitor<'_, '_, '_> {
            fn visit_ty(&mut self, ty: &'ra Ty) {
                trace!("SelfVisitor considering ty={:?}", ty);
                if self.is_self_ty(ty) {
                    trace!("SelfVisitor found Self");
                    self.self_found = true;
                }
                visit::walk_ty(self, ty)
            }

            // A type may have an expression as a const generic argument.
            // We do not want to recurse into those.
            fn visit_expr(&mut self, _: &'ra Expr) {}
        }

        let impl_self = self
            .diag_metadata
            .current_self_type
            .as_ref()
            .and_then(|ty| {
                if let TyKind::Path(None, _) = ty.kind {
                    self.r.partial_res_map.get(&ty.id)
                } else {
                    None
                }
            })
            .and_then(|res| res.full_res())
            .filter(|res| {
                // Permit the types that unambiguously always
                // result in the same type constructor being used
                // (it can't differ between `Self` and `self`).
                matches!(
                    res,
                    Res::Def(DefKind::Struct | DefKind::Union | DefKind::Enum, _,) | Res::PrimTy(_)
                )
            });
        let mut visitor = FindReferenceVisitor { r: self.r, impl_self, lifetime: Set1::Empty };
        visitor.visit_ty(ty);
        trace!("FindReferenceVisitor found={:?}", visitor.lifetime);
        visitor.lifetime
    }

    /// Determine whether or not a label from the `rib_index`th label rib is reachable.
    pub fn is_label_valid_from_rib(&self, rib_index: usize) -> bool {
        let ribs = &self.label_ribs[rib_index + 1..];

        for rib in ribs {
            if rib.kind.is_label_barrier() {
                return false;
            }
        }

        true
    }
}
