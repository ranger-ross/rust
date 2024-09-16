#![allow(unused_imports)]

// ignore-tidy-filelength

use core::ops::ControlFlow;
use std::borrow::Cow;

use hir::Expr;
use rustc_ast::ast::Mutability;
use rustc_attr::parse_confusables;
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_data_structures::sorted_map::SortedMap;
use rustc_data_structures::unord::UnordSet;
use rustc_errors::codes::*;
use rustc_errors::{pluralize, struct_span_code_err, Applicability, Diag, MultiSpan, StashKey};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::lang_items::LangItem;
use rustc_hir::{self as hir, ExprKind, HirId, Node, PathSegment, QPath};
use rustc_infer::infer::{self, RegionVariableOrigin};
use rustc_middle::bug;
use rustc_middle::ty::fast_reject::{simplify_type, DeepRejectCtxt, TreatParams};
use rustc_middle::ty::print::{
    with_crate_prefix, with_forced_trimmed_paths, PrintTraitRefExt as _,
};
use rustc_middle::ty::{self, GenericArgKind, IsSuggestable, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefIdSet;
use rustc_span::symbol::{kw, sym, Ident};
use rustc_span::{
    edit_distance, ErrorGuaranteed, ExpnKind, FileName, MacroKind, Span, Symbol, DUMMY_SP,
};
use rustc_trait_selection::error_reporting::traits::on_unimplemented::OnUnimplementedNote;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
use rustc_trait_selection::traits::{
    supertraits, FulfillmentError, Obligation, ObligationCause, ObligationCauseCode,
};
use tracing::{debug, info};

use crate::errors::{self, CandidateTraitNote, NoAssociatedItem};
use crate::method::probe::{AutorefOrPtrAdjustment, IsSuggestion, Mode, ProbeScope};
use crate::method::suggest::traits::all_traits;
use crate::method::suggest::SelfSource;
use crate::method::{CandidateSource, MethodError, NoMatchData};
use crate::{Expectation, FnCtxt};

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    pub(super) fn is_fn_ty(&self, ty: Ty<'tcx>, span: Span) -> bool {
        let tcx = self.tcx;
        match ty.kind() {
            // Not all of these (e.g., unsafe fns) implement `FnOnce`,
            // so we look for these beforehand.
            // FIXME(async_closures): These don't impl `FnOnce` by default.
            ty::Closure(..) | ty::FnDef(..) | ty::FnPtr(..) => true,
            // If it's not a simple function, look for things which implement `FnOnce`.
            _ => {
                let Some(fn_once) = tcx.lang_items().fn_once_trait() else {
                    return false;
                };

                // This conditional prevents us from asking to call errors and unresolved types.
                // It might seem that we can use `predicate_must_hold_modulo_regions`,
                // but since a Dummy binder is used to fill in the FnOnce trait's arguments,
                // type resolution always gives a "maybe" here.
                if self.autoderef(span, ty).any(|(ty, _)| {
                    info!("check deref {:?} error", ty);
                    matches!(ty.kind(), ty::Error(_) | ty::Infer(_))
                }) {
                    return false;
                }

                self.autoderef(span, ty).any(|(ty, _)| {
                    info!("check deref {:?} impl FnOnce", ty);
                    self.probe(|_| {
                        let trait_ref =
                            ty::TraitRef::new(tcx, fn_once, [ty, self.next_ty_var(span)]);
                        let poly_trait_ref = ty::Binder::dummy(trait_ref);
                        let obligation = Obligation::misc(
                            tcx,
                            span,
                            self.body_id,
                            self.param_env,
                            poly_trait_ref,
                        );
                        self.predicate_may_hold(&obligation)
                    })
                })
            }
        }
    }

    pub(super) fn is_slice_ty(&self, ty: Ty<'tcx>, span: Span) -> bool {
        self.autoderef(span, ty).any(|(ty, _)| matches!(ty.kind(), ty::Slice(..) | ty::Array(..)))
    }

    pub(super) fn impl_into_iterator_should_be_iterator(
        &self,
        ty: Ty<'tcx>,
        span: Span,
        unsatisfied_predicates: &Vec<(
            ty::Predicate<'_>,
            Option<ty::Predicate<'_>>,
            Option<ObligationCause<'_>>,
        )>,
    ) -> bool {
        fn predicate_bounds_generic_param<'tcx>(
            predicate: ty::Predicate<'_>,
            generics: &'tcx ty::Generics,
            generic_param: &ty::GenericParamDef,
            tcx: TyCtxt<'tcx>,
        ) -> bool {
            if let ty::PredicateKind::Clause(ty::ClauseKind::Trait(trait_pred)) =
                predicate.kind().as_ref().skip_binder()
            {
                let ty::TraitPredicate { trait_ref: ty::TraitRef { args, .. }, .. } = trait_pred;
                if args.is_empty() {
                    return false;
                }
                let Some(arg_ty) = args[0].as_type() else {
                    return false;
                };
                let ty::Param(param) = *arg_ty.kind() else {
                    return false;
                };
                // Is `generic_param` the same as the arg for this trait predicate?
                generic_param.index == generics.type_param(param, tcx).index
            } else {
                false
            }
        }

        pub(super) fn is_iterator_predicate(predicate: ty::Predicate<'_>, tcx: TyCtxt<'_>) -> bool {
            if let ty::PredicateKind::Clause(ty::ClauseKind::Trait(trait_pred)) =
                predicate.kind().as_ref().skip_binder()
            {
                tcx.is_diagnostic_item(sym::Iterator, trait_pred.trait_ref.def_id)
            } else {
                false
            }
        }

        // Does the `ty` implement `IntoIterator`?
        let Some(into_iterator_trait) = self.tcx.get_diagnostic_item(sym::IntoIterator) else {
            return false;
        };
        let trait_ref = ty::TraitRef::new(self.tcx, into_iterator_trait, [ty]);
        let cause = ObligationCause::new(span, self.body_id, ObligationCauseCode::Misc);
        let obligation = Obligation::new(self.tcx, cause, self.param_env, trait_ref);
        if !self.predicate_must_hold_modulo_regions(&obligation) {
            return false;
        }

        match *ty.peel_refs().kind() {
            ty::Param(param) => {
                let generics = self.tcx.generics_of(self.body_id);
                let generic_param = generics.type_param(param, self.tcx);
                for unsatisfied in unsatisfied_predicates.iter() {
                    // The parameter implements `IntoIterator`
                    // but it has called a method that requires it to implement `Iterator`
                    if predicate_bounds_generic_param(
                        unsatisfied.0,
                        generics,
                        generic_param,
                        self.tcx,
                    ) && is_iterator_predicate(unsatisfied.0, self.tcx)
                    {
                        return true;
                    }
                }
            }
            ty::Slice(..) | ty::Adt(..) | ty::Alias(ty::Opaque, _) => {
                for unsatisfied in unsatisfied_predicates.iter() {
                    if is_iterator_predicate(unsatisfied.0, self.tcx) {
                        return true;
                    }
                }
            }
            _ => return false,
        }
        false
    }

    pub(super) fn suggest_missing_writer(
        &self,
        rcvr_ty: Ty<'tcx>,
        rcvr_expr: &hir::Expr<'tcx>,
    ) -> Diag<'_> {
        let mut file = None;
        let ty_str = self.tcx.short_ty_string(rcvr_ty, &mut file);
        let mut err = struct_span_code_err!(
            self.dcx(),
            rcvr_expr.span,
            E0599,
            "cannot write into `{}`",
            ty_str
        );
        err.span_note(
            rcvr_expr.span,
            "must implement `io::Write`, `fmt::Write`, or have a `write_fmt` method",
        );
        if let ExprKind::Lit(_) = rcvr_expr.kind {
            err.span_help(
                rcvr_expr.span.shrink_to_lo(),
                "a writer is needed before this format string",
            );
        };
        if let Some(file) = file {
            err.note(format!("the full type name has been written to '{}'", file.display()));
            err.note("consider using `--verbose` to print the full type name to the console");
        }

        err
    }

    pub(super) fn suggest_use_shadowed_binding_with_method(
        &self,
        self_source: SelfSource<'tcx>,
        method_name: Ident,
        ty_str_reported: &str,
        err: &mut Diag<'_>,
    ) {
        #[derive(Debug)]
        struct LetStmt {
            ty_hir_id_opt: Option<hir::HirId>,
            binding_id: hir::HirId,
            span: Span,
            init_hir_id: hir::HirId,
        }

        // Used for finding suggest binding.
        // ```rust
        // earlier binding for suggesting:
        // let y = vec![1, 2];
        // now binding:
        // if let Some(y) = x {
        //     y.push(y);
        // }
        // ```
        struct LetVisitor<'a, 'tcx> {
            // Error binding which don't have `method_name`.
            binding_name: Symbol,
            binding_id: hir::HirId,
            // Used for check if the suggest binding has `method_name`.
            fcx: &'a FnCtxt<'a, 'tcx>,
            call_expr: &'tcx Expr<'tcx>,
            method_name: Ident,
            // Suggest the binding which is shallowed.
            sugg_let: Option<LetStmt>,
        }

        impl<'a, 'tcx> LetVisitor<'a, 'tcx> {
            // Check scope of binding.
            fn is_sub_scope(&self, sub_id: hir::ItemLocalId, super_id: hir::ItemLocalId) -> bool {
                let scope_tree = self.fcx.tcx.region_scope_tree(self.fcx.body_id);
                if let Some(sub_var_scope) = scope_tree.var_scope(sub_id)
                    && let Some(super_var_scope) = scope_tree.var_scope(super_id)
                    && scope_tree.is_subscope_of(sub_var_scope, super_var_scope)
                {
                    return true;
                }
                false
            }

            // Check if an earlier shadowed binding make `the receiver` of a MethodCall has the method.
            // If it does, record the earlier binding for subsequent notes.
            fn check_and_add_sugg_binding(&mut self, binding: LetStmt) -> bool {
                if !self.is_sub_scope(self.binding_id.local_id, binding.binding_id.local_id) {
                    return false;
                }

                // Get the earlier shadowed binding'ty and use it to check the method.
                if let Some(ty_hir_id) = binding.ty_hir_id_opt
                    && let Some(tyck_ty) = self.fcx.node_ty_opt(ty_hir_id)
                {
                    if self
                        .fcx
                        .lookup_probe_for_diagnostic(
                            self.method_name,
                            tyck_ty,
                            self.call_expr,
                            ProbeScope::TraitsInScope,
                            None,
                        )
                        .is_ok()
                    {
                        self.sugg_let = Some(binding);
                        return true;
                    } else {
                        return false;
                    }
                }

                // If the shadowed binding has an itializer expression,
                // use the initializer expression'ty to try to find the method again.
                // For example like:  `let mut x = Vec::new();`,
                // `Vec::new()` is the itializer expression.
                if let Some(self_ty) = self.fcx.node_ty_opt(binding.init_hir_id)
                    && self
                        .fcx
                        .lookup_probe_for_diagnostic(
                            self.method_name,
                            self_ty,
                            self.call_expr,
                            ProbeScope::TraitsInScope,
                            None,
                        )
                        .is_ok()
                {
                    self.sugg_let = Some(binding);
                    return true;
                }
                return false;
            }
        }

        impl<'v> Visitor<'v> for LetVisitor<'_, '_> {
            type Result = ControlFlow<()>;
            fn visit_stmt(&mut self, ex: &'v hir::Stmt<'v>) -> Self::Result {
                if let hir::StmtKind::Let(&hir::LetStmt { pat, ty, init, .. }) = ex.kind
                    && let hir::PatKind::Binding(_, binding_id, binding_name, ..) = pat.kind
                    && let Some(init) = init
                    && binding_name.name == self.binding_name
                    && binding_id != self.binding_id
                {
                    if self.check_and_add_sugg_binding(LetStmt {
                        ty_hir_id_opt: if let Some(ty) = ty { Some(ty.hir_id) } else { None },
                        binding_id,
                        span: pat.span,
                        init_hir_id: init.hir_id,
                    }) {
                        return ControlFlow::Break(());
                    }
                    ControlFlow::Continue(())
                } else {
                    hir::intravisit::walk_stmt(self, ex)
                }
            }

            // Used for find the error binding.
            // When the visitor reaches this point, all the shadowed bindings
            // have been found, so the visitor ends.
            fn visit_pat(&mut self, p: &'v hir::Pat<'v>) -> Self::Result {
                match p.kind {
                    hir::PatKind::Binding(_, binding_id, binding_name, _) => {
                        if binding_name.name == self.binding_name && binding_id == self.binding_id {
                            return ControlFlow::Break(());
                        }
                    }
                    _ => {
                        intravisit::walk_pat(self, p);
                    }
                }
                ControlFlow::Continue(())
            }
        }

        if let SelfSource::MethodCall(rcvr) = self_source
            && let hir::ExprKind::Path(QPath::Resolved(_, path)) = rcvr.kind
            && let hir::def::Res::Local(recv_id) = path.res
            && let Some(segment) = path.segments.first()
        {
            let body = self.tcx.hir().body_owned_by(self.body_id);

            if let Node::Expr(call_expr) = self.tcx.parent_hir_node(rcvr.hir_id) {
                let mut let_visitor = LetVisitor {
                    fcx: self,
                    call_expr,
                    binding_name: segment.ident.name,
                    binding_id: recv_id,
                    method_name,
                    sugg_let: None,
                };
                let_visitor.visit_body(&body);
                if let Some(sugg_let) = let_visitor.sugg_let
                    && let Some(self_ty) = self.node_ty_opt(sugg_let.init_hir_id)
                {
                    let _sm = self.infcx.tcx.sess.source_map();
                    let rcvr_name = segment.ident.name;
                    let mut span = MultiSpan::from_span(sugg_let.span);
                    span.push_span_label(sugg_let.span,
                            format!("`{rcvr_name}` of type `{self_ty}` that has method `{method_name}` defined earlier here"));
                    span.push_span_label(
                        self.tcx.hir().span(recv_id),
                        format!(
                            "earlier `{rcvr_name}` shadowed here with type `{ty_str_reported}`"
                        ),
                    );
                    err.span_note(
                        span,
                        format!(
                            "there's an earlier shadowed binding `{rcvr_name}` of type `{self_ty}` \
                                    that has method `{method_name}` available"
                        ),
                    );
                }
            }
        }
    }

    pub(crate) fn confusable_method_name(
        &self,
        err: &mut Diag<'_>,
        rcvr_ty: Ty<'tcx>,
        item_name: Ident,
        call_args: Option<Vec<Ty<'tcx>>>,
    ) -> Option<Symbol> {
        if let ty::Adt(adt, adt_args) = rcvr_ty.kind() {
            for inherent_impl_did in self.tcx.inherent_impls(adt.did()).into_iter().flatten() {
                for inherent_method in
                    self.tcx.associated_items(inherent_impl_did).in_definition_order()
                {
                    if let Some(attr) =
                        self.tcx.get_attr(inherent_method.def_id, sym::rustc_confusables)
                        && let Some(candidates) = parse_confusables(attr)
                        && candidates.contains(&item_name.name)
                        && let ty::AssocKind::Fn = inherent_method.kind
                    {
                        let args =
                            ty::GenericArgs::identity_for_item(self.tcx, inherent_method.def_id)
                                .rebase_onto(
                                    self.tcx,
                                    inherent_method.container_id(self.tcx),
                                    adt_args,
                                );
                        let fn_sig =
                            self.tcx.fn_sig(inherent_method.def_id).instantiate(self.tcx, args);
                        let fn_sig = self.instantiate_binder_with_fresh_vars(
                            item_name.span,
                            infer::FnCall,
                            fn_sig,
                        );
                        if let Some(ref args) = call_args
                            && fn_sig.inputs()[1..]
                                .iter()
                                .zip(args.into_iter())
                                .all(|(expected, found)| self.can_coerce(*expected, *found))
                            && fn_sig.inputs()[1..].len() == args.len()
                        {
                            err.span_suggestion_verbose(
                                item_name.span,
                                format!("you might have meant to use `{}`", inherent_method.name),
                                inherent_method.name,
                                Applicability::MaybeIncorrect,
                            );
                            return Some(inherent_method.name);
                        } else if let None = call_args {
                            err.span_note(
                                self.tcx.def_span(inherent_method.def_id),
                                format!(
                                    "you might have meant to use method `{}`",
                                    inherent_method.name,
                                ),
                            );
                            return Some(inherent_method.name);
                        }
                    }
                }
            }
        }
        None
    }

    /// Look at all the associated functions without receivers in the type's inherent impls
    /// to look for builders that return `Self`, `Option<Self>` or `Result<Self, _>`.
    pub(super) fn find_builder_fn(
        &self,
        err: &mut Diag<'_>,
        rcvr_ty: Ty<'tcx>,
        expr_id: hir::HirId,
    ) {
        let ty::Adt(adt_def, _) = rcvr_ty.kind() else {
            return;
        };
        // FIXME(oli-obk): try out bubbling this error up one level and cancelling the other error in that case.
        let Ok(impls) = self.tcx.inherent_impls(adt_def.did()) else { return };
        let mut items = impls
            .iter()
            .flat_map(|i| self.tcx.associated_items(i).in_definition_order())
            // Only assoc fn with no receivers and only if
            // they are resolvable
            .filter(|item| {
                matches!(item.kind, ty::AssocKind::Fn)
                    && !item.fn_has_self_parameter
                    && self
                        .probe_for_name(
                            Mode::Path,
                            item.ident(self.tcx),
                            None,
                            IsSuggestion(true),
                            rcvr_ty,
                            expr_id,
                            ProbeScope::TraitsInScope,
                        )
                        .is_ok()
            })
            .filter_map(|item| {
                // Only assoc fns that return `Self`, `Option<Self>` or `Result<Self, _>`.
                let ret_ty = self
                    .tcx
                    .fn_sig(item.def_id)
                    .instantiate(self.tcx, self.fresh_args_for_item(DUMMY_SP, item.def_id))
                    .output();
                let ret_ty = self.tcx.instantiate_bound_regions_with_erased(ret_ty);
                let ty::Adt(def, args) = ret_ty.kind() else {
                    return None;
                };
                // Check for `-> Self`
                if self.can_eq(self.param_env, ret_ty, rcvr_ty) {
                    return Some((item.def_id, ret_ty));
                }
                // Check for `-> Option<Self>` or `-> Result<Self, _>`
                if ![self.tcx.lang_items().option_type(), self.tcx.get_diagnostic_item(sym::Result)]
                    .contains(&Some(def.did()))
                {
                    return None;
                }
                let arg = args.get(0)?.expect_ty();
                if self.can_eq(self.param_env, rcvr_ty, arg) {
                    Some((item.def_id, ret_ty))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let post = if items.len() > 5 {
            let items_len = items.len();
            items.truncate(4);
            format!("\nand {} others", items_len - 4)
        } else {
            String::new()
        };
        match &items[..] {
            [] => {}
            [(def_id, ret_ty)] => {
                err.span_note(
                    self.tcx.def_span(def_id),
                    format!(
                        "if you're trying to build a new `{rcvr_ty}`, consider using `{}` which \
                         returns `{ret_ty}`",
                        self.tcx.def_path_str(def_id),
                    ),
                );
            }
            _ => {
                let span: MultiSpan = items
                    .iter()
                    .map(|(def_id, _)| self.tcx.def_span(def_id))
                    .collect::<Vec<Span>>()
                    .into();
                err.span_note(
                    span,
                    format!(
                        "if you're trying to build a new `{rcvr_ty}` consider using one of the \
                         following associated functions:\n{}{post}",
                        items
                            .iter()
                            .map(|(def_id, _ret_ty)| self.tcx.def_path_str(def_id))
                            .collect::<Vec<String>>()
                            .join("\n")
                    ),
                );
            }
        }
    }

    /// Suggest possible range with adding parentheses, for example:
    /// when encountering `0..1.map(|i| i + 1)` suggest `(0..1).map(|i| i + 1)`.
    pub(super) fn report_failed_method_call_on_range_end(
        &self,
        tcx: TyCtxt<'tcx>,
        actual: Ty<'tcx>,
        source: SelfSource<'tcx>,
        span: Span,
        item_name: Ident,
        ty_str: &str,
    ) -> Result<(), ErrorGuaranteed> {
        if let SelfSource::MethodCall(expr) = source {
            for (_, parent) in tcx.hir().parent_iter(expr.hir_id).take(5) {
                if let Node::Expr(parent_expr) = parent {
                    let lang_item = match parent_expr.kind {
                        ExprKind::Struct(qpath, _, _) => match *qpath {
                            QPath::LangItem(LangItem::Range, ..) => Some(LangItem::Range),
                            QPath::LangItem(LangItem::RangeTo, ..) => Some(LangItem::RangeTo),
                            QPath::LangItem(LangItem::RangeToInclusive, ..) => {
                                Some(LangItem::RangeToInclusive)
                            }
                            _ => None,
                        },
                        ExprKind::Call(func, _) => match func.kind {
                            // `..=` desugars into `::std::ops::RangeInclusive::new(...)`.
                            ExprKind::Path(QPath::LangItem(LangItem::RangeInclusiveNew, ..)) => {
                                Some(LangItem::RangeInclusiveStruct)
                            }
                            _ => None,
                        },
                        _ => None,
                    };

                    if lang_item.is_none() {
                        continue;
                    }

                    let span_included = match parent_expr.kind {
                        hir::ExprKind::Struct(_, eps, _) => {
                            eps.len() > 0 && eps.last().is_some_and(|ep| ep.span.contains(span))
                        }
                        // `..=` desugars into `::std::ops::RangeInclusive::new(...)`.
                        hir::ExprKind::Call(func, ..) => func.span.contains(span),
                        _ => false,
                    };

                    if !span_included {
                        continue;
                    }

                    let Some(range_def_id) =
                        lang_item.and_then(|lang_item| self.tcx.lang_items().get(lang_item))
                    else {
                        continue;
                    };
                    let range_ty =
                        self.tcx.type_of(range_def_id).instantiate(self.tcx, &[actual.into()]);

                    let pick = self.lookup_probe_for_diagnostic(
                        item_name,
                        range_ty,
                        expr,
                        ProbeScope::AllTraits,
                        None,
                    );
                    if pick.is_ok() {
                        let range_span = parent_expr.span.with_hi(expr.span.hi());
                        return Err(self.dcx().emit_err(errors::MissingParenthesesInRange {
                            span,
                            ty_str: ty_str.to_string(),
                            method_name: item_name.as_str().to_string(),
                            add_missing_parentheses: Some(errors::AddMissingParenthesesInRange {
                                func_name: item_name.name.as_str().to_string(),
                                left: range_span.shrink_to_lo(),
                                right: range_span.shrink_to_hi(),
                            }),
                        }));
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn report_failed_method_call_on_numerical_infer_var(
        &self,
        tcx: TyCtxt<'tcx>,
        actual: Ty<'tcx>,
        source: SelfSource<'_>,
        span: Span,
        item_kind: &str,
        item_name: Ident,
        ty_str: &str,
    ) -> Result<(), ErrorGuaranteed> {
        let found_candidate = all_traits(self.tcx)
            .into_iter()
            .any(|info| self.associated_value(info.def_id, item_name).is_some());
        let found_assoc = |ty: Ty<'tcx>| {
            simplify_type(tcx, ty, TreatParams::InstantiateWithInfer)
                .and_then(|simp| {
                    tcx.incoherent_impls(simp)
                        .into_iter()
                        .flatten()
                        .find_map(|&id| self.associated_value(id, item_name))
                })
                .is_some()
        };
        let found_candidate = found_candidate
            || found_assoc(tcx.types.i8)
            || found_assoc(tcx.types.i16)
            || found_assoc(tcx.types.i32)
            || found_assoc(tcx.types.i64)
            || found_assoc(tcx.types.i128)
            || found_assoc(tcx.types.u8)
            || found_assoc(tcx.types.u16)
            || found_assoc(tcx.types.u32)
            || found_assoc(tcx.types.u64)
            || found_assoc(tcx.types.u128)
            || found_assoc(tcx.types.f32)
            || found_assoc(tcx.types.f64);
        if found_candidate
            && actual.is_numeric()
            && !actual.has_concrete_skeleton()
            && let SelfSource::MethodCall(expr) = source
        {
            let mut err = struct_span_code_err!(
                self.dcx(),
                span,
                E0689,
                "can't call {} `{}` on ambiguous numeric type `{}`",
                item_kind,
                item_name,
                ty_str
            );
            let concrete_type = if actual.is_integral() { "i32" } else { "f32" };
            match expr.kind {
                ExprKind::Lit(lit) => {
                    // numeric literal
                    let snippet = tcx
                        .sess
                        .source_map()
                        .span_to_snippet(lit.span)
                        .unwrap_or_else(|_| "<numeric literal>".to_owned());

                    // If this is a floating point literal that ends with '.',
                    // get rid of it to stop this from becoming a member access.
                    let snippet = snippet.strip_suffix('.').unwrap_or(&snippet);
                    err.span_suggestion(
                        lit.span,
                        format!(
                            "you must specify a concrete type for this numeric value, \
                                         like `{concrete_type}`"
                        ),
                        format!("{snippet}_{concrete_type}"),
                        Applicability::MaybeIncorrect,
                    );
                }
                ExprKind::Path(QPath::Resolved(_, path)) => {
                    // local binding
                    if let hir::def::Res::Local(hir_id) = path.res {
                        let span = tcx.hir().span(hir_id);
                        let filename = tcx.sess.source_map().span_to_filename(span);

                        let parent_node = self.tcx.parent_hir_node(hir_id);
                        let msg = format!(
                            "you must specify a type for this binding, like `{concrete_type}`",
                        );

                        match (filename, parent_node) {
                            (
                                FileName::Real(_),
                                Node::LetStmt(hir::LetStmt {
                                    source: hir::LocalSource::Normal,
                                    ty,
                                    ..
                                }),
                            ) => {
                                let type_span = ty
                                    .map(|ty| ty.span.with_lo(span.hi()))
                                    .unwrap_or(span.shrink_to_hi());
                                err.span_suggestion(
                                    // account for `let x: _ = 42;`
                                    //                   ^^^
                                    type_span,
                                    msg,
                                    format!(": {concrete_type}"),
                                    Applicability::MaybeIncorrect,
                                );
                            }
                            _ => {
                                err.span_label(span, msg);
                            }
                        }
                    }
                }
                _ => {}
            }
            return Err(err.emit());
        }
        Ok(())
    }

    pub(super) fn suggest_unwrapping_inner_self(
        &self,
        err: &mut Diag<'_>,
        source: SelfSource<'tcx>,
        actual: Ty<'tcx>,
        item_name: Ident,
    ) {
        let tcx = self.tcx;
        let SelfSource::MethodCall(expr) = source else {
            return;
        };
        let call_expr = tcx.hir().expect_expr(tcx.parent_hir_id(expr.hir_id));

        let ty::Adt(kind, args) = actual.kind() else {
            return;
        };
        match kind.adt_kind() {
            ty::AdtKind::Enum => {
                let matching_variants: Vec<_> = kind
                    .variants()
                    .iter()
                    .flat_map(|variant| {
                        let [field] = &variant.fields.raw[..] else {
                            return None;
                        };
                        let field_ty = field.ty(tcx, args);

                        // Skip `_`, since that'll just lead to ambiguity.
                        if self.resolve_vars_if_possible(field_ty).is_ty_var() {
                            return None;
                        }

                        self.lookup_probe_for_diagnostic(
                            item_name,
                            field_ty,
                            call_expr,
                            ProbeScope::TraitsInScope,
                            None,
                        )
                        .ok()
                        .map(|pick| (variant, field, pick))
                    })
                    .collect();

                let ret_ty_matches = |diagnostic_item| {
                    if let Some(ret_ty) = self
                        .ret_coercion
                        .as_ref()
                        .map(|c| self.resolve_vars_if_possible(c.borrow().expected_ty()))
                        && let ty::Adt(kind, _) = ret_ty.kind()
                        && tcx.get_diagnostic_item(diagnostic_item) == Some(kind.did())
                    {
                        true
                    } else {
                        false
                    }
                };

                match &matching_variants[..] {
                    [(_, field, pick)] => {
                        let self_ty = field.ty(tcx, args);
                        err.span_note(
                            tcx.def_span(pick.item.def_id),
                            format!("the method `{item_name}` exists on the type `{self_ty}`"),
                        );
                        let (article, kind, variant, question) =
                            if tcx.is_diagnostic_item(sym::Result, kind.did()) {
                                ("a", "Result", "Err", ret_ty_matches(sym::Result))
                            } else if tcx.is_diagnostic_item(sym::Option, kind.did()) {
                                ("an", "Option", "None", ret_ty_matches(sym::Option))
                            } else {
                                return;
                            };
                        if question {
                            err.span_suggestion_verbose(
                                expr.span.shrink_to_hi(),
                                format!(
                                    "use the `?` operator to extract the `{self_ty}` value, propagating \
                                    {article} `{kind}::{variant}` value to the caller"
                                ),
                                "?",
                                Applicability::MachineApplicable,
                            );
                        } else {
                            err.span_suggestion_verbose(
                                expr.span.shrink_to_hi(),
                                format!(
                                    "consider using `{kind}::expect` to unwrap the `{self_ty}` value, \
                                    panicking if the value is {article} `{kind}::{variant}`"
                                ),
                                ".expect(\"REASON\")",
                                Applicability::HasPlaceholders,
                            );
                        }
                    }
                    // FIXME(compiler-errors): Support suggestions for other matching enum variants
                    _ => {}
                }
            }
            // Target wrapper types - types that wrap or pretend to wrap another type,
            // perhaps this inner type is meant to be called?
            ty::AdtKind::Struct | ty::AdtKind::Union => {
                let [first] = ***args else {
                    return;
                };
                let ty::GenericArgKind::Type(ty) = first.unpack() else {
                    return;
                };
                let Ok(pick) = self.lookup_probe_for_diagnostic(
                    item_name,
                    ty,
                    call_expr,
                    ProbeScope::TraitsInScope,
                    None,
                ) else {
                    return;
                };

                let name = self.ty_to_value_string(actual);
                let inner_id = kind.did();
                let mutable = if let Some(AutorefOrPtrAdjustment::Autoref { mutbl, .. }) =
                    pick.autoref_or_ptr_adjustment
                {
                    Some(mutbl)
                } else {
                    None
                };

                if tcx.is_diagnostic_item(sym::LocalKey, inner_id) {
                    err.help("use `with` or `try_with` to access thread local storage");
                } else if tcx.is_lang_item(kind.did(), LangItem::MaybeUninit) {
                    err.help(format!(
                        "if this `{name}` has been initialized, \
                        use one of the `assume_init` methods to access the inner value"
                    ));
                } else if tcx.is_diagnostic_item(sym::RefCell, inner_id) {
                    let (suggestion, borrow_kind, panic_if) = match mutable {
                        Some(Mutability::Not) => (".borrow()", "borrow", "a mutable borrow exists"),
                        Some(Mutability::Mut) => {
                            (".borrow_mut()", "mutably borrow", "any borrows exist")
                        }
                        None => return,
                    };
                    err.span_suggestion_verbose(
                        expr.span.shrink_to_hi(),
                        format!(
                            "use `{suggestion}` to {borrow_kind} the `{ty}`, \
                            panicking if {panic_if}"
                        ),
                        suggestion,
                        Applicability::MaybeIncorrect,
                    );
                } else if tcx.is_diagnostic_item(sym::Mutex, inner_id) {
                    err.span_suggestion_verbose(
                        expr.span.shrink_to_hi(),
                        format!(
                            "use `.lock().unwrap()` to borrow the `{ty}`, \
                            blocking the current thread until it can be acquired"
                        ),
                        ".lock().unwrap()",
                        Applicability::MaybeIncorrect,
                    );
                } else if tcx.is_diagnostic_item(sym::RwLock, inner_id) {
                    let (suggestion, borrow_kind) = match mutable {
                        Some(Mutability::Not) => (".read().unwrap()", "borrow"),
                        Some(Mutability::Mut) => (".write().unwrap()", "mutably borrow"),
                        None => return,
                    };
                    err.span_suggestion_verbose(
                        expr.span.shrink_to_hi(),
                        format!(
                            "use `{suggestion}` to {borrow_kind} the `{ty}`, \
                            blocking the current thread until it can be acquired"
                        ),
                        suggestion,
                        Applicability::MaybeIncorrect,
                    );
                } else {
                    return;
                };

                err.span_note(
                    tcx.def_span(pick.item.def_id),
                    format!("the method `{item_name}` exists on the type `{ty}`"),
                );
            }
        }
    }

    pub(super) fn note_derefed_ty_has_method(
        &self,
        err: &mut Diag<'_>,
        self_source: SelfSource<'tcx>,
        rcvr_ty: Ty<'tcx>,
        item_name: Ident,
        expected: Expectation<'tcx>,
    ) {
        let SelfSource::QPath(ty) = self_source else {
            return;
        };
        for (deref_ty, _) in self.autoderef(DUMMY_SP, rcvr_ty).skip(1) {
            if let Ok(pick) = self.probe_for_name(
                Mode::Path,
                item_name,
                expected.only_has_type(self),
                IsSuggestion(true),
                deref_ty,
                ty.hir_id,
                ProbeScope::TraitsInScope,
            ) {
                if deref_ty.is_suggestable(self.tcx, true)
                    // If this method receives `&self`, then the provided
                    // argument _should_ coerce, so it's valid to suggest
                    // just changing the path.
                    && pick.item.fn_has_self_parameter
                    && let Some(self_ty) =
                        self.tcx.fn_sig(pick.item.def_id).instantiate_identity().inputs().skip_binder().get(0)
                    && self_ty.is_ref()
                {
                    let suggested_path = match deref_ty.kind() {
                        ty::Bool
                        | ty::Char
                        | ty::Int(_)
                        | ty::Uint(_)
                        | ty::Float(_)
                        | ty::Adt(_, _)
                        | ty::Str
                        | ty::Alias(ty::Projection | ty::Inherent, _)
                        | ty::Param(_) => format!("{deref_ty}"),
                        // we need to test something like  <&[_]>::len or <(&[u32])>::len
                        // and Vec::function();
                        // <&[_]>::len or <&[u32]>::len doesn't need an extra "<>" between
                        // but for Adt type like Vec::function()
                        // we would suggest <[_]>::function();
                        _ if self
                            .tcx
                            .sess
                            .source_map()
                            .span_wrapped_by_angle_or_parentheses(ty.span) =>
                        {
                            format!("{deref_ty}")
                        }
                        _ => format!("<{deref_ty}>"),
                    };
                    err.span_suggestion_verbose(
                        ty.span,
                        format!("the function `{item_name}` is implemented on `{deref_ty}`"),
                        suggested_path,
                        Applicability::MaybeIncorrect,
                    );
                } else {
                    err.span_note(
                        ty.span,
                        format!("the function `{item_name}` is implemented on `{deref_ty}`"),
                    );
                }
                return;
            }
        }
    }

    /// Print out the type for use in value namespace.
    pub(super) fn ty_to_value_string(&self, ty: Ty<'tcx>) -> String {
        match ty.kind() {
            ty::Adt(def, args) => self.tcx.def_path_str_with_args(def.did(), args),
            _ => self.ty_to_string(ty),
        }
    }

    pub(super) fn suggest_await_before_method(
        &self,
        err: &mut Diag<'_>,
        item_name: Ident,
        ty: Ty<'tcx>,
        call: &hir::Expr<'_>,
        span: Span,
        return_type: Option<Ty<'tcx>>,
    ) {
        let output_ty = match self.err_ctxt().get_impl_future_output_ty(ty) {
            Some(output_ty) => self.resolve_vars_if_possible(output_ty),
            _ => return,
        };
        let method_exists =
            self.method_exists_for_diagnostic(item_name, output_ty, call.hir_id, return_type);
        debug!("suggest_await_before_method: is_method_exist={}", method_exists);
        if method_exists {
            err.span_suggestion_verbose(
                span.shrink_to_lo(),
                "consider `await`ing on the `Future` and calling the method on its `Output`",
                "await.",
                Applicability::MaybeIncorrect,
            );
        }
    }

    pub(super) fn suggest_use_candidates<F>(&self, candidates: Vec<DefId>, handle_candidates: F)
    where
        F: FnOnce(Vec<String>, Vec<String>, Span),
    {
        let parent_map = self.tcx.visible_parent_map(());

        let scope = self.tcx.parent_module_from_def_id(self.body_id);
        let (accessible_candidates, inaccessible_candidates): (Vec<_>, Vec<_>) =
            candidates.into_iter().partition(|id| {
                let vis = self.tcx.visibility(*id);
                vis.is_accessible_from(scope, self.tcx)
            });

        let sugg = |candidates: Vec<_>, visible| {
            // Separate out candidates that must be imported with a glob, because they are named `_`
            // and cannot be referred with their identifier.
            let (candidates, globs): (Vec<_>, Vec<_>) =
                candidates.into_iter().partition(|trait_did| {
                    if let Some(parent_did) = parent_map.get(trait_did) {
                        // If the item is re-exported as `_`, we should suggest a glob-import instead.
                        if *parent_did != self.tcx.parent(*trait_did)
                            && self
                                .tcx
                                .module_children(*parent_did)
                                .iter()
                                .filter(|child| child.res.opt_def_id() == Some(*trait_did))
                                .all(|child| child.ident.name == kw::Underscore)
                        {
                            return false;
                        }
                    }

                    true
                });

            let prefix = if visible { "use " } else { "" };
            let postfix = if visible { ";" } else { "" };
            let path_strings = candidates.iter().map(|trait_did| {
                format!(
                    "{prefix}{}{postfix}\n",
                    with_crate_prefix!(self.tcx.def_path_str(*trait_did)),
                )
            });

            let glob_path_strings = globs.iter().map(|trait_did| {
                let parent_did = parent_map.get(trait_did).unwrap();
                format!(
                    "{prefix}{}::*{postfix} // trait {}\n",
                    with_crate_prefix!(self.tcx.def_path_str(*parent_did)),
                    self.tcx.item_name(*trait_did),
                )
            });
            let mut sugg: Vec<_> = path_strings.chain(glob_path_strings).collect();
            sugg.sort();
            sugg
        };

        let accessible_sugg = sugg(accessible_candidates, true);
        let inaccessible_sugg = sugg(inaccessible_candidates, false);

        let (module, _, _) = self.tcx.hir().get_module(scope);
        let span = module.spans.inject_use_span;
        handle_candidates(accessible_sugg, inaccessible_sugg, span);
    }

    /// issue #102320, for `unwrap_or` with closure as argument, suggest `unwrap_or_else`
    /// FIXME: currently not working for suggesting `map_or_else`, see #102408
    pub(crate) fn suggest_else_fn_with_closure(
        &self,
        err: &mut Diag<'_>,
        expr: &hir::Expr<'_>,
        found: Ty<'tcx>,
        expected: Ty<'tcx>,
    ) -> bool {
        let Some((_def_id_or_name, output, _inputs)) = self.extract_callable_info(found) else {
            return false;
        };

        if !self.can_coerce(output, expected) {
            return false;
        }

        if let Node::Expr(call_expr) = self.tcx.parent_hir_node(expr.hir_id)
            && let hir::ExprKind::MethodCall(
                hir::PathSegment { ident: method_name, .. },
                self_expr,
                args,
                ..,
            ) = call_expr.kind
            && let Some(self_ty) = self.typeck_results.borrow().expr_ty_opt(self_expr)
        {
            let new_name = Ident {
                name: Symbol::intern(&format!("{}_else", method_name.as_str())),
                span: method_name.span,
            };
            let probe = self.lookup_probe_for_diagnostic(
                new_name,
                self_ty,
                self_expr,
                ProbeScope::TraitsInScope,
                Some(expected),
            );

            // check the method arguments number
            if let Ok(pick) = probe
                && let fn_sig = self.tcx.fn_sig(pick.item.def_id)
                && let fn_args = fn_sig.skip_binder().skip_binder().inputs()
                && fn_args.len() == args.len() + 1
            {
                err.span_suggestion_verbose(
                    method_name.span.shrink_to_hi(),
                    format!("try calling `{}` instead", new_name.name.as_str()),
                    "_else",
                    Applicability::MaybeIncorrect,
                );
                return true;
            }
        }
        false
    }

    /// Checks whether there is a local type somewhere in the chain of
    /// autoderefs of `rcvr_ty`.
    pub(super) fn type_derefs_to_local(
        &self,
        span: Span,
        rcvr_ty: Ty<'tcx>,
        source: SelfSource<'tcx>,
    ) -> bool {
        fn is_local(ty: Ty<'_>) -> bool {
            match ty.kind() {
                ty::Adt(def, _) => def.did().is_local(),
                ty::Foreign(did) => did.is_local(),
                ty::Dynamic(tr, ..) => tr.principal().is_some_and(|d| d.def_id().is_local()),
                ty::Param(_) => true,

                // Everything else (primitive types, etc.) is effectively
                // non-local (there are "edge" cases, e.g., `(LocalType,)`, but
                // the noise from these sort of types is usually just really
                // annoying, rather than any sort of help).
                _ => false,
            }
        }

        // This occurs for UFCS desugaring of `T::method`, where there is no
        // receiver expression for the method call, and thus no autoderef.
        if let SelfSource::QPath(_) = source {
            return is_local(rcvr_ty);
        }

        self.autoderef(span, rcvr_ty).any(|(ty, _)| is_local(ty))
    }
}
