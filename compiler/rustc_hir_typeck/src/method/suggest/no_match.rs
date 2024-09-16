#![allow(unused_imports)]

//! Give useful errors and suggestions to users when an item can't be
//! found or is otherwise invalid.

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

use super::misc;
use crate::errors::{self, CandidateTraitNote, NoAssociatedItem};
use crate::method::probe::{AutorefOrPtrAdjustment, IsSuggestion, Mode, ProbeScope};
use crate::method::suggest::SelfSource;
use crate::method::{CandidateSource, MethodError, NoMatchData};
use crate::{Expectation, FnCtxt};

pub(super) trait SuggestNoMatchMethodError<'tcx> {
    fn report_no_match_method_error(
        &self,
        span: Span,
        rcvr_ty: Ty<'tcx>,
        item_name: Ident,
        expr_id: hir::HirId,
        source: SelfSource<'tcx>,
        args: Option<&'tcx [hir::Expr<'tcx>]>,
        sugg_span: Span,
        no_match_data: &mut NoMatchData<'tcx>,
        expected: Expectation<'tcx>,
        trait_missing_method: bool,
    ) -> ErrorGuaranteed;
}

impl<'a, 'tcx> SuggestNoMatchMethodError<'tcx> for FnCtxt<'a, 'tcx> {
    fn report_no_match_method_error(
        &self,
        mut span: Span,
        rcvr_ty: Ty<'tcx>,
        item_name: Ident,
        expr_id: hir::HirId,
        source: SelfSource<'tcx>,
        args: Option<&'tcx [hir::Expr<'tcx>]>,
        sugg_span: Span,
        no_match_data: &mut NoMatchData<'tcx>,
        expected: Expectation<'tcx>,
        trait_missing_method: bool,
    ) -> ErrorGuaranteed {
        let mode = no_match_data.mode;
        let tcx = self.tcx;
        let rcvr_ty = self.resolve_vars_if_possible(rcvr_ty);
        let mut ty_file = None;
        let (mut ty_str, short_ty_str) =
            if trait_missing_method && let ty::Dynamic(predicates, _, _) = rcvr_ty.kind() {
                (predicates.to_string(), with_forced_trimmed_paths!(predicates.to_string()))
            } else {
                (
                    tcx.short_ty_string(rcvr_ty, &mut ty_file),
                    with_forced_trimmed_paths!(rcvr_ty.to_string()),
                )
            };
        let is_method = mode == Mode::MethodCall;
        let unsatisfied_predicates = &no_match_data.unsatisfied_predicates;
        let similar_candidate = no_match_data.similar_candidate;
        let item_kind = if is_method {
            "method"
        } else if rcvr_ty.is_enum() {
            "variant or associated item"
        } else {
            match (item_name.as_str().chars().next(), rcvr_ty.is_fresh_ty()) {
                (Some(name), false) if name.is_lowercase() => "function or associated item",
                (Some(_), false) => "associated item",
                (Some(_), true) | (None, false) => "variant or associated item",
                (None, true) => "variant",
            }
        };

        // We could pass the file for long types into these two, but it isn't strictly necessary
        // given how targeted they are.
        if let Err(guar) = self.report_failed_method_call_on_range_end(
            tcx,
            rcvr_ty,
            source,
            span,
            item_name,
            &short_ty_str,
        ) {
            return guar;
        }
        if let Err(guar) = self.report_failed_method_call_on_numerical_infer_var(
            tcx,
            rcvr_ty,
            source,
            span,
            item_kind,
            item_name,
            &short_ty_str,
        ) {
            return guar;
        }
        span = item_name.span;

        // Don't show generic arguments when the method can't be found in any implementation (#81576).
        let mut ty_str_reported = ty_str.clone();
        if let ty::Adt(_, generics) = rcvr_ty.kind() {
            if generics.len() > 0 {
                let mut autoderef = self.autoderef(span, rcvr_ty);
                let candidate_found = autoderef.any(|(ty, _)| {
                    if let ty::Adt(adt_def, _) = ty.kind() {
                        self.tcx
                            .inherent_impls(adt_def.did())
                            .into_iter()
                            .flatten()
                            .any(|def_id| self.associated_value(*def_id, item_name).is_some())
                    } else {
                        false
                    }
                });
                let has_deref = autoderef.step_count() > 0;
                if !candidate_found && !has_deref && unsatisfied_predicates.is_empty() {
                    if let Some((path_string, _)) = ty_str.split_once('<') {
                        ty_str_reported = path_string.to_string();
                    }
                }
            }
        }

        let is_write = sugg_span.ctxt().outer_expn_data().macro_def_id.is_some_and(|def_id| {
            tcx.is_diagnostic_item(sym::write_macro, def_id)
                || tcx.is_diagnostic_item(sym::writeln_macro, def_id)
        }) && item_name.name == Symbol::intern("write_fmt");
        let mut err = if is_write && let SelfSource::MethodCall(rcvr_expr) = source {
            self.suggest_missing_writer(rcvr_ty, rcvr_expr)
        } else {
            let mut err = self.dcx().create_err(NoAssociatedItem {
                span,
                item_kind,
                item_name,
                ty_prefix: if trait_missing_method {
                    // FIXME(mu001999) E0599 maybe not suitable here because it is for types
                    Cow::from("trait")
                } else {
                    rcvr_ty.prefix_string(self.tcx)
                },
                ty_str: ty_str_reported.clone(),
                trait_missing_method,
            });

            if is_method {
                self.suggest_use_shadowed_binding_with_method(
                    source,
                    item_name,
                    &ty_str_reported,
                    &mut err,
                );
            }

            err
        };
        if tcx.sess.source_map().is_multiline(sugg_span) {
            err.span_label(sugg_span.with_hi(span.lo()), "");
        }

        if short_ty_str.len() < ty_str.len() && ty_str.len() > 10 {
            ty_str = short_ty_str;
        }

        if let Some(file) = ty_file {
            err.note(format!("the full type name has been written to '{}'", file.display(),));
            err.note("consider using `--verbose` to print the full type name to the console");
        }
        if rcvr_ty.references_error() {
            err.downgrade_to_delayed_bug();
        }

        if matches!(source, SelfSource::QPath(_)) && args.is_some() {
            self.find_builder_fn(&mut err, rcvr_ty, expr_id);
        }

        if tcx.ty_is_opaque_future(rcvr_ty) && item_name.name == sym::poll {
            err.help(format!(
                "method `poll` found on `Pin<&mut {ty_str}>`, \
                see documentation for `std::pin::Pin`"
            ));
            err.help("self type must be pinned to call `Future::poll`, \
                see https://rust-lang.github.io/async-book/04_pinning/01_chapter.html#pinning-in-practice"
            );
        }

        if let Mode::MethodCall = mode
            && let SelfSource::MethodCall(cal) = source
        {
            self.suggest_await_before_method(
                &mut err,
                item_name,
                rcvr_ty,
                cal,
                span,
                expected.only_has_type(self),
            );
        }
        if let Some(span) =
            tcx.resolutions(()).confused_type_with_std_module.get(&span.with_parent(None))
        {
            err.span_suggestion(
                span.shrink_to_lo(),
                "you are looking for the module in `std`, not the primitive type",
                "std::",
                Applicability::MachineApplicable,
            );
        }

        // on pointers, check if the method would exist on a reference
        if let SelfSource::MethodCall(rcvr_expr) = source
            && let ty::RawPtr(ty, ptr_mutbl) = *rcvr_ty.kind()
            && let Ok(pick) = self.lookup_probe_for_diagnostic(
                item_name,
                Ty::new_ref(tcx, ty::Region::new_error_misc(tcx), ty, ptr_mutbl),
                self.tcx.hir().expect_expr(self.tcx.parent_hir_id(rcvr_expr.hir_id)),
                ProbeScope::TraitsInScope,
                None,
            )
            && let ty::Ref(_, _, sugg_mutbl) = *pick.self_ty.kind()
            && (sugg_mutbl.is_not() || ptr_mutbl.is_mut())
        {
            let (method, method_anchor) = match sugg_mutbl {
                Mutability::Not => {
                    let method_anchor = match ptr_mutbl {
                        Mutability::Not => "as_ref",
                        Mutability::Mut => "as_ref-1",
                    };
                    ("as_ref", method_anchor)
                }
                Mutability::Mut => ("as_mut", "as_mut"),
            };
            err.span_note(
                tcx.def_span(pick.item.def_id),
                format!("the method `{item_name}` exists on the type `{ty}`", ty = pick.self_ty),
            );
            let mut_str = ptr_mutbl.ptr_str();
            err.note(format!(
                "you might want to use the unsafe method `<*{mut_str} T>::{method}` to get \
                an optional reference to the value behind the pointer"
            ));
            err.note(format!(
                "read the documentation for `<*{mut_str} T>::{method}` and ensure you satisfy its \
                safety preconditions before calling it to avoid undefined behavior: \
                https://doc.rust-lang.org/std/primitive.pointer.html#method.{method_anchor}"
            ));
        }

        let mut ty_span = match rcvr_ty.kind() {
            ty::Param(param_type) => {
                Some(param_type.span_from_generics(self.tcx, self.body_id.to_def_id()))
            }
            ty::Adt(def, _) if def.did().is_local() => Some(tcx.def_span(def.did())),
            _ => None,
        };

        if let SelfSource::MethodCall(rcvr_expr) = source {
            self.suggest_fn_call(&mut err, rcvr_expr, rcvr_ty, |output_ty| {
                let call_expr =
                    self.tcx.hir().expect_expr(self.tcx.parent_hir_id(rcvr_expr.hir_id));
                let probe = self.lookup_probe_for_diagnostic(
                    item_name,
                    output_ty,
                    call_expr,
                    ProbeScope::AllTraits,
                    expected.only_has_type(self),
                );
                probe.is_ok()
            });
            self.note_internal_mutation_in_method(
                &mut err,
                rcvr_expr,
                expected.to_option(self),
                rcvr_ty,
            );
        }

        let mut custom_span_label = false;

        let static_candidates = &mut no_match_data.static_candidates;

        // `static_candidates` may have same candidates appended by
        // inherent and extension, which may result in incorrect
        // diagnostic.
        static_candidates.dedup();

        if !static_candidates.is_empty() {
            err.note(
                "found the following associated functions; to be used as methods, \
                 functions must have a `self` parameter",
            );
            err.span_label(span, "this is an associated function, not a method");
            custom_span_label = true;
        }
        if static_candidates.len() == 1 {
            self.suggest_associated_call_syntax(
                &mut err,
                static_candidates,
                rcvr_ty,
                source,
                item_name,
                args,
                sugg_span,
            );
            self.note_candidates_on_method_error(
                rcvr_ty,
                item_name,
                source,
                args,
                span,
                &mut err,
                static_candidates,
                None,
            );
        } else if static_candidates.len() > 1 {
            self.note_candidates_on_method_error(
                rcvr_ty,
                item_name,
                source,
                args,
                span,
                &mut err,
                static_candidates,
                Some(sugg_span),
            );
        }

        let mut bound_spans: SortedMap<Span, Vec<String>> = Default::default();
        let mut restrict_type_params = false;
        let mut suggested_derive = false;
        let mut unsatisfied_bounds = false;
        if item_name.name == sym::count && self.is_slice_ty(rcvr_ty, span) {
            let msg = "consider using `len` instead";
            if let SelfSource::MethodCall(_expr) = source {
                err.span_suggestion_short(span, msg, "len", Applicability::MachineApplicable);
            } else {
                err.span_label(span, msg);
            }
            if let Some(iterator_trait) = self.tcx.get_diagnostic_item(sym::Iterator) {
                let iterator_trait = self.tcx.def_path_str(iterator_trait);
                err.note(format!(
                    "`count` is defined on `{iterator_trait}`, which `{rcvr_ty}` does not implement"
                ));
            }
        } else if self.impl_into_iterator_should_be_iterator(rcvr_ty, span, unsatisfied_predicates)
        {
            err.span_label(span, format!("`{rcvr_ty}` is not an iterator"));
            err.multipart_suggestion_verbose(
                "call `.into_iter()` first",
                vec![(span.shrink_to_lo(), format!("into_iter()."))],
                Applicability::MaybeIncorrect,
            );
            return err.emit();
        } else if !unsatisfied_predicates.is_empty() && matches!(rcvr_ty.kind(), ty::Param(_)) {
            // We special case the situation where we are looking for `_` in
            // `<TypeParam as _>::method` because otherwise the machinery will look for blanket
            // implementations that have unsatisfied trait bounds to suggest, leading us to claim
            // things like "we're looking for a trait with method `cmp`, both `Iterator` and `Ord`
            // have one, in order to implement `Ord` you need to restrict `TypeParam: FnPtr` so
            // that `impl<T: FnPtr> Ord for T` can apply", which is not what we want. We have a type
            // parameter, we want to directly say "`Ord::cmp` and `Iterator::cmp` exist, restrict
            // `TypeParam: Ord` or `TypeParam: Iterator`"". That is done further down when calling
            // `self.suggest_traits_to_import`, so we ignore the `unsatisfied_predicates`
            // suggestions.
        } else if !unsatisfied_predicates.is_empty() {
            let mut type_params = FxIndexMap::default();

            // Pick out the list of unimplemented traits on the receiver.
            // This is used for custom error messages with the `#[rustc_on_unimplemented]` attribute.
            let mut unimplemented_traits = FxIndexMap::default();
            let mut unimplemented_traits_only = true;
            for (predicate, _parent_pred, cause) in unsatisfied_predicates {
                if let (ty::PredicateKind::Clause(ty::ClauseKind::Trait(p)), Some(cause)) =
                    (predicate.kind().skip_binder(), cause.as_ref())
                {
                    if p.trait_ref.self_ty() != rcvr_ty {
                        // This is necessary, not just to keep the errors clean, but also
                        // because our derived obligations can wind up with a trait ref that
                        // requires a different param_env to be correctly compared.
                        continue;
                    }
                    unimplemented_traits.entry(p.trait_ref.def_id).or_insert((
                        predicate.kind().rebind(p.trait_ref),
                        Obligation {
                            cause: cause.clone(),
                            param_env: self.param_env,
                            predicate: *predicate,
                            recursion_depth: 0,
                        },
                    ));
                }
            }

            // Make sure that, if any traits other than the found ones were involved,
            // we don't report an unimplemented trait.
            // We don't want to say that `iter::Cloned` is not an iterator, just
            // because of some non-Clone item being iterated over.
            for (predicate, _parent_pred, _cause) in unsatisfied_predicates {
                match predicate.kind().skip_binder() {
                    ty::PredicateKind::Clause(ty::ClauseKind::Trait(p))
                        if unimplemented_traits.contains_key(&p.trait_ref.def_id) => {}
                    _ => {
                        unimplemented_traits_only = false;
                        break;
                    }
                }
            }

            let mut collect_type_param_suggestions =
                |self_ty: Ty<'tcx>, parent_pred: ty::Predicate<'tcx>, obligation: &str| {
                    // We don't care about regions here, so it's fine to skip the binder here.
                    if let (ty::Param(_), ty::PredicateKind::Clause(ty::ClauseKind::Trait(p))) =
                        (self_ty.kind(), parent_pred.kind().skip_binder())
                    {
                        let node = match p.trait_ref.self_ty().kind() {
                            ty::Param(_) => {
                                // Account for `fn` items like in `issue-35677.rs` to
                                // suggest restricting its type params.
                                Some(self.tcx.hir_node_by_def_id(self.body_id))
                            }
                            ty::Adt(def, _) => def
                                .did()
                                .as_local()
                                .map(|def_id| self.tcx.hir_node_by_def_id(def_id)),
                            _ => None,
                        };
                        if let Some(hir::Node::Item(hir::Item { kind, .. })) = node
                            && let Some(g) = kind.generics()
                        {
                            let key = (
                                g.tail_span_for_predicate_suggestion(),
                                g.add_where_or_trailing_comma(),
                            );
                            type_params
                                .entry(key)
                                .or_insert_with(UnordSet::default)
                                .insert(obligation.to_owned());
                            return true;
                        }
                    }
                    false
                };
            let mut bound_span_label = |self_ty: Ty<'_>, obligation: &str, quiet: &str| {
                let msg = format!("`{}`", if obligation.len() > 50 { quiet } else { obligation });
                match self_ty.kind() {
                    // Point at the type that couldn't satisfy the bound.
                    ty::Adt(def, _) => {
                        bound_spans.get_mut_or_insert_default(tcx.def_span(def.did())).push(msg)
                    }
                    // Point at the trait object that couldn't satisfy the bound.
                    ty::Dynamic(preds, _, _) => {
                        for pred in preds.iter() {
                            match pred.skip_binder() {
                                ty::ExistentialPredicate::Trait(tr) => {
                                    bound_spans
                                        .get_mut_or_insert_default(tcx.def_span(tr.def_id))
                                        .push(msg.clone());
                                }
                                ty::ExistentialPredicate::Projection(_)
                                | ty::ExistentialPredicate::AutoTrait(_) => {}
                            }
                        }
                    }
                    // Point at the closure that couldn't satisfy the bound.
                    ty::Closure(def_id, _) => {
                        bound_spans
                            .get_mut_or_insert_default(tcx.def_span(*def_id))
                            .push(format!("`{quiet}`"));
                    }
                    _ => {}
                }
            };
            let mut format_pred = |pred: ty::Predicate<'tcx>| {
                let bound_predicate = pred.kind();
                match bound_predicate.skip_binder() {
                    ty::PredicateKind::Clause(ty::ClauseKind::Projection(pred)) => {
                        let pred = bound_predicate.rebind(pred);
                        // `<Foo as Iterator>::Item = String`.
                        let projection_term = pred.skip_binder().projection_term;
                        let quiet_projection_term =
                            projection_term.with_self_ty(tcx, Ty::new_var(tcx, ty::TyVid::ZERO));

                        let term = pred.skip_binder().term;

                        let obligation = format!("{projection_term} = {term}");
                        let quiet = with_forced_trimmed_paths!(format!(
                            "{} = {}",
                            quiet_projection_term, term
                        ));

                        bound_span_label(projection_term.self_ty(), &obligation, &quiet);
                        Some((obligation, projection_term.self_ty()))
                    }
                    ty::PredicateKind::Clause(ty::ClauseKind::Trait(poly_trait_ref)) => {
                        let p = poly_trait_ref.trait_ref;
                        let self_ty = p.self_ty();
                        let path = p.print_only_trait_path();
                        let obligation = format!("{self_ty}: {path}");
                        let quiet = with_forced_trimmed_paths!(format!("_: {}", path));
                        bound_span_label(self_ty, &obligation, &quiet);
                        Some((obligation, self_ty))
                    }
                    _ => None,
                }
            };

            // Find all the requirements that come from a local `impl` block.
            let mut skip_list: UnordSet<_> = Default::default();
            let mut spanned_predicates = FxIndexMap::default();
            for (p, parent_p, cause) in unsatisfied_predicates {
                // Extract the predicate span and parent def id of the cause,
                // if we have one.
                let (item_def_id, cause_span) = match cause.as_ref().map(|cause| cause.code()) {
                    Some(ObligationCauseCode::ImplDerived(data)) => {
                        (data.impl_or_alias_def_id, data.span)
                    }
                    Some(
                        ObligationCauseCode::WhereClauseInExpr(def_id, span, _, _)
                        | ObligationCauseCode::WhereClause(def_id, span),
                    ) if !span.is_dummy() => (*def_id, *span),
                    _ => continue,
                };

                // Don't point out the span of `WellFormed` predicates.
                if !matches!(
                    p.kind().skip_binder(),
                    ty::PredicateKind::Clause(
                        ty::ClauseKind::Projection(..) | ty::ClauseKind::Trait(..)
                    )
                ) {
                    continue;
                };

                match self.tcx.hir().get_if_local(item_def_id) {
                    // Unmet obligation comes from a `derive` macro, point at it once to
                    // avoid multiple span labels pointing at the same place.
                    Some(Node::Item(hir::Item {
                        kind: hir::ItemKind::Impl(hir::Impl { of_trait, self_ty, .. }),
                        ..
                    })) if matches!(
                        self_ty.span.ctxt().outer_expn_data().kind,
                        ExpnKind::Macro(MacroKind::Derive, _)
                    ) || matches!(
                        of_trait.as_ref().map(|t| t.path.span.ctxt().outer_expn_data().kind),
                        Some(ExpnKind::Macro(MacroKind::Derive, _))
                    ) =>
                    {
                        let span = self_ty.span.ctxt().outer_expn_data().call_site;
                        let entry = spanned_predicates.entry(span);
                        let entry = entry.or_insert_with(|| {
                            (FxIndexSet::default(), FxIndexSet::default(), Vec::new())
                        });
                        entry.0.insert(span);
                        entry.1.insert((
                            span,
                            "unsatisfied trait bound introduced in this `derive` macro",
                        ));
                        entry.2.push(p);
                        skip_list.insert(p);
                    }

                    // Unmet obligation coming from an `impl`.
                    Some(Node::Item(hir::Item {
                        kind: hir::ItemKind::Impl(hir::Impl { of_trait, self_ty, generics, .. }),
                        span: item_span,
                        ..
                    })) => {
                        let sized_pred =
                            unsatisfied_predicates.iter().any(|(pred, _, _)| {
                                match pred.kind().skip_binder() {
                                    ty::PredicateKind::Clause(ty::ClauseKind::Trait(pred)) => {
                                        self.tcx.is_lang_item(pred.def_id(), LangItem::Sized)
                                            && pred.polarity == ty::PredicatePolarity::Positive
                                    }
                                    _ => false,
                                }
                            });
                        for param in generics.params {
                            if param.span == cause_span && sized_pred {
                                let (sp, sugg) = match param.colon_span {
                                    Some(sp) => (sp.shrink_to_hi(), " ?Sized +"),
                                    None => (param.span.shrink_to_hi(), ": ?Sized"),
                                };
                                err.span_suggestion_verbose(
                                    sp,
                                    "consider relaxing the type parameter's implicit `Sized` bound",
                                    sugg,
                                    Applicability::MachineApplicable,
                                );
                            }
                        }
                        if let Some(pred) = parent_p {
                            // Done to add the "doesn't satisfy" `span_label`.
                            let _ = format_pred(*pred);
                        }
                        skip_list.insert(p);
                        let entry = spanned_predicates.entry(self_ty.span);
                        let entry = entry.or_insert_with(|| {
                            (FxIndexSet::default(), FxIndexSet::default(), Vec::new())
                        });
                        entry.2.push(p);
                        if cause_span != *item_span {
                            entry.0.insert(cause_span);
                            entry.1.insert((cause_span, "unsatisfied trait bound introduced here"));
                        } else {
                            if let Some(trait_ref) = of_trait {
                                entry.0.insert(trait_ref.path.span);
                            }
                            entry.0.insert(self_ty.span);
                        };
                        if let Some(trait_ref) = of_trait {
                            entry.1.insert((trait_ref.path.span, ""));
                        }
                        entry.1.insert((self_ty.span, ""));
                    }
                    Some(Node::Item(hir::Item {
                        kind: hir::ItemKind::Trait(rustc_ast::ast::IsAuto::Yes, ..),
                        span: item_span,
                        ..
                    })) => {
                        self.dcx().span_delayed_bug(
                            *item_span,
                            "auto trait is invoked with no method error, but no error reported?",
                        );
                    }
                    Some(
                        Node::Item(hir::Item {
                            ident,
                            kind: hir::ItemKind::Trait(..) | hir::ItemKind::TraitAlias(..),
                            ..
                        })
                        // We may also encounter unsatisfied GAT or method bounds
                        | Node::TraitItem(hir::TraitItem { ident, .. })
                        | Node::ImplItem(hir::ImplItem { ident, .. }),
                    ) => {
                        skip_list.insert(p);
                        let entry = spanned_predicates.entry(ident.span);
                        let entry = entry.or_insert_with(|| {
                            (FxIndexSet::default(), FxIndexSet::default(), Vec::new())
                        });
                        entry.0.insert(cause_span);
                        entry.1.insert((ident.span, ""));
                        entry.1.insert((cause_span, "unsatisfied trait bound introduced here"));
                        entry.2.push(p);
                    }
                    Some(node) => unreachable!("encountered `{node:?}` due to `{cause:#?}`"),
                    None => (),
                }
            }
            let mut spanned_predicates: Vec<_> = spanned_predicates.into_iter().collect();
            spanned_predicates.sort_by_key(|(span, _)| *span);
            for (_, (primary_spans, span_labels, predicates)) in spanned_predicates {
                let mut preds: Vec<_> = predicates
                    .iter()
                    .filter_map(|pred| format_pred(**pred))
                    .map(|(p, _)| format!("`{p}`"))
                    .collect();
                preds.sort();
                preds.dedup();
                let msg = if let [pred] = &preds[..] {
                    format!("trait bound {pred} was not satisfied")
                } else {
                    format!("the following trait bounds were not satisfied:\n{}", preds.join("\n"),)
                };
                let mut span: MultiSpan = primary_spans.into_iter().collect::<Vec<_>>().into();
                for (sp, label) in span_labels {
                    span.push_span_label(sp, label);
                }
                err.span_note(span, msg);
                unsatisfied_bounds = true;
            }

            let mut suggested_bounds = UnordSet::default();
            // The requirements that didn't have an `impl` span to show.
            let mut bound_list = unsatisfied_predicates
                .iter()
                .filter_map(|(pred, parent_pred, _cause)| {
                    let mut suggested = false;
                    format_pred(*pred).map(|(p, self_ty)| {
                        if let Some(parent) = parent_pred
                            && suggested_bounds.contains(parent)
                        {
                            // We don't suggest `PartialEq` when we already suggest `Eq`.
                        } else if !suggested_bounds.contains(pred)
                            && collect_type_param_suggestions(self_ty, *pred, &p)
                        {
                            suggested = true;
                            suggested_bounds.insert(pred);
                        }
                        (
                            match parent_pred {
                                None => format!("`{p}`"),
                                Some(parent_pred) => match format_pred(*parent_pred) {
                                    None => format!("`{p}`"),
                                    Some((parent_p, _)) => {
                                        if !suggested
                                            && !suggested_bounds.contains(pred)
                                            && !suggested_bounds.contains(parent_pred)
                                            && collect_type_param_suggestions(
                                                self_ty,
                                                *parent_pred,
                                                &p,
                                            )
                                        {
                                            suggested_bounds.insert(pred);
                                        }
                                        format!("`{p}`\nwhich is required by `{parent_p}`")
                                    }
                                },
                            },
                            *pred,
                        )
                    })
                })
                .filter(|(_, pred)| !skip_list.contains(&pred))
                .map(|(t, _)| t)
                .enumerate()
                .collect::<Vec<(usize, String)>>();

            if !matches!(rcvr_ty.peel_refs().kind(), ty::Param(_)) {
                for ((span, add_where_or_comma), obligations) in type_params.into_iter() {
                    restrict_type_params = true;
                    // #74886: Sort here so that the output is always the same.
                    let obligations = obligations.into_sorted_stable_ord();
                    err.span_suggestion_verbose(
                        span,
                        format!(
                            "consider restricting the type parameter{s} to satisfy the trait \
                             bound{s}",
                            s = pluralize!(obligations.len())
                        ),
                        format!("{} {}", add_where_or_comma, obligations.join(", ")),
                        Applicability::MaybeIncorrect,
                    );
                }
            }

            bound_list.sort_by(|(_, a), (_, b)| a.cmp(b)); // Sort alphabetically.
            bound_list.dedup_by(|(_, a), (_, b)| a == b); // #35677
            bound_list.sort_by_key(|(pos, _)| *pos); // Keep the original predicate order.

            if !bound_list.is_empty() || !skip_list.is_empty() {
                let bound_list =
                    bound_list.into_iter().map(|(_, path)| path).collect::<Vec<_>>().join("\n");
                let actual_prefix = rcvr_ty.prefix_string(self.tcx);
                info!("unimplemented_traits.len() == {}", unimplemented_traits.len());
                let mut long_ty_file = None;
                let (primary_message, label, notes) = if unimplemented_traits.len() == 1
                    && unimplemented_traits_only
                {
                    unimplemented_traits
                        .into_iter()
                        .next()
                        .map(|(_, (trait_ref, obligation))| {
                            if trait_ref.self_ty().references_error() || rcvr_ty.references_error()
                            {
                                // Avoid crashing.
                                return (None, None, Vec::new());
                            }
                            let OnUnimplementedNote { message, label, notes, .. } = self
                                .err_ctxt()
                                .on_unimplemented_note(trait_ref, &obligation, &mut long_ty_file);
                            (message, label, notes)
                        })
                        .unwrap()
                } else {
                    (None, None, Vec::new())
                };
                let primary_message = primary_message.unwrap_or_else(|| {
                    format!(
                        "the {item_kind} `{item_name}` exists for {actual_prefix} `{ty_str}`, \
                         but its trait bounds were not satisfied"
                    )
                });
                err.primary_message(primary_message);
                if let Some(file) = long_ty_file {
                    err.note(format!(
                        "the full name for the type has been written to '{}'",
                        file.display(),
                    ));
                    err.note(
                        "consider using `--verbose` to print the full type name to the console",
                    );
                }
                if let Some(label) = label {
                    custom_span_label = true;
                    err.span_label(span, label);
                }
                if !bound_list.is_empty() {
                    err.note(format!(
                        "the following trait bounds were not satisfied:\n{bound_list}"
                    ));
                }
                for note in notes {
                    err.note(note);
                }

                suggested_derive = self.suggest_derive(&mut err, unsatisfied_predicates);

                unsatisfied_bounds = true;
            }
        } else if let ty::Adt(def, targs) = rcvr_ty.kind()
            && let SelfSource::MethodCall(rcvr_expr) = source
        {
            // This is useful for methods on arbitrary self types that might have a simple
            // mutability difference, like calling a method on `Pin<&mut Self>` that is on
            // `Pin<&Self>`.
            if targs.len() == 1 {
                let mut item_segment = hir::PathSegment::invalid();
                item_segment.ident = item_name;
                for t in [Ty::new_mut_ref, Ty::new_imm_ref, |_, _, t| t] {
                    let new_args =
                        tcx.mk_args_from_iter(targs.iter().map(|arg| match arg.as_type() {
                            Some(ty) => ty::GenericArg::from(t(
                                tcx,
                                tcx.lifetimes.re_erased,
                                ty.peel_refs(),
                            )),
                            _ => arg,
                        }));
                    let rcvr_ty = Ty::new_adt(tcx, *def, new_args);
                    if let Ok(method) = self.lookup_method_for_diagnostic(
                        rcvr_ty,
                        &item_segment,
                        span,
                        tcx.parent_hir_node(rcvr_expr.hir_id).expect_expr(),
                        rcvr_expr,
                    ) {
                        err.span_note(
                            tcx.def_span(method.def_id),
                            format!("{item_kind} is available for `{rcvr_ty}`"),
                        );
                    }
                }
            }
        }

        let mut find_candidate_for_method = false;

        let mut label_span_not_found = |err: &mut Diag<'_>| {
            if unsatisfied_predicates.is_empty() {
                err.span_label(span, format!("{item_kind} not found in `{ty_str}`"));
                let is_string_or_ref_str = match rcvr_ty.kind() {
                    ty::Ref(_, ty, _) => {
                        ty.is_str()
                            || matches!(
                                ty.kind(),
                                ty::Adt(adt, _) if self.tcx.is_lang_item(adt.did(), LangItem::String)
                            )
                    }
                    ty::Adt(adt, _) => self.tcx.is_lang_item(adt.did(), LangItem::String),
                    _ => false,
                };
                if is_string_or_ref_str && item_name.name == sym::iter {
                    err.span_suggestion_verbose(
                        item_name.span,
                        "because of the in-memory representation of `&str`, to obtain \
                         an `Iterator` over each of its codepoint use method `chars`",
                        "chars",
                        Applicability::MachineApplicable,
                    );
                }
                if let ty::Adt(adt, _) = rcvr_ty.kind() {
                    let mut inherent_impls_candidate = self
                        .tcx
                        .inherent_impls(adt.did())
                        .into_iter()
                        .flatten()
                        .copied()
                        .filter(|def_id| {
                            if let Some(assoc) = self.associated_value(*def_id, item_name) {
                                // Check for both mode is the same so we avoid suggesting
                                // incorrect associated item.
                                match (mode, assoc.fn_has_self_parameter, source) {
                                    (Mode::MethodCall, true, SelfSource::MethodCall(_)) => {
                                        // We check that the suggest type is actually
                                        // different from the received one
                                        // So we avoid suggestion method with Box<Self>
                                        // for instance
                                        self.tcx.at(span).type_of(*def_id).instantiate_identity()
                                            != rcvr_ty
                                    }
                                    (Mode::Path, false, _) => true,
                                    _ => false,
                                }
                            } else {
                                false
                            }
                        })
                        .collect::<Vec<_>>();
                    if !inherent_impls_candidate.is_empty() {
                        inherent_impls_candidate.sort_by_key(|id| self.tcx.def_path_str(id));
                        inherent_impls_candidate.dedup();

                        // number of types to show at most
                        let limit = if inherent_impls_candidate.len() == 5 { 5 } else { 4 };
                        let type_candidates = inherent_impls_candidate
                            .iter()
                            .take(limit)
                            .map(|impl_item| {
                                format!(
                                    "- `{}`",
                                    self.tcx.at(span).type_of(*impl_item).instantiate_identity()
                                )
                            })
                            .collect::<Vec<_>>()
                            .join("\n");
                        let additional_types = if inherent_impls_candidate.len() > limit {
                            format!("\nand {} more types", inherent_impls_candidate.len() - limit)
                        } else {
                            "".to_string()
                        };
                        err.note(format!(
                            "the {item_kind} was found for\n{type_candidates}{additional_types}"
                        ));
                        find_candidate_for_method = mode == Mode::MethodCall;
                    }
                }
            } else {
                let ty_str =
                    if ty_str.len() > 50 { String::new() } else { format!("on `{ty_str}` ") };
                err.span_label(
                    span,
                    format!("{item_kind} cannot be called {ty_str}due to unsatisfied trait bounds"),
                );
            }
        };

        // If the method name is the name of a field with a function or closure type,
        // give a helping note that it has to be called as `(x.f)(...)`.
        if let SelfSource::MethodCall(expr) = source {
            if !self.suggest_calling_field_as_fn(span, rcvr_ty, expr, item_name, &mut err)
                && similar_candidate.is_none()
                && !custom_span_label
            {
                label_span_not_found(&mut err);
            }
        } else if !custom_span_label {
            label_span_not_found(&mut err);
        }

        let confusable_suggested = self.confusable_method_name(
            &mut err,
            rcvr_ty,
            item_name,
            args.map(|args| {
                args.iter()
                    .map(|expr| {
                        self.node_ty_opt(expr.hir_id).unwrap_or_else(|| self.next_ty_var(expr.span))
                    })
                    .collect()
            }),
        );

        // Don't suggest (for example) `expr.field.clone()` if `expr.clone()`
        // can't be called due to `typeof(expr): Clone` not holding.
        if unsatisfied_predicates.is_empty() {
            self.suggest_calling_method_on_field(
                &mut err,
                source,
                span,
                rcvr_ty,
                item_name,
                expected.only_has_type(self),
            );
        }

        self.suggest_unwrapping_inner_self(&mut err, source, rcvr_ty, item_name);

        for (span, mut bounds) in bound_spans {
            if !tcx.sess.source_map().is_span_accessible(span) {
                continue;
            }
            bounds.sort();
            bounds.dedup();
            let pre = if Some(span) == ty_span {
                ty_span.take();
                format!(
                    "{item_kind} `{item_name}` not found for this {} because it ",
                    rcvr_ty.prefix_string(self.tcx)
                )
            } else {
                String::new()
            };
            let msg = match &bounds[..] {
                [bound] => format!("{pre}doesn't satisfy {bound}"),
                bounds if bounds.len() > 4 => format!("doesn't satisfy {} bounds", bounds.len()),
                [bounds @ .., last] => {
                    format!("{pre}doesn't satisfy {} or {last}", bounds.join(", "))
                }
                [] => unreachable!(),
            };
            err.span_label(span, msg);
        }
        if let Some(span) = ty_span {
            err.span_label(
                span,
                format!(
                    "{item_kind} `{item_name}` not found for this {}",
                    rcvr_ty.prefix_string(self.tcx)
                ),
            );
        }

        if rcvr_ty.is_numeric() && rcvr_ty.is_fresh() || restrict_type_params || suggested_derive {
        } else {
            self.suggest_traits_to_import(
                &mut err,
                span,
                rcvr_ty,
                item_name,
                args.map(|args| args.len() + 1),
                source,
                no_match_data.out_of_scope_traits.clone(),
                static_candidates,
                unsatisfied_bounds,
                expected.only_has_type(self),
                trait_missing_method,
            );
        }

        // Don't emit a suggestion if we found an actual method
        // that had unsatisfied trait bounds
        if unsatisfied_predicates.is_empty() && rcvr_ty.is_enum() {
            let adt_def = rcvr_ty.ty_adt_def().expect("enum is not an ADT");
            if let Some(var_name) = edit_distance::find_best_match_for_name(
                &adt_def.variants().iter().map(|s| s.name).collect::<Vec<_>>(),
                item_name.name,
                None,
            ) && let Some(variant) = adt_def.variants().iter().find(|s| s.name == var_name)
            {
                let mut suggestion = vec![(span, var_name.to_string())];
                if let SelfSource::QPath(ty) = source
                    && let hir::Node::Expr(ref path_expr) = self.tcx.parent_hir_node(ty.hir_id)
                    && let hir::ExprKind::Path(_) = path_expr.kind
                    && let hir::Node::Stmt(hir::Stmt {
                        kind: hir::StmtKind::Semi(ref parent), ..
                    })
                    | hir::Node::Expr(ref parent) = self.tcx.parent_hir_node(path_expr.hir_id)
                {
                    let replacement_span =
                        if let hir::ExprKind::Call(..) | hir::ExprKind::Struct(..) = parent.kind {
                            // We want to replace the parts that need to go, like `()` and `{}`.
                            span.with_hi(parent.span.hi())
                        } else {
                            span
                        };
                    match (variant.ctor, parent.kind) {
                        (None, hir::ExprKind::Struct(..)) => {
                            // We want a struct and we have a struct. We won't suggest changing
                            // the fields (at least for now).
                            suggestion = vec![(span, var_name.to_string())];
                        }
                        (None, _) => {
                            // struct
                            suggestion = vec![(
                                replacement_span,
                                if variant.fields.is_empty() {
                                    format!("{var_name} {{}}")
                                } else {
                                    format!(
                                        "{var_name} {{ {} }}",
                                        variant
                                            .fields
                                            .iter()
                                            .map(|f| format!("{}: /* value */", f.name))
                                            .collect::<Vec<_>>()
                                            .join(", ")
                                    )
                                },
                            )];
                        }
                        (Some((hir::def::CtorKind::Const, _)), _) => {
                            // unit, remove the `()`.
                            suggestion = vec![(replacement_span, var_name.to_string())];
                        }
                        (
                            Some((hir::def::CtorKind::Fn, def_id)),
                            hir::ExprKind::Call(rcvr, args),
                        ) => {
                            let fn_sig = self.tcx.fn_sig(def_id).instantiate_identity();
                            let inputs = fn_sig.inputs().skip_binder();
                            // FIXME: reuse the logic for "change args" suggestion to account for types
                            // involved and detect things like substitution.
                            match (inputs, args) {
                                (inputs, []) => {
                                    // Add arguments.
                                    suggestion.push((
                                        rcvr.span.shrink_to_hi().with_hi(parent.span.hi()),
                                        format!(
                                            "({})",
                                            inputs
                                                .iter()
                                                .map(|i| format!("/* {i} */"))
                                                .collect::<Vec<String>>()
                                                .join(", ")
                                        ),
                                    ));
                                }
                                (_, [arg]) if inputs.len() != args.len() => {
                                    // Replace arguments.
                                    suggestion.push((
                                        arg.span,
                                        inputs
                                            .iter()
                                            .map(|i| format!("/* {i} */"))
                                            .collect::<Vec<String>>()
                                            .join(", "),
                                    ));
                                }
                                (_, [arg_start, .., arg_end]) if inputs.len() != args.len() => {
                                    // Replace arguments.
                                    suggestion.push((
                                        arg_start.span.to(arg_end.span),
                                        inputs
                                            .iter()
                                            .map(|i| format!("/* {i} */"))
                                            .collect::<Vec<String>>()
                                            .join(", "),
                                    ));
                                }
                                // Argument count is the same, keep as is.
                                _ => {}
                            }
                        }
                        (Some((hir::def::CtorKind::Fn, def_id)), _) => {
                            let fn_sig = self.tcx.fn_sig(def_id).instantiate_identity();
                            let inputs = fn_sig.inputs().skip_binder();
                            suggestion = vec![(
                                replacement_span,
                                format!(
                                    "{var_name}({})",
                                    inputs
                                        .iter()
                                        .map(|i| format!("/* {i} */"))
                                        .collect::<Vec<String>>()
                                        .join(", ")
                                ),
                            )];
                        }
                    }
                }
                err.multipart_suggestion_verbose(
                    "there is a variant with a similar name",
                    suggestion,
                    Applicability::HasPlaceholders,
                );
            }
        }

        if item_name.name == sym::as_str && rcvr_ty.peel_refs().is_str() {
            let msg = "remove this method call";
            let mut fallback_span = true;
            if let SelfSource::MethodCall(expr) = source {
                let call_expr = self.tcx.hir().expect_expr(self.tcx.parent_hir_id(expr.hir_id));
                if let Some(span) = call_expr.span.trim_start(expr.span) {
                    err.span_suggestion(span, msg, "", Applicability::MachineApplicable);
                    fallback_span = false;
                }
            }
            if fallback_span {
                err.span_label(span, msg);
            }
        } else if let Some(similar_candidate) = similar_candidate {
            // Don't emit a suggestion if we found an actual method
            // that had unsatisfied trait bounds
            if unsatisfied_predicates.is_empty()
                // ...or if we already suggested that name because of `rustc_confusable` annotation.
                && Some(similar_candidate.name) != confusable_suggested
            {
                self.find_likely_intended_associated_item(
                    &mut err,
                    similar_candidate,
                    span,
                    args,
                    mode,
                );
            }
        }

        if !find_candidate_for_method {
            self.lookup_segments_chain_for_no_match_method(
                &mut err,
                item_name,
                item_kind,
                source,
                no_match_data,
            );
        }

        self.note_derefed_ty_has_method(&mut err, source, rcvr_ty, item_name, expected);
        err.emit()
    }
}

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    /// If an appropriate error source is not found, check method chain for possible candidates
    pub(super) fn lookup_segments_chain_for_no_match_method(
        &self,
        err: &mut Diag<'_>,
        item_name: Ident,
        item_kind: &str,
        source: SelfSource<'tcx>,
        no_match_data: &NoMatchData<'tcx>,
    ) {
        if no_match_data.unsatisfied_predicates.is_empty()
            && let Mode::MethodCall = no_match_data.mode
            && let SelfSource::MethodCall(mut source_expr) = source
        {
            let mut stack_methods = vec![];
            while let hir::ExprKind::MethodCall(_path_segment, rcvr_expr, _args, method_span) =
                source_expr.kind
            {
                // Pop the matching receiver, to align on it's notional span
                if let Some(prev_match) = stack_methods.pop() {
                    err.span_label(
                        method_span,
                        format!("{item_kind} `{item_name}` is available on `{prev_match}`"),
                    );
                }
                let rcvr_ty = self.resolve_vars_if_possible(
                    self.typeck_results
                        .borrow()
                        .expr_ty_adjusted_opt(rcvr_expr)
                        .unwrap_or(Ty::new_misc_error(self.tcx)),
                );

                let Ok(candidates) = self.probe_for_name_many(
                    Mode::MethodCall,
                    item_name,
                    None,
                    IsSuggestion(true),
                    rcvr_ty,
                    source_expr.hir_id,
                    ProbeScope::TraitsInScope,
                ) else {
                    return;
                };

                // FIXME: `probe_for_name_many` searches for methods in inherent implementations,
                // so it may return a candidate that doesn't belong to this `revr_ty`. We need to
                // check whether the instantiated type matches the received one.
                for _matched_method in candidates {
                    // found a match, push to stack
                    stack_methods.push(rcvr_ty);
                }
                source_expr = rcvr_expr;
            }
            // If there is a match at the start of the chain, add a label for it too!
            if let Some(prev_match) = stack_methods.pop() {
                err.span_label(
                    source_expr.span,
                    format!("{item_kind} `{item_name}` is available on `{prev_match}`"),
                );
            }
        }
    }
}
