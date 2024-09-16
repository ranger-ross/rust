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
    pub(super) fn find_likely_intended_associated_item(
        &self,
        err: &mut Diag<'_>,
        similar_candidate: ty::AssocItem,
        span: Span,
        args: Option<&'tcx [hir::Expr<'tcx>]>,
        mode: Mode,
    ) {
        let tcx = self.tcx;
        let def_kind = similar_candidate.kind.as_def_kind();
        let an = self.tcx.def_kind_descr_article(def_kind, similar_candidate.def_id);
        let msg = format!(
            "there is {an} {} `{}` with a similar name",
            self.tcx.def_kind_descr(def_kind, similar_candidate.def_id),
            similar_candidate.name,
        );
        // Methods are defined within the context of a struct and their first parameter
        // is always `self`, which represents the instance of the struct the method is
        // being called on Associated functions don’t take self as a parameter and they are
        // not methods because they don’t have an instance of the struct to work with.
        if def_kind == DefKind::AssocFn {
            let ty_args = self.infcx.fresh_args_for_item(span, similar_candidate.def_id);
            let fn_sig = tcx.fn_sig(similar_candidate.def_id).instantiate(tcx, ty_args);
            let fn_sig = self.instantiate_binder_with_fresh_vars(span, infer::FnCall, fn_sig);
            if similar_candidate.fn_has_self_parameter {
                if let Some(args) = args
                    && fn_sig.inputs()[1..].len() == args.len()
                {
                    // We found a method with the same number of arguments as the method
                    // call expression the user wrote.
                    err.span_suggestion_verbose(
                        span,
                        msg,
                        similar_candidate.name,
                        Applicability::MaybeIncorrect,
                    );
                } else {
                    // We found a method but either the expression is not a method call or
                    // the argument count didn't match.
                    err.span_help(
                        tcx.def_span(similar_candidate.def_id),
                        format!(
                            "{msg}{}",
                            if let None = args { "" } else { ", but with different arguments" },
                        ),
                    );
                }
            } else if let Some(args) = args
                && fn_sig.inputs().len() == args.len()
            {
                // We have fn call expression and the argument count match the associated
                // function we found.
                err.span_suggestion_verbose(
                    span,
                    msg,
                    similar_candidate.name,
                    Applicability::MaybeIncorrect,
                );
            } else {
                err.span_help(tcx.def_span(similar_candidate.def_id), msg);
            }
        } else if let Mode::Path = mode
            && args.unwrap_or(&[]).is_empty()
        {
            // We have an associated item syntax and we found something that isn't an fn.
            err.span_suggestion_verbose(
                span,
                msg,
                similar_candidate.name,
                Applicability::MaybeIncorrect,
            );
        } else {
            // The expression is a function or method call, but the item we found is an
            // associated const or type.
            err.span_help(tcx.def_span(similar_candidate.def_id), msg);
        }
    }

    /// Suggest calling `Ty::method` if `.method()` isn't found because the method
    /// doesn't take a `self` receiver.
    pub(super) fn suggest_associated_call_syntax(
        &self,
        err: &mut Diag<'_>,
        static_candidates: &Vec<CandidateSource>,
        rcvr_ty: Ty<'tcx>,
        source: SelfSource<'tcx>,
        item_name: Ident,
        args: Option<&'tcx [hir::Expr<'tcx>]>,
        sugg_span: Span,
    ) {
        let mut has_unsuggestable_args = false;
        let ty_str = if let Some(CandidateSource::Impl(impl_did)) = static_candidates.get(0) {
            // When the "method" is resolved through dereferencing, we really want the
            // original type that has the associated function for accurate suggestions.
            // (#61411)
            let impl_ty = self.tcx.type_of(*impl_did).instantiate_identity();
            let target_ty = self
                .autoderef(sugg_span, rcvr_ty)
                .find(|(rcvr_ty, _)| {
                    DeepRejectCtxt::relate_rigid_infer(self.tcx).types_may_unify(*rcvr_ty, impl_ty)
                })
                .map_or(impl_ty, |(ty, _)| ty)
                .peel_refs();
            if let ty::Adt(def, args) = target_ty.kind() {
                // If there are any inferred arguments, (`{integer}`), we should replace
                // them with underscores to allow the compiler to infer them
                let infer_args = self.tcx.mk_args_from_iter(args.into_iter().map(|arg| {
                    if !arg.is_suggestable(self.tcx, true) {
                        has_unsuggestable_args = true;
                        match arg.unpack() {
                            GenericArgKind::Lifetime(_) => self
                                .next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP))
                                .into(),
                            GenericArgKind::Type(_) => self.next_ty_var(DUMMY_SP).into(),
                            GenericArgKind::Const(_) => self.next_const_var(DUMMY_SP).into(),
                        }
                    } else {
                        arg
                    }
                }));

                self.tcx.value_path_str_with_args(def.did(), infer_args)
            } else {
                self.ty_to_value_string(target_ty)
            }
        } else {
            self.ty_to_value_string(rcvr_ty.peel_refs())
        };
        if let SelfSource::MethodCall(_) = source {
            let first_arg = static_candidates.get(0).and_then(|candidate_source| {
                let (assoc_did, self_ty) = match candidate_source {
                    CandidateSource::Impl(impl_did) => {
                        (*impl_did, self.tcx.type_of(*impl_did).instantiate_identity())
                    }
                    CandidateSource::Trait(trait_did) => (*trait_did, rcvr_ty),
                };

                let assoc = self.associated_value(assoc_did, item_name)?;
                if assoc.kind != ty::AssocKind::Fn {
                    return None;
                }

                // for CandidateSource::Impl, `Self` will be instantiated to a concrete type
                // but for CandidateSource::Trait, `Self` is still `Self`
                let sig = self.tcx.fn_sig(assoc.def_id).instantiate_identity();
                sig.inputs().skip_binder().get(0).and_then(|first| {
                    // if the type of first arg is the same as the current impl type, we should take the first arg into assoc function
                    let first_ty = first.peel_refs();
                    if first_ty == self_ty || first_ty == self.tcx.types.self_param {
                        Some(first.ref_mutability().map_or("", |mutbl| mutbl.ref_prefix_str()))
                    } else {
                        None
                    }
                })
            });

            let mut applicability = Applicability::MachineApplicable;
            let args = if let SelfSource::MethodCall(receiver) = source
                && let Some(args) = args
            {
                // The first arg is the same kind as the receiver
                let explicit_args = if first_arg.is_some() {
                    std::iter::once(receiver).chain(args.iter()).collect::<Vec<_>>()
                } else {
                    // There is no `Self` kind to infer the arguments from
                    if has_unsuggestable_args {
                        applicability = Applicability::HasPlaceholders;
                    }
                    args.iter().collect()
                };
                format!(
                    "({}{})",
                    first_arg.unwrap_or(""),
                    explicit_args
                        .iter()
                        .map(|arg| self
                            .tcx
                            .sess
                            .source_map()
                            .span_to_snippet(arg.span)
                            .unwrap_or_else(|_| {
                                applicability = Applicability::HasPlaceholders;
                                "_".to_owned()
                            }))
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            } else {
                applicability = Applicability::HasPlaceholders;
                "(...)".to_owned()
            };
            err.span_suggestion(
                sugg_span,
                "use associated function syntax instead",
                format!("{ty_str}::{item_name}{args}"),
                applicability,
            );
        } else {
            err.help(format!("try with `{ty_str}::{item_name}`",));
        }
    }

    /// Suggest calling a field with a type that implements the `Fn*` traits instead of a method with
    /// the same name as the field i.e. `(a.my_fn_ptr)(10)` instead of `a.my_fn_ptr(10)`.
    pub(super) fn suggest_calling_field_as_fn(
        &self,
        span: Span,
        rcvr_ty: Ty<'tcx>,
        expr: &hir::Expr<'_>,
        item_name: Ident,
        err: &mut Diag<'_>,
    ) -> bool {
        let tcx = self.tcx;
        let field_receiver = self.autoderef(span, rcvr_ty).find_map(|(ty, _)| match ty.kind() {
            ty::Adt(def, args) if !def.is_enum() => {
                let variant = &def.non_enum_variant();
                tcx.find_field_index(item_name, variant).map(|index| {
                    let field = &variant.fields[index];
                    let field_ty = field.ty(tcx, args);
                    (field, field_ty)
                })
            }
            _ => None,
        });
        if let Some((field, field_ty)) = field_receiver {
            let scope = tcx.parent_module_from_def_id(self.body_id);
            let is_accessible = field.vis.is_accessible_from(scope, tcx);

            if is_accessible {
                if self.is_fn_ty(field_ty, span) {
                    let expr_span = expr.span.to(item_name.span);
                    err.multipart_suggestion(
                        format!(
                            "to call the function stored in `{item_name}`, \
                                         surround the field access with parentheses",
                        ),
                        vec![
                            (expr_span.shrink_to_lo(), '('.to_string()),
                            (expr_span.shrink_to_hi(), ')'.to_string()),
                        ],
                        Applicability::MachineApplicable,
                    );
                } else {
                    let call_expr = tcx.hir().expect_expr(tcx.parent_hir_id(expr.hir_id));

                    if let Some(span) = call_expr.span.trim_start(item_name.span) {
                        err.span_suggestion(
                            span,
                            "remove the arguments",
                            "",
                            Applicability::MaybeIncorrect,
                        );
                    }
                }
            }

            let field_kind = if is_accessible { "field" } else { "private field" };
            err.span_label(item_name.span, format!("{field_kind}, not a method"));
            return true;
        }
        false
    }

    /// For code `rect::area(...)`,
    /// if `rect` is a local variable and `area` is a valid assoc method for it,
    /// we try to suggest `rect.area()`
    pub(crate) fn suggest_assoc_method_call(&self, segs: &[PathSegment<'_>]) {
        debug!("suggest_assoc_method_call segs: {:?}", segs);
        let [seg1, seg2] = segs else {
            return;
        };
        self.dcx().try_steal_modify_and_emit_err(
            seg1.ident.span,
            StashKey::CallAssocMethod,
            |err| {
                let body = self.tcx.hir().body_owned_by(self.body_id);
                struct LetVisitor {
                    ident_name: Symbol,
                }

                // FIXME: This really should be taking scoping, etc into account.
                impl<'v> Visitor<'v> for LetVisitor {
                    type Result = ControlFlow<Option<&'v hir::Expr<'v>>>;
                    fn visit_stmt(&mut self, ex: &'v hir::Stmt<'v>) -> Self::Result {
                        if let hir::StmtKind::Let(&hir::LetStmt { pat, init, .. }) = ex.kind
                            && let hir::PatKind::Binding(_, _, ident, ..) = pat.kind
                            && ident.name == self.ident_name
                        {
                            ControlFlow::Break(init)
                        } else {
                            hir::intravisit::walk_stmt(self, ex)
                        }
                    }
                }

                if let Node::Expr(call_expr) = self.tcx.parent_hir_node(seg1.hir_id)
                    && let ControlFlow::Break(Some(expr)) =
                        (LetVisitor { ident_name: seg1.ident.name }).visit_body(&body)
                    && let Some(self_ty) = self.node_ty_opt(expr.hir_id)
                {
                    let probe = self.lookup_probe_for_diagnostic(
                        seg2.ident,
                        self_ty,
                        call_expr,
                        ProbeScope::TraitsInScope,
                        None,
                    );
                    if probe.is_ok() {
                        let sm = self.infcx.tcx.sess.source_map();
                        err.span_suggestion_verbose(
                            sm.span_extend_while(seg1.ident.span.shrink_to_hi(), |c| c == ':')
                                .unwrap(),
                            "you may have meant to call an instance method",
                            ".",
                            Applicability::MaybeIncorrect,
                        );
                    }
                }
            },
        );
    }

    /// Suggest calling a method on a field i.e. `a.field.bar()` instead of `a.bar()`
    pub(super) fn suggest_calling_method_on_field(
        &self,
        err: &mut Diag<'_>,
        source: SelfSource<'tcx>,
        span: Span,
        actual: Ty<'tcx>,
        item_name: Ident,
        return_type: Option<Ty<'tcx>>,
    ) {
        if let SelfSource::MethodCall(expr) = source {
            let mod_id = self.tcx.parent_module(expr.hir_id).to_def_id();
            for (fields, args) in
                self.get_field_candidates_considering_privacy(span, actual, mod_id, expr.hir_id)
            {
                let call_expr = self.tcx.hir().expect_expr(self.tcx.parent_hir_id(expr.hir_id));

                let lang_items = self.tcx.lang_items();
                let never_mention_traits = [
                    lang_items.clone_trait(),
                    lang_items.deref_trait(),
                    lang_items.deref_mut_trait(),
                    self.tcx.get_diagnostic_item(sym::AsRef),
                    self.tcx.get_diagnostic_item(sym::AsMut),
                    self.tcx.get_diagnostic_item(sym::Borrow),
                    self.tcx.get_diagnostic_item(sym::BorrowMut),
                ];
                let mut candidate_fields: Vec<_> = fields
                    .into_iter()
                    .filter_map(|candidate_field| {
                        self.check_for_nested_field_satisfying(
                            span,
                            &|_, field_ty| {
                                self.lookup_probe_for_diagnostic(
                                    item_name,
                                    field_ty,
                                    call_expr,
                                    ProbeScope::TraitsInScope,
                                    return_type,
                                )
                                .is_ok_and(|pick| {
                                    !never_mention_traits
                                        .iter()
                                        .flatten()
                                        .any(|def_id| self.tcx.parent(pick.item.def_id) == *def_id)
                                })
                            },
                            candidate_field,
                            args,
                            vec![],
                            mod_id,
                            expr.hir_id,
                        )
                    })
                    .map(|field_path| {
                        field_path
                            .iter()
                            .map(|id| id.name.to_ident_string())
                            .collect::<Vec<String>>()
                            .join(".")
                    })
                    .collect();
                candidate_fields.sort();

                let len = candidate_fields.len();
                if len > 0 {
                    err.span_suggestions(
                        item_name.span.shrink_to_lo(),
                        format!(
                            "{} of the expressions' fields {} a method of the same name",
                            if len > 1 { "some" } else { "one" },
                            if len > 1 { "have" } else { "has" },
                        ),
                        candidate_fields.iter().map(|path| format!("{path}.")),
                        Applicability::MaybeIncorrect,
                    );
                }
            }
        }
    }
}
