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
use tracing::{debug, info, instrument};

use crate::errors::{self, CandidateTraitNote, NoAssociatedItem};
use crate::method::probe::{AutorefOrPtrAdjustment, IsSuggestion, Mode, ProbeScope};
use crate::method::suggest::no_match::SuggestNoMatchMethodError;
use crate::method::{CandidateSource, MethodError, NoMatchData};
use crate::{Expectation, FnCtxt};

mod call;
pub(crate) mod derive;
mod misc;
mod no_match;
mod note;
pub(crate) mod traits;

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    #[instrument(level = "debug", skip(self))]
    pub fn report_method_error(
        &self,
        call_id: HirId,
        rcvr_ty: Ty<'tcx>,
        error: MethodError<'tcx>,
        expected: Expectation<'tcx>,
        trait_missing_method: bool,
    ) -> ErrorGuaranteed {
        let (span, sugg_span, source, item_name, args) = match self.tcx.hir_node(call_id) {
            hir::Node::Expr(&hir::Expr {
                kind: hir::ExprKind::MethodCall(segment, rcvr, args, _),
                span,
                ..
            }) => {
                (segment.ident.span, span, SelfSource::MethodCall(rcvr), segment.ident, Some(args))
            }
            hir::Node::Expr(&hir::Expr {
                kind: hir::ExprKind::Path(QPath::TypeRelative(rcvr, segment)),
                span,
                ..
            })
            | hir::Node::Pat(&hir::Pat {
                kind:
                    hir::PatKind::Path(QPath::TypeRelative(rcvr, segment))
                    | hir::PatKind::Struct(QPath::TypeRelative(rcvr, segment), ..)
                    | hir::PatKind::TupleStruct(QPath::TypeRelative(rcvr, segment), ..),
                span,
                ..
            }) => {
                let args = match self.tcx.parent_hir_node(call_id) {
                    hir::Node::Expr(&hir::Expr {
                        kind: hir::ExprKind::Call(callee, args), ..
                    }) if callee.hir_id == call_id => Some(args),
                    _ => None,
                };
                (segment.ident.span, span, SelfSource::QPath(rcvr), segment.ident, args)
            }
            node => unreachable!("{node:?}"),
        };

        // Avoid suggestions when we don't know what's going on.
        if let Err(guar) = rcvr_ty.error_reported() {
            return guar;
        }

        match error {
            MethodError::NoMatch(mut no_match_data) => {
                return self.report_no_match_method_error(
                    span,
                    rcvr_ty,
                    item_name,
                    call_id,
                    source,
                    args,
                    sugg_span,
                    &mut no_match_data,
                    expected,
                    trait_missing_method,
                );
            }

            MethodError::Ambiguity(mut sources) => {
                let mut err = struct_span_code_err!(
                    self.dcx(),
                    item_name.span,
                    E0034,
                    "multiple applicable items in scope"
                );
                err.span_label(item_name.span, format!("multiple `{item_name}` found"));

                self.note_candidates_on_method_error(
                    rcvr_ty,
                    item_name,
                    source,
                    args,
                    span,
                    &mut err,
                    &mut sources,
                    Some(sugg_span),
                );
                return err.emit();
            }

            MethodError::PrivateMatch(kind, def_id, out_of_scope_traits) => {
                let kind = self.tcx.def_kind_descr(kind, def_id);
                let mut err = struct_span_code_err!(
                    self.dcx(),
                    item_name.span,
                    E0624,
                    "{} `{}` is private",
                    kind,
                    item_name
                );
                err.span_label(item_name.span, format!("private {kind}"));
                let sp = self
                    .tcx
                    .hir()
                    .span_if_local(def_id)
                    .unwrap_or_else(|| self.tcx.def_span(def_id));
                err.span_label(sp, format!("private {kind} defined here"));
                self.suggest_valid_traits(&mut err, item_name, out_of_scope_traits, true);

                return err.emit();
            }

            MethodError::IllegalSizedBound { candidates, needs_mut, bound_span, self_expr } => {
                let msg = if needs_mut {
                    with_forced_trimmed_paths!(format!(
                        "the `{item_name}` method cannot be invoked on `{rcvr_ty}`"
                    ))
                } else {
                    format!("the `{item_name}` method cannot be invoked on a trait object")
                };
                let mut err = self.dcx().struct_span_err(span, msg);
                if !needs_mut {
                    err.span_label(bound_span, "this has a `Sized` requirement");
                }
                if !candidates.is_empty() {
                    let help = format!(
                        "{an}other candidate{s} {were} found in the following trait{s}",
                        an = if candidates.len() == 1 { "an" } else { "" },
                        s = pluralize!(candidates.len()),
                        were = pluralize!("was", candidates.len()),
                    );
                    self.suggest_use_candidates(
                        candidates,
                        |accessible_sugg, inaccessible_sugg, span| {
                            let suggest_for_access =
                                |err: &mut Diag<'_>, mut msg: String, sugg: Vec<_>| {
                                    msg += &format!(
                                        ", perhaps add a `use` for {one_of_them}:",
                                        one_of_them =
                                            if sugg.len() == 1 { "it" } else { "one_of_them" },
                                    );
                                    err.span_suggestions(
                                        span,
                                        msg,
                                        sugg,
                                        Applicability::MaybeIncorrect,
                                    );
                                };
                            let suggest_for_privacy =
                                |err: &mut Diag<'_>, mut msg: String, suggs: Vec<String>| {
                                    if let [sugg] = suggs.as_slice() {
                                        err.help(format!("\
                                            trait `{}` provides `{item_name}` is implemented but not reachable",
                                            sugg.trim(),
                                        ));
                                    } else {
                                        msg += &format!(" but {} not reachable", pluralize!("is", suggs.len()));
                                        err.span_suggestions(
                                            span,
                                            msg,
                                            suggs,
                                            Applicability::MaybeIncorrect,
                                        );
                                    }
                                };
                            if accessible_sugg.is_empty() {
                                // `inaccessible_sugg` must not be empty
                                suggest_for_privacy(&mut err, help, inaccessible_sugg);
                            } else if inaccessible_sugg.is_empty() {
                                suggest_for_access(&mut err, help, accessible_sugg);
                            } else {
                                suggest_for_access(&mut err, help.clone(), accessible_sugg);
                                suggest_for_privacy(&mut err, help, inaccessible_sugg);
                            }
                        },
                    );
                }
                if let ty::Ref(region, t_type, mutability) = rcvr_ty.kind() {
                    if needs_mut {
                        let trait_type =
                            Ty::new_ref(self.tcx, *region, *t_type, mutability.invert());
                        let msg = format!("you need `{trait_type}` instead of `{rcvr_ty}`");
                        let mut kind = &self_expr.kind;
                        while let hir::ExprKind::AddrOf(_, _, expr)
                        | hir::ExprKind::Unary(hir::UnOp::Deref, expr) = kind
                        {
                            kind = &expr.kind;
                        }
                        if let hir::ExprKind::Path(hir::QPath::Resolved(None, path)) = kind
                            && let hir::def::Res::Local(hir_id) = path.res
                            && let hir::Node::Pat(b) = self.tcx.hir_node(hir_id)
                            && let hir::Node::Param(p) = self.tcx.parent_hir_node(b.hir_id)
                            && let Some(decl) = self.tcx.parent_hir_node(p.hir_id).fn_decl()
                            && let Some(ty) = decl.inputs.iter().find(|ty| ty.span == p.ty_span)
                            && let hir::TyKind::Ref(_, mut_ty) = &ty.kind
                            && let hir::Mutability::Not = mut_ty.mutbl
                        {
                            err.span_suggestion_verbose(
                                mut_ty.ty.span.shrink_to_lo(),
                                msg,
                                "mut ",
                                Applicability::MachineApplicable,
                            );
                        } else {
                            err.help(msg);
                        }
                    }
                }
                return err.emit();
            }

            MethodError::BadReturnType => bug!("no return type expectations but got BadReturnType"),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum SelfSource<'a> {
    QPath(&'a hir::Ty<'a>),
    MethodCall(&'a hir::Expr<'a> /* rcvr */),
}
