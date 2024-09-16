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

use super::misc;
use crate::errors::{self, CandidateTraitNote, NoAssociatedItem};
use crate::method::probe::{AutorefOrPtrAdjustment, IsSuggestion, Mode, ProbeScope};
use crate::method::suggest::traits::all_traits;
use crate::method::suggest::SelfSource;
use crate::method::{CandidateSource, MethodError, NoMatchData};
use crate::{Expectation, FnCtxt};

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    pub(super) fn note_candidates_on_method_error(
        &self,
        rcvr_ty: Ty<'tcx>,
        item_name: Ident,
        self_source: SelfSource<'tcx>,
        args: Option<&'tcx [hir::Expr<'tcx>]>,
        span: Span,
        err: &mut Diag<'_>,
        sources: &mut Vec<CandidateSource>,
        sugg_span: Option<Span>,
    ) {
        sources.sort_by_key(|source| match source {
            CandidateSource::Trait(id) => (0, self.tcx.def_path_str(id)),
            CandidateSource::Impl(id) => (1, self.tcx.def_path_str(id)),
        });
        sources.dedup();
        // Dynamic limit to avoid hiding just one candidate, which is silly.
        let limit = if sources.len() == 5 { 5 } else { 4 };

        let mut suggs = vec![];
        for (idx, source) in sources.iter().take(limit).enumerate() {
            match *source {
                CandidateSource::Impl(impl_did) => {
                    // Provide the best span we can. Use the item, if local to crate, else
                    // the impl, if local to crate (item may be defaulted), else nothing.
                    let Some(item) = self.associated_value(impl_did, item_name).or_else(|| {
                        let impl_trait_ref = self.tcx.impl_trait_ref(impl_did)?;
                        self.associated_value(impl_trait_ref.skip_binder().def_id, item_name)
                    }) else {
                        continue;
                    };

                    let note_span = if item.def_id.is_local() {
                        Some(self.tcx.def_span(item.def_id))
                    } else if impl_did.is_local() {
                        Some(self.tcx.def_span(impl_did))
                    } else {
                        None
                    };

                    let impl_ty = self.tcx.at(span).type_of(impl_did).instantiate_identity();

                    let insertion = match self.tcx.impl_trait_ref(impl_did) {
                        None => String::new(),
                        Some(trait_ref) => {
                            format!(
                                " of the trait `{}`",
                                self.tcx.def_path_str(trait_ref.skip_binder().def_id)
                            )
                        }
                    };

                    let (note_str, idx) = if sources.len() > 1 {
                        (
                            format!(
                                "candidate #{} is defined in an impl{} for the type `{}`",
                                idx + 1,
                                insertion,
                                impl_ty,
                            ),
                            Some(idx + 1),
                        )
                    } else {
                        (
                            format!(
                                "the candidate is defined in an impl{insertion} for the type `{impl_ty}`",
                            ),
                            None,
                        )
                    };
                    if let Some(note_span) = note_span {
                        // We have a span pointing to the method. Show note with snippet.
                        err.span_note(note_span, note_str);
                    } else {
                        err.note(note_str);
                    }
                    if let Some(sugg_span) = sugg_span
                        && let Some(trait_ref) = self.tcx.impl_trait_ref(impl_did)
                        && let Some(sugg) = print_disambiguation_help(
                            self.tcx,
                            err,
                            self_source,
                            args,
                            trait_ref
                                .instantiate(
                                    self.tcx,
                                    self.fresh_args_for_item(sugg_span, impl_did),
                                )
                                .with_self_ty(self.tcx, rcvr_ty),
                            idx,
                            sugg_span,
                            item,
                        )
                    {
                        suggs.push(sugg);
                    }
                }
                CandidateSource::Trait(trait_did) => {
                    let Some(item) = self.associated_value(trait_did, item_name) else { continue };
                    let item_span = self.tcx.def_span(item.def_id);
                    let idx = if sources.len() > 1 {
                        let msg = format!(
                            "candidate #{} is defined in the trait `{}`",
                            idx + 1,
                            self.tcx.def_path_str(trait_did)
                        );
                        err.span_note(item_span, msg);
                        Some(idx + 1)
                    } else {
                        let msg = format!(
                            "the candidate is defined in the trait `{}`",
                            self.tcx.def_path_str(trait_did)
                        );
                        err.span_note(item_span, msg);
                        None
                    };
                    if let Some(sugg_span) = sugg_span
                        && let Some(sugg) = print_disambiguation_help(
                            self.tcx,
                            err,
                            self_source,
                            args,
                            ty::TraitRef::new_from_args(
                                self.tcx,
                                trait_did,
                                self.fresh_args_for_item(sugg_span, trait_did),
                            )
                            .with_self_ty(self.tcx, rcvr_ty),
                            idx,
                            sugg_span,
                            item,
                        )
                    {
                        suggs.push(sugg);
                    }
                }
            }
        }
        if !suggs.is_empty()
            && let Some(span) = sugg_span
        {
            suggs.sort();
            err.span_suggestions(
                span.with_hi(item_name.span.lo()),
                "use fully-qualified syntax to disambiguate",
                suggs,
                Applicability::MachineApplicable,
            );
        }
        if sources.len() > limit {
            err.note(format!("and {} others", sources.len() - limit));
        }
    }
}

fn print_disambiguation_help<'tcx>(
    tcx: TyCtxt<'tcx>,
    err: &mut Diag<'_>,
    source: SelfSource<'tcx>,
    args: Option<&'tcx [hir::Expr<'tcx>]>,
    trait_ref: ty::TraitRef<'tcx>,
    candidate_idx: Option<usize>,
    span: Span,
    item: ty::AssocItem,
) -> Option<String> {
    let trait_impl_type = trait_ref.self_ty().peel_refs();
    let trait_ref = if item.fn_has_self_parameter {
        trait_ref.print_only_trait_name().to_string()
    } else {
        format!("<{} as {}>", trait_ref.args[0], trait_ref.print_only_trait_name())
    };
    Some(
        if matches!(item.kind, ty::AssocKind::Fn)
            && let SelfSource::MethodCall(receiver) = source
            && let Some(args) = args
        {
            let def_kind_descr = tcx.def_kind_descr(item.kind.as_def_kind(), item.def_id);
            let item_name = item.ident(tcx);
            let first_input =
                tcx.fn_sig(item.def_id).instantiate_identity().skip_binder().inputs().get(0);
            let (first_arg_type, rcvr_ref) = (
                first_input.map(|first| first.peel_refs()),
                first_input
                    .and_then(|ty| ty.ref_mutability())
                    .map_or("", |mutbl| mutbl.ref_prefix_str()),
            );

            // If the type of first arg of this assoc function is `Self` or current trait impl type or `arbitrary_self_types`, we need to take the receiver as args. Otherwise, we don't.
            let args = if let Some(first_arg_type) = first_arg_type
                && (first_arg_type == tcx.types.self_param
                    || first_arg_type == trait_impl_type
                    || item.fn_has_self_parameter)
            {
                Some(receiver)
            } else {
                None
            }
            .into_iter()
            .chain(args)
            .map(|arg| {
                tcx.sess.source_map().span_to_snippet(arg.span).unwrap_or_else(|_| "_".to_owned())
            })
            .collect::<Vec<_>>()
            .join(", ");

            let args = format!("({}{})", rcvr_ref, args);
            err.span_suggestion_verbose(
                span,
                format!(
                    "disambiguate the {def_kind_descr} for {}",
                    if let Some(candidate) = candidate_idx {
                        format!("candidate #{candidate}")
                    } else {
                        "the candidate".to_string()
                    },
                ),
                format!("{trait_ref}::{item_name}{args}"),
                Applicability::HasPlaceholders,
            );
            return None;
        } else {
            format!("{trait_ref}::")
        },
    )
}
