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
    pub(crate) fn suggest_derive(
        &self,
        err: &mut Diag<'_>,
        unsatisfied_predicates: &[(
            ty::Predicate<'tcx>,
            Option<ty::Predicate<'tcx>>,
            Option<ObligationCause<'tcx>>,
        )],
    ) -> bool {
        let mut derives = self.note_predicate_source_and_get_derives(err, unsatisfied_predicates);
        derives.sort();
        derives.dedup();

        let mut derives_grouped = Vec::<(String, Span, String)>::new();
        for (self_name, self_span, trait_name) in derives.into_iter() {
            if let Some((last_self_name, _, ref mut last_trait_names)) = derives_grouped.last_mut()
            {
                if last_self_name == &self_name {
                    last_trait_names.push_str(format!(", {trait_name}").as_str());
                    continue;
                }
            }
            derives_grouped.push((self_name, self_span, trait_name.to_string()));
        }

        for (self_name, self_span, traits) in &derives_grouped {
            err.span_suggestion_verbose(
                self_span.shrink_to_lo(),
                format!("consider annotating `{self_name}` with `#[derive({traits})]`"),
                format!("#[derive({traits})]\n"),
                Applicability::MaybeIncorrect,
            );
        }
        !derives_grouped.is_empty()
    }

    pub(super) fn note_predicate_source_and_get_derives(
        &self,
        err: &mut Diag<'_>,
        unsatisfied_predicates: &[(
            ty::Predicate<'tcx>,
            Option<ty::Predicate<'tcx>>,
            Option<ObligationCause<'tcx>>,
        )],
    ) -> Vec<(String, Span, Symbol)> {
        let mut derives = Vec::<(String, Span, Symbol)>::new();
        let mut traits = Vec::new();
        for (pred, _, _) in unsatisfied_predicates {
            let Some(ty::PredicateKind::Clause(ty::ClauseKind::Trait(trait_pred))) =
                pred.kind().no_bound_vars()
            else {
                continue;
            };
            let adt = match trait_pred.self_ty().ty_adt_def() {
                Some(adt) if adt.did().is_local() => adt,
                _ => continue,
            };
            if let Some(diagnostic_name) = self.tcx.get_diagnostic_name(trait_pred.def_id()) {
                let can_derive = match diagnostic_name {
                    sym::Default => !adt.is_enum(),
                    sym::Eq
                    | sym::PartialEq
                    | sym::Ord
                    | sym::PartialOrd
                    | sym::Clone
                    | sym::Copy
                    | sym::Hash
                    | sym::Debug => true,
                    _ => false,
                };
                if can_derive {
                    let self_name = trait_pred.self_ty().to_string();
                    let self_span = self.tcx.def_span(adt.did());
                    for super_trait in
                        supertraits(self.tcx, ty::Binder::dummy(trait_pred.trait_ref))
                    {
                        if let Some(parent_diagnostic_name) =
                            self.tcx.get_diagnostic_name(super_trait.def_id())
                        {
                            derives.push((self_name.clone(), self_span, parent_diagnostic_name));
                        }
                    }
                    derives.push((self_name, self_span, diagnostic_name));
                } else {
                    traits.push(trait_pred.def_id());
                }
            } else {
                traits.push(trait_pred.def_id());
            }
        }
        traits.sort_by_key(|id| self.tcx.def_path_str(id));
        traits.dedup();

        let len = traits.len();
        if len > 0 {
            let span =
                MultiSpan::from_spans(traits.iter().map(|&did| self.tcx.def_span(did)).collect());
            let mut names = format!("`{}`", self.tcx.def_path_str(traits[0]));
            for (i, &did) in traits.iter().enumerate().skip(1) {
                if len > 2 {
                    names.push_str(", ");
                }
                if i == len - 1 {
                    names.push_str(" and ");
                }
                names.push('`');
                names.push_str(&self.tcx.def_path_str(did));
                names.push('`');
            }
            err.span_note(
                span,
                format!("the trait{} {} must be implemented", pluralize!(len), names),
            );
        }

        derives
    }
}
