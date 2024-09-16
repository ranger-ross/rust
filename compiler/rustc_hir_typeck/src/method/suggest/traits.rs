#![allow(unused_imports)]

use core::ops::ControlFlow;
use std::borrow::Cow;

use hir::Expr;
use rustc_ast::ast::Mutability;
use rustc_attr::parse_confusables;
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_data_structures::sorted_map::SortedMap;
use rustc_errors::{pluralize, Applicability, Diag, MultiSpan};
use rustc_hir::def_id::DefId;
use rustc_hir::lang_items::LangItem;
use rustc_hir::{self as hir, Node};
use rustc_middle::ty::fast_reject::{simplify_type, TreatParams};
use rustc_middle::ty::print::{
    with_crate_prefix, with_forced_trimmed_paths, PrintTraitRefExt as _,
};
use rustc_middle::ty::{self, GenericArgKind, IsSuggestable, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefIdSet;
use rustc_span::symbol::{kw, sym, Ident};
use rustc_span::Span;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
use rustc_trait_selection::traits::{FulfillmentError, Obligation, ObligationCause};
use tracing::debug;

use crate::errors::CandidateTraitNote;
use crate::method::probe::{AutorefOrPtrAdjustment, IsSuggestion, Mode, ProbeScope};
use crate::method::suggest::SelfSource;
use crate::method::{CandidateSource, MethodError};
use crate::FnCtxt;

#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) struct TraitInfo {
    pub def_id: DefId,
}

/// Retrieves all traits in this crate and any dependent crates,
/// and wraps them into `TraitInfo` for custom sorting.
pub(crate) fn all_traits(tcx: TyCtxt<'_>) -> Vec<TraitInfo> {
    tcx.all_traits().map(|def_id| TraitInfo { def_id }).collect()
}

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    pub(super) fn suggest_valid_traits(
        &self,
        err: &mut Diag<'_>,
        item_name: Ident,
        valid_out_of_scope_traits: Vec<DefId>,
        explain: bool,
    ) -> bool {
        if !valid_out_of_scope_traits.is_empty() {
            let mut candidates = valid_out_of_scope_traits;
            candidates.sort_by_key(|id| self.tcx.def_path_str(id));
            candidates.dedup();

            // `TryFrom` and `FromIterator` have no methods
            let edition_fix = candidates
                .iter()
                .find(|did| self.tcx.is_diagnostic_item(sym::TryInto, **did))
                .copied();

            if explain {
                err.help("items from traits can only be used if the trait is in scope");
            }

            let msg = format!(
                "{this_trait_is} implemented but not in scope",
                this_trait_is = if candidates.len() == 1 {
                    format!(
                        "trait `{}` which provides `{item_name}` is",
                        self.tcx.item_name(candidates[0]),
                    )
                } else {
                    format!("the following traits which provide `{item_name}` are")
                }
            );

            self.suggest_use_candidates(candidates, |accessible_sugg, inaccessible_sugg, span| {
                let suggest_for_access = |err: &mut Diag<'_>, mut msg: String, suggs: Vec<_>| {
                    msg += &format!(
                        "; perhaps you want to import {one_of}",
                        one_of = if suggs.len() == 1 { "it" } else { "one of them" },
                    );
                    err.span_suggestions(span, msg, suggs, Applicability::MaybeIncorrect);
                };
                let suggest_for_privacy = |err: &mut Diag<'_>, suggs: Vec<String>| {
                    let msg = format!(
                        "{this_trait_is} implemented but not reachable",
                        this_trait_is = if let [sugg] = suggs.as_slice() {
                            format!("trait `{}` which provides `{item_name}` is", sugg.trim())
                        } else {
                            format!("the following traits which provide `{item_name}` are")
                        }
                    );
                    if suggs.len() == 1 {
                        err.help(msg);
                    } else {
                        err.span_suggestions(span, msg, suggs, Applicability::MaybeIncorrect);
                    }
                };
                if accessible_sugg.is_empty() {
                    // `inaccessible_sugg` must not be empty
                    suggest_for_privacy(err, inaccessible_sugg);
                } else if inaccessible_sugg.is_empty() {
                    suggest_for_access(err, msg, accessible_sugg);
                } else {
                    suggest_for_access(err, msg, accessible_sugg);
                    suggest_for_privacy(err, inaccessible_sugg);
                }
            });

            if let Some(did) = edition_fix {
                err.note(format!(
                    "'{}' is included in the prelude starting in Edition 2021",
                    with_crate_prefix!(self.tcx.def_path_str(did))
                ));
            }

            true
        } else {
            false
        }
    }

    pub(super) fn suggest_traits_to_import(
        &self,
        err: &mut Diag<'_>,
        span: Span,
        rcvr_ty: Ty<'tcx>,
        item_name: Ident,
        inputs_len: Option<usize>,
        source: SelfSource<'tcx>,
        valid_out_of_scope_traits: Vec<DefId>,
        static_candidates: &[CandidateSource],
        unsatisfied_bounds: bool,
        return_type: Option<Ty<'tcx>>,
        trait_missing_method: bool,
    ) {
        let mut alt_rcvr_sugg = false;
        let mut trait_in_other_version_found = false;
        if let (SelfSource::MethodCall(rcvr), false) = (source, unsatisfied_bounds) {
            debug!(
                "suggest_traits_to_import: span={:?}, item_name={:?}, rcvr_ty={:?}, rcvr={:?}",
                span, item_name, rcvr_ty, rcvr
            );
            let skippable = [
                self.tcx.lang_items().clone_trait(),
                self.tcx.lang_items().deref_trait(),
                self.tcx.lang_items().deref_mut_trait(),
                self.tcx.lang_items().drop_trait(),
                self.tcx.get_diagnostic_item(sym::AsRef),
            ];
            // Try alternative arbitrary self types that could fulfill this call.
            // FIXME: probe for all types that *could* be arbitrary self-types, not
            // just this list.
            for (rcvr_ty, post, pin_call) in &[
                (rcvr_ty, "", None),
                (
                    Ty::new_mut_ref(self.tcx, self.tcx.lifetimes.re_erased, rcvr_ty),
                    "&mut ",
                    Some("as_mut"),
                ),
                (
                    Ty::new_imm_ref(self.tcx, self.tcx.lifetimes.re_erased, rcvr_ty),
                    "&",
                    Some("as_ref"),
                ),
            ] {
                match self.lookup_probe_for_diagnostic(
                    item_name,
                    *rcvr_ty,
                    rcvr,
                    ProbeScope::AllTraits,
                    return_type,
                ) {
                    Ok(pick) => {
                        // If the method is defined for the receiver we have, it likely wasn't `use`d.
                        // We point at the method, but we just skip the rest of the check for arbitrary
                        // self types and rely on the suggestion to `use` the trait from
                        // `suggest_valid_traits`.
                        let did = Some(pick.item.container_id(self.tcx));
                        if skippable.contains(&did) {
                            continue;
                        }
                        trait_in_other_version_found = self
                            .detect_and_explain_multiple_crate_versions(
                                err,
                                pick.item.def_id,
                                rcvr.hir_id,
                                Some(*rcvr_ty),
                            );
                        if pick.autoderefs == 0 && !trait_in_other_version_found {
                            err.span_label(
                                pick.item.ident(self.tcx).span,
                                format!("the method is available for `{rcvr_ty}` here"),
                            );
                        }
                        break;
                    }
                    Err(MethodError::Ambiguity(_)) => {
                        // If the method is defined (but ambiguous) for the receiver we have, it is also
                        // likely we haven't `use`d it. It may be possible that if we `Box`/`Pin`/etc.
                        // the receiver, then it might disambiguate this method, but I think these
                        // suggestions are generally misleading (see #94218).
                        break;
                    }
                    Err(_) => (),
                }

                let Some(unpin_trait) = self.tcx.lang_items().unpin_trait() else {
                    return;
                };
                let pred = ty::TraitRef::new(self.tcx, unpin_trait, [*rcvr_ty]);
                let unpin = self.predicate_must_hold_considering_regions(&Obligation::new(
                    self.tcx,
                    ObligationCause::misc(rcvr.span, self.body_id),
                    self.param_env,
                    pred,
                ));
                for (rcvr_ty, pre) in &[
                    (Ty::new_lang_item(self.tcx, *rcvr_ty, LangItem::OwnedBox), "Box::new"),
                    (Ty::new_lang_item(self.tcx, *rcvr_ty, LangItem::Pin), "Pin::new"),
                    (Ty::new_diagnostic_item(self.tcx, *rcvr_ty, sym::Arc), "Arc::new"),
                    (Ty::new_diagnostic_item(self.tcx, *rcvr_ty, sym::Rc), "Rc::new"),
                ] {
                    if let Some(new_rcvr_t) = *rcvr_ty
                        && let Ok(pick) = self.lookup_probe_for_diagnostic(
                            item_name,
                            new_rcvr_t,
                            rcvr,
                            ProbeScope::AllTraits,
                            return_type,
                        )
                    {
                        debug!("try_alt_rcvr: pick candidate {:?}", pick);
                        let did = Some(pick.item.container_id(self.tcx));
                        // We don't want to suggest a container type when the missing
                        // method is `.clone()` or `.deref()` otherwise we'd suggest
                        // `Arc::new(foo).clone()`, which is far from what the user wants.
                        // Explicitly ignore the `Pin::as_ref()` method as `Pin` does not
                        // implement the `AsRef` trait.
                        let skip = skippable.contains(&did)
                            || (("Pin::new" == *pre)
                                && ((sym::as_ref == item_name.name) || !unpin))
                            || inputs_len.is_some_and(|inputs_len| {
                                pick.item.kind == ty::AssocKind::Fn
                                    && self
                                        .tcx
                                        .fn_sig(pick.item.def_id)
                                        .skip_binder()
                                        .skip_binder()
                                        .inputs()
                                        .len()
                                        != inputs_len
                            });
                        // Make sure the method is defined for the *actual* receiver: we don't
                        // want to treat `Box<Self>` as a receiver if it only works because of
                        // an autoderef to `&self`
                        if pick.autoderefs == 0 && !skip {
                            err.span_label(
                                pick.item.ident(self.tcx).span,
                                format!("the method is available for `{new_rcvr_t}` here"),
                            );
                            err.multipart_suggestion(
                                "consider wrapping the receiver expression with the \
                                 appropriate type",
                                vec![
                                    (rcvr.span.shrink_to_lo(), format!("{pre}({post}")),
                                    (rcvr.span.shrink_to_hi(), ")".to_string()),
                                ],
                                Applicability::MaybeIncorrect,
                            );
                            // We don't care about the other suggestions.
                            alt_rcvr_sugg = true;
                        }
                    }
                }
                // We special case the situation where `Pin::new` wouldn't work, and instead
                // suggest using the `pin!()` macro instead.
                if let Some(new_rcvr_t) = Ty::new_lang_item(self.tcx, *rcvr_ty, LangItem::Pin)
                    // We didn't find an alternative receiver for the method.
                    && !alt_rcvr_sugg
                    // `T: !Unpin`
                    && !unpin
                    // The method isn't `as_ref`, as it would provide a wrong suggestion for `Pin`.
                    && sym::as_ref != item_name.name
                    // Either `Pin::as_ref` or `Pin::as_mut`.
                    && let Some(pin_call) = pin_call
                    // Search for `item_name` as a method accessible on `Pin<T>`.
                    && let Ok(pick) = self.lookup_probe_for_diagnostic(
                        item_name,
                        new_rcvr_t,
                        rcvr,
                        ProbeScope::AllTraits,
                        return_type,
                    )
                    // We skip some common traits that we don't want to consider because autoderefs
                    // would take care of them.
                    && !skippable.contains(&Some(pick.item.container_id(self.tcx)))
                    // We don't want to go through derefs.
                    && pick.autoderefs == 0
                    // Check that the method of the same name that was found on the new `Pin<T>`
                    // receiver has the same number of arguments that appear in the user's code.
                    && inputs_len.is_some_and(|inputs_len| pick.item.kind == ty::AssocKind::Fn && self.tcx.fn_sig(pick.item.def_id).skip_binder().skip_binder().inputs().len() == inputs_len)
                {
                    let indent = self
                        .tcx
                        .sess
                        .source_map()
                        .indentation_before(rcvr.span)
                        .unwrap_or_else(|| " ".to_string());
                    let mut expr = rcvr;
                    while let Node::Expr(call_expr) = self.tcx.parent_hir_node(expr.hir_id)
                        && let hir::ExprKind::MethodCall(hir::PathSegment { .. }, ..) =
                            call_expr.kind
                    {
                        expr = call_expr;
                    }
                    match self.tcx.parent_hir_node(expr.hir_id) {
                        Node::LetStmt(stmt)
                            if let Some(init) = stmt.init
                                && let Ok(code) =
                                    self.tcx.sess.source_map().span_to_snippet(rcvr.span) =>
                        {
                            // We need to take care to account for the existing binding when we
                            // suggest the code.
                            err.multipart_suggestion(
                                "consider pinning the expression",
                                vec![
                                    (
                                        stmt.span.shrink_to_lo(),
                                        format!(
                                            "let mut pinned = std::pin::pin!({code});\n{indent}"
                                        ),
                                    ),
                                    (
                                        init.span.until(rcvr.span.shrink_to_hi()),
                                        format!("pinned.{pin_call}()"),
                                    ),
                                ],
                                Applicability::MaybeIncorrect,
                            );
                        }
                        Node::Block(_) | Node::Stmt(_) => {
                            // There's no binding, so we can provide a slightly nicer looking
                            // suggestion.
                            err.multipart_suggestion(
                                "consider pinning the expression",
                                vec![
                                    (
                                        rcvr.span.shrink_to_lo(),
                                        format!("let mut pinned = std::pin::pin!("),
                                    ),
                                    (
                                        rcvr.span.shrink_to_hi(),
                                        format!(");\n{indent}pinned.{pin_call}()"),
                                    ),
                                ],
                                Applicability::MaybeIncorrect,
                            );
                        }
                        _ => {
                            // We don't quite know what the users' code looks like, so we don't
                            // provide a pinning suggestion.
                            err.span_help(
                                rcvr.span,
                                "consider pinning the expression with `std::pin::pin!()` and \
                                 assigning that to a new binding",
                            );
                        }
                    }
                    // We don't care about the other suggestions.
                    alt_rcvr_sugg = true;
                }
            }
        }

        if let SelfSource::QPath(ty) = source
            && !valid_out_of_scope_traits.is_empty()
            && let hir::TyKind::Path(path) = ty.kind
            && let hir::QPath::Resolved(..) = path
            && let Some(assoc) = self
                .tcx
                .associated_items(valid_out_of_scope_traits[0])
                .filter_by_name_unhygienic(item_name.name)
                .next()
        {
            // See if the `Type::function(val)` where `function` wasn't found corresponds to a
            // `Trait` that is imported directly, but `Type` came from a different version of the
            // same crate.

            let rcvr_ty = self.node_ty_opt(ty.hir_id);
            trait_in_other_version_found = self.detect_and_explain_multiple_crate_versions(
                err,
                assoc.def_id,
                ty.hir_id,
                rcvr_ty,
            );
        }
        if !trait_in_other_version_found
            && self.suggest_valid_traits(err, item_name, valid_out_of_scope_traits, true)
        {
            return;
        }

        let type_is_local = self.type_derefs_to_local(span, rcvr_ty, source);

        let mut arbitrary_rcvr = vec![];
        // There are no traits implemented, so lets suggest some traits to
        // implement, by finding ones that have the item name, and are
        // legal to implement.
        let mut candidates = all_traits(self.tcx)
            .into_iter()
            // Don't issue suggestions for unstable traits since they're
            // unlikely to be implementable anyway
            .filter(|info| match self.tcx.lookup_stability(info.def_id) {
                Some(attr) => attr.level.is_stable(),
                None => true,
            })
            .filter(|info| {
                // Static candidates are already implemented, and known not to work
                // Do not suggest them again
                static_candidates.iter().all(|sc| match *sc {
                    CandidateSource::Trait(def_id) => def_id != info.def_id,
                    CandidateSource::Impl(def_id) => {
                        self.tcx.trait_id_of_impl(def_id) != Some(info.def_id)
                    }
                })
            })
            .filter(|info| {
                // We approximate the coherence rules to only suggest
                // traits that are legal to implement by requiring that
                // either the type or trait is local. Multi-dispatch means
                // this isn't perfect (that is, there are cases when
                // implementing a trait would be legal but is rejected
                // here).
                (type_is_local || info.def_id.is_local())
                    && !self.tcx.trait_is_auto(info.def_id)
                    && self
                        .associated_value(info.def_id, item_name)
                        .filter(|item| {
                            if let ty::AssocKind::Fn = item.kind {
                                let id = item
                                    .def_id
                                    .as_local()
                                    .map(|def_id| self.tcx.hir_node_by_def_id(def_id));
                                if let Some(hir::Node::TraitItem(hir::TraitItem {
                                    kind: hir::TraitItemKind::Fn(fn_sig, method),
                                    ..
                                })) = id
                                {
                                    let self_first_arg = match method {
                                        hir::TraitFn::Required([ident, ..]) => {
                                            ident.name == kw::SelfLower
                                        }
                                        hir::TraitFn::Provided(body_id) => {
                                            self.tcx.hir().body(*body_id).params.first().map_or(
                                                false,
                                                |param| {
                                                    matches!(
                                                        param.pat.kind,
                                                        hir::PatKind::Binding(_, _, ident, _)
                                                            if ident.name == kw::SelfLower
                                                    )
                                                },
                                            )
                                        }
                                        _ => false,
                                    };

                                    if !fn_sig.decl.implicit_self.has_implicit_self()
                                        && self_first_arg
                                    {
                                        if let Some(ty) = fn_sig.decl.inputs.get(0) {
                                            arbitrary_rcvr.push(ty.span);
                                        }
                                        return false;
                                    }
                                }
                            }
                            // We only want to suggest public or local traits (#45781).
                            item.visibility(self.tcx).is_public() || info.def_id.is_local()
                        })
                        .is_some()
            })
            .collect::<Vec<_>>();
        for span in &arbitrary_rcvr {
            err.span_label(
                *span,
                "the method might not be found because of this arbitrary self type",
            );
        }
        if alt_rcvr_sugg {
            return;
        }

        if !candidates.is_empty() {
            // Sort local crate results before others
            candidates
                .sort_by_key(|&info| (!info.def_id.is_local(), self.tcx.def_path_str(info.def_id)));
            candidates.dedup();

            let param_type = match *rcvr_ty.kind() {
                ty::Param(param) => Some(param),
                ty::Ref(_, ty, _) => match *ty.kind() {
                    ty::Param(param) => Some(param),
                    _ => None,
                },
                _ => None,
            };
            if !trait_missing_method {
                err.help(if param_type.is_some() {
                    "items from traits can only be used if the type parameter is bounded by the trait"
                } else {
                    "items from traits can only be used if the trait is implemented and in scope"
                });
            }

            let candidates_len = candidates.len();
            let message = |action| {
                format!(
                    "the following {traits_define} an item `{name}`, perhaps you need to {action} \
                     {one_of_them}:",
                    traits_define =
                        if candidates_len == 1 { "trait defines" } else { "traits define" },
                    action = action,
                    one_of_them = if candidates_len == 1 { "it" } else { "one of them" },
                    name = item_name,
                )
            };
            // Obtain the span for `param` and use it for a structured suggestion.
            if let Some(param) = param_type {
                let generics = self.tcx.generics_of(self.body_id.to_def_id());
                let type_param = generics.type_param(param, self.tcx);
                let hir = self.tcx.hir();
                if let Some(def_id) = type_param.def_id.as_local() {
                    let id = self.tcx.local_def_id_to_hir_id(def_id);
                    // Get the `hir::Param` to verify whether it already has any bounds.
                    // We do this to avoid suggesting code that ends up as `T: FooBar`,
                    // instead we suggest `T: Foo + Bar` in that case.
                    match self.tcx.hir_node(id) {
                        Node::GenericParam(param) => {
                            enum Introducer {
                                Plus,
                                Colon,
                                Nothing,
                            }
                            let hir_generics = hir.get_generics(id.owner.def_id).unwrap();
                            let trait_def_ids: DefIdSet = hir_generics
                                .bounds_for_param(def_id)
                                .flat_map(|bp| bp.bounds.iter())
                                .filter_map(|bound| bound.trait_ref()?.trait_def_id())
                                .collect();
                            if candidates.iter().any(|t| trait_def_ids.contains(&t.def_id)) {
                                return;
                            }
                            let msg = message(format!(
                                "restrict type parameter `{}` with",
                                param.name.ident(),
                            ));
                            let bounds_span = hir_generics.bounds_span_for_suggestions(def_id);
                            if rcvr_ty.is_ref()
                                && param.is_impl_trait()
                                && let Some((bounds_span, _)) = bounds_span
                            {
                                err.multipart_suggestions(
                                    msg,
                                    candidates.iter().map(|t| {
                                        vec![
                                            (param.span.shrink_to_lo(), "(".to_string()),
                                            (
                                                bounds_span,
                                                format!(" + {})", self.tcx.def_path_str(t.def_id)),
                                            ),
                                        ]
                                    }),
                                    Applicability::MaybeIncorrect,
                                );
                                return;
                            }

                            let (sp, introducer, open_paren_sp) =
                                if let Some((span, open_paren_sp)) = bounds_span {
                                    (span, Introducer::Plus, open_paren_sp)
                                } else if let Some(colon_span) = param.colon_span {
                                    (colon_span.shrink_to_hi(), Introducer::Nothing, None)
                                } else if param.is_impl_trait() {
                                    (param.span.shrink_to_hi(), Introducer::Plus, None)
                                } else {
                                    (param.span.shrink_to_hi(), Introducer::Colon, None)
                                };

                            let all_suggs = candidates.iter().map(|cand| {
                                let suggestion = format!(
                                    "{} {}",
                                    match introducer {
                                        Introducer::Plus => " +",
                                        Introducer::Colon => ":",
                                        Introducer::Nothing => "",
                                    },
                                    self.tcx.def_path_str(cand.def_id)
                                );

                                let mut suggs = vec![];

                                if let Some(open_paren_sp) = open_paren_sp {
                                    suggs.push((open_paren_sp, "(".to_string()));
                                    suggs.push((sp, format!("){suggestion}")));
                                } else {
                                    suggs.push((sp, suggestion));
                                }

                                suggs
                            });

                            err.multipart_suggestions(
                                msg,
                                all_suggs,
                                Applicability::MaybeIncorrect,
                            );

                            return;
                        }
                        Node::Item(hir::Item {
                            kind: hir::ItemKind::Trait(.., bounds, _),
                            ident,
                            ..
                        }) => {
                            let (sp, sep, article) = if bounds.is_empty() {
                                (ident.span.shrink_to_hi(), ":", "a")
                            } else {
                                (bounds.last().unwrap().span().shrink_to_hi(), " +", "another")
                            };
                            err.span_suggestions(
                                sp,
                                message(format!("add {article} supertrait for")),
                                candidates.iter().map(|t| {
                                    format!("{} {}", sep, self.tcx.def_path_str(t.def_id),)
                                }),
                                Applicability::MaybeIncorrect,
                            );
                            return;
                        }
                        _ => {}
                    }
                }
            }

            let (potential_candidates, explicitly_negative) = if param_type.is_some() {
                // FIXME: Even though negative bounds are not implemented, we could maybe handle
                // cases where a positive bound implies a negative impl.
                (candidates, Vec::new())
            } else if let Some(simp_rcvr_ty) =
                simplify_type(self.tcx, rcvr_ty, TreatParams::AsRigid)
            {
                let mut potential_candidates = Vec::new();
                let mut explicitly_negative = Vec::new();
                for candidate in candidates {
                    // Check if there's a negative impl of `candidate` for `rcvr_ty`
                    if self
                        .tcx
                        .all_impls(candidate.def_id)
                        .map(|imp_did| {
                            self.tcx.impl_trait_header(imp_did).expect(
                                "inherent impls can't be candidates, only trait impls can be",
                            )
                        })
                        .filter(|header| header.polarity != ty::ImplPolarity::Positive)
                        .any(|header| {
                            let imp = header.trait_ref.instantiate_identity();
                            let imp_simp =
                                simplify_type(self.tcx, imp.self_ty(), TreatParams::AsRigid);
                            imp_simp.is_some_and(|s| s == simp_rcvr_ty)
                        })
                    {
                        explicitly_negative.push(candidate);
                    } else {
                        potential_candidates.push(candidate);
                    }
                }
                (potential_candidates, explicitly_negative)
            } else {
                // We don't know enough about `recv_ty` to make proper suggestions.
                (candidates, Vec::new())
            };

            let impls_trait = |def_id: DefId| {
                let args = ty::GenericArgs::for_item(self.tcx, def_id, |param, _| {
                    if param.index == 0 {
                        rcvr_ty.into()
                    } else {
                        self.infcx.var_for_def(span, param)
                    }
                });
                self.infcx
                    .type_implements_trait(def_id, args, self.param_env)
                    .must_apply_modulo_regions()
                    && param_type.is_none()
            };
            match &potential_candidates[..] {
                [] => {}
                [trait_info] if trait_info.def_id.is_local() => {
                    if impls_trait(trait_info.def_id) {
                        self.suggest_valid_traits(err, item_name, vec![trait_info.def_id], false);
                    } else {
                        err.subdiagnostic(CandidateTraitNote {
                            span: self.tcx.def_span(trait_info.def_id),
                            trait_name: self.tcx.def_path_str(trait_info.def_id),
                            item_name,
                            action_or_ty: if trait_missing_method {
                                "NONE".to_string()
                            } else {
                                param_type.map_or_else(
                                    || "implement".to_string(), // FIXME: it might only need to be imported into scope, not implemented.
                                    |p| p.to_string(),
                                )
                            },
                        });
                    }
                }
                trait_infos => {
                    let mut msg = message(param_type.map_or_else(
                        || "implement".to_string(), // FIXME: it might only need to be imported into scope, not implemented.
                        |param| format!("restrict type parameter `{param}` with"),
                    ));
                    for (i, trait_info) in trait_infos.iter().enumerate() {
                        if impls_trait(trait_info.def_id) {
                            self.suggest_valid_traits(
                                err,
                                item_name,
                                vec![trait_info.def_id],
                                false,
                            );
                        }
                        msg.push_str(&format!(
                            "\ncandidate #{}: `{}`",
                            i + 1,
                            self.tcx.def_path_str(trait_info.def_id),
                        ));
                    }
                    err.note(msg);
                }
            }
            match &explicitly_negative[..] {
                [] => {}
                [trait_info] => {
                    let msg = format!(
                        "the trait `{}` defines an item `{}`, but is explicitly unimplemented",
                        self.tcx.def_path_str(trait_info.def_id),
                        item_name
                    );
                    err.note(msg);
                }
                trait_infos => {
                    let mut msg = format!(
                        "the following traits define an item `{item_name}`, but are explicitly unimplemented:"
                    );
                    for trait_info in trait_infos {
                        msg.push_str(&format!("\n{}", self.tcx.def_path_str(trait_info.def_id)));
                    }
                    err.note(msg);
                }
            }
        }
    }

    fn detect_and_explain_multiple_crate_versions(
        &self,
        err: &mut Diag<'_>,
        item_def_id: DefId,
        hir_id: hir::HirId,
        rcvr_ty: Option<Ty<'_>>,
    ) -> bool {
        let hir_id = self.tcx.parent_hir_id(hir_id);
        let Some(traits) = self.tcx.in_scope_traits(hir_id) else { return false };
        if traits.is_empty() {
            return false;
        }
        let trait_def_id = self.tcx.parent(item_def_id);
        let krate = self.tcx.crate_name(trait_def_id.krate);
        let name = self.tcx.item_name(trait_def_id);
        let candidates: Vec<_> = traits
            .iter()
            .filter(|c| {
                c.def_id.krate != trait_def_id.krate
                    && self.tcx.crate_name(c.def_id.krate) == krate
                    && self.tcx.item_name(c.def_id) == name
            })
            .map(|c| (c.def_id, c.import_ids.get(0).cloned()))
            .collect();
        if candidates.is_empty() {
            return false;
        }
        let item_span = self.tcx.def_span(item_def_id);
        let msg = format!(
            "there are multiple different versions of crate `{krate}` in the dependency graph",
        );
        let trait_span = self.tcx.def_span(trait_def_id);
        let mut multi_span: MultiSpan = trait_span.into();
        multi_span.push_span_label(trait_span, format!("this is the trait that is needed"));
        let descr = self.tcx.associated_item(item_def_id).descr();
        let rcvr_ty =
            rcvr_ty.map(|t| format!("`{t}`")).unwrap_or_else(|| "the receiver".to_string());
        multi_span
            .push_span_label(item_span, format!("the {descr} is available for {rcvr_ty} here"));
        for (def_id, import_def_id) in candidates {
            if let Some(import_def_id) = import_def_id {
                multi_span.push_span_label(
                    self.tcx.def_span(import_def_id),
                    format!(
                        "`{name}` imported here doesn't correspond to the right version of crate \
                         `{krate}`",
                    ),
                );
            }
            multi_span.push_span_label(
                self.tcx.def_span(def_id),
                format!("this is the trait that was imported"),
            );
        }
        err.span_note(multi_span, msg);
        true
    }

    pub(crate) fn note_unmet_impls_on_type(
        &self,
        err: &mut Diag<'_>,
        errors: Vec<FulfillmentError<'tcx>>,
        suggest_derive: bool,
    ) {
        let preds: Vec<_> = errors
            .iter()
            .filter_map(|e| match e.obligation.predicate.kind().skip_binder() {
                ty::PredicateKind::Clause(ty::ClauseKind::Trait(pred)) => {
                    match pred.self_ty().kind() {
                        ty::Adt(_, _) => Some(pred),
                        _ => None,
                    }
                }
                _ => None,
            })
            .collect();

        // Note for local items and foreign items respectively.
        let (mut local_preds, mut foreign_preds): (Vec<_>, Vec<_>) =
            preds.iter().partition(|&pred| {
                if let ty::Adt(def, _) = pred.self_ty().kind() {
                    def.did().is_local()
                } else {
                    false
                }
            });

        local_preds.sort_by_key(|pred: &&ty::TraitPredicate<'_>| pred.trait_ref.to_string());
        let local_def_ids = local_preds
            .iter()
            .filter_map(|pred| match pred.self_ty().kind() {
                ty::Adt(def, _) => Some(def.did()),
                _ => None,
            })
            .collect::<FxIndexSet<_>>();
        let mut local_spans: MultiSpan = local_def_ids
            .iter()
            .filter_map(|def_id| {
                let span = self.tcx.def_span(*def_id);
                if span.is_dummy() { None } else { Some(span) }
            })
            .collect::<Vec<_>>()
            .into();
        for pred in &local_preds {
            match pred.self_ty().kind() {
                ty::Adt(def, _) => {
                    local_spans.push_span_label(
                        self.tcx.def_span(def.did()),
                        format!("must implement `{}`", pred.trait_ref.print_trait_sugared()),
                    );
                }
                _ => {}
            }
        }
        if local_spans.primary_span().is_some() {
            let msg = if let [local_pred] = local_preds.as_slice() {
                format!(
                    "an implementation of `{}` might be missing for `{}`",
                    local_pred.trait_ref.print_trait_sugared(),
                    local_pred.self_ty()
                )
            } else {
                format!(
                    "the following type{} would have to `impl` {} required trait{} for this \
                     operation to be valid",
                    pluralize!(local_def_ids.len()),
                    if local_def_ids.len() == 1 { "its" } else { "their" },
                    pluralize!(local_preds.len()),
                )
            };
            err.span_note(local_spans, msg);
        }

        foreign_preds.sort_by_key(|pred: &&ty::TraitPredicate<'_>| pred.trait_ref.to_string());
        let foreign_def_ids = foreign_preds
            .iter()
            .filter_map(|pred| match pred.self_ty().kind() {
                ty::Adt(def, _) => Some(def.did()),
                _ => None,
            })
            .collect::<FxIndexSet<_>>();
        let mut foreign_spans: MultiSpan = foreign_def_ids
            .iter()
            .filter_map(|def_id| {
                let span = self.tcx.def_span(*def_id);
                if span.is_dummy() { None } else { Some(span) }
            })
            .collect::<Vec<_>>()
            .into();
        for pred in &foreign_preds {
            match pred.self_ty().kind() {
                ty::Adt(def, _) => {
                    foreign_spans.push_span_label(
                        self.tcx.def_span(def.did()),
                        format!("not implement `{}`", pred.trait_ref.print_trait_sugared()),
                    );
                }
                _ => {}
            }
        }
        if foreign_spans.primary_span().is_some() {
            let msg = if let [foreign_pred] = foreign_preds.as_slice() {
                format!(
                    "the foreign item type `{}` doesn't implement `{}`",
                    foreign_pred.self_ty(),
                    foreign_pred.trait_ref.print_trait_sugared()
                )
            } else {
                format!(
                    "the foreign item type{} {} implement required trait{} for this \
                     operation to be valid",
                    pluralize!(foreign_def_ids.len()),
                    if foreign_def_ids.len() > 1 { "don't" } else { "doesn't" },
                    pluralize!(foreign_preds.len()),
                )
            };
            err.span_note(foreign_spans, msg);
        }

        let preds: Vec<_> = errors
            .iter()
            .map(|e| (e.obligation.predicate, None, Some(e.obligation.cause.clone())))
            .collect();
        if suggest_derive {
            self.suggest_derive(err, &preds);
        } else {
            // The predicate comes from a binop where the lhs and rhs have different types.
            let _ = self.note_predicate_source_and_get_derives(err, &preds);
        }
    }
}
