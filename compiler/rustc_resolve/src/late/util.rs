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
}
