# Kea Type System Formalization

Lean 4 formalization of Kea's type-and-effect system.

This work starts by cannibalizing the existing Rill formal corpus and then extending it for Kea's effect-row and handler semantics.

## Current Status

- **Phase 1 (active):** Core migration from Rill `formal/` into `kea/formal/`, with effect-row surface aligned to Kea (`Ty.functionEff` + `EffectRow`) and current Lean build green.
- **Phase 1 (active):** Core migration now includes explicit WF judgments and substitution-preservation lemmas for the effect-row-extended core surface.
- **Phase 1 (active):** Unification-side WF contracts are now staged (`Kea/WellFormed`, `Kea/Properties/WfSubstitution`, `Kea/Properties/WfRename`, `Kea/Properties/WfGeneralize`, `Kea/Properties/WfUnify`), including branch-shaped row-update lemmas for `unifyRows`.
- **Phase 1 (active):** Combined row-branch contracts now include extension + WF range + compat/WF swap packaging via `Kea/Properties/WfUnifyExtends` (`unifyRows_contract_full_wf`).
- **Phase 1 (active):** `WfUnifyExtends` now has branch-complete wrappers (no-update, single-bind, open-open fresh) for direct full-contract discharge at common `unifyRows` success shapes.
- **Phase 1 (active):** `WfUnifyExtends` now includes `bindTypeVar` combined contracts (`bindTypeVar_ok_extendsAndWfRange`, `bindTypeVar_ok_contract_full_wf`) so type-var bind success paths share the same extension + WF range + acyclic compat/WF packaging surface.
- **Phase 1 (active):** `WfUnifyExtends` now includes full-state `bindTypeVar` packaging (`bindTypeVar_ok_with_non_subst_fields_contract_full_wf`) so type-var bind contracts compose cleanly with non-`subst` state updates.
- **Phase 1 (active):** `WfUnifyExtends` now includes contract projections for `bindTypeVar` full contracts (extension-only and WF-range-only, including non-`subst` state variants) to simplify downstream theorem consumption.
- **Phase 1 (active):** `WfUnifyExtends` now also projects the acyclic compat/WF agreement component out of `bindTypeVar` full contracts (base + non-`subst` state variants), completing one-hop access to all three contract facets.
- **Phase 1 (active):** `WfUnify` now includes `bindTypeVar` WF transport wrappers over non-`subst` state edits (`bindTypeVar_ok_with_lacks_preserves_substWellFormedRange`, `bindTypeVar_ok_with_non_subst_fields_preserves_substWellFormedRange`) for direct reuse in branch/state proofs.
- **Phase 1 (active):** `WfSubstitution` now includes WF-empty corollaries for well-founded row/effect-row substitution (`applySubstRowWF_empty_preserves_wf`, `applySubstEffectRowWF_empty_preserves_wf`) to complete the empty-substitution WF baseline across effect-row forms.
- **Phase 1 (active):** `WfSubstitution` now includes `TyList`/`RowFields` WF-preservation and empty-substitution lemmas (`applySubstTyList_preserves_wf_of_no_domain_vars`, `applySubstRowFields_preserves_wf_of_no_domain_vars`, `applySubstTyList_empty_preserves_wf`, `applySubstRowFields_empty_preserves_wf`) to close container-level WF gaps.
- **Phase 1 (active):** `WfSubstitution` now includes explicit `Ty.functionEff` component-wise WF wrappers for both fuel and WF substitution (`applySubst_functionEff_preserves_wf_of_component_no_domain_vars`, `applySubstWF_functionEff_preserves_wf_of_component_no_domain_vars`), alongside the existing compat wrapper.
- **Phase 1 (active):** Added explicit effect-row compat alias/surface (`applySubstEffectRowCompat`) and `WfSubstitution` lemmas (`applySubstEffectRowCompat_preserves_wf_of_no_domain_vars`, `applySubstEffectRowCompat_empty_preserves_wf`) so effect-row call sites can stay on compat APIs end-to-end.
- **Phase 1 (active):** Added compat aliases for `TyList`/`RowFields` (`applySubstTyListCompat`, `applySubstRowFieldsCompat`) with matching `WfSubstitution` preservation/empty lemmas, completing container-level compat WF surfaces.
- **Phase 1 (active):** `WfGeneralize` now includes a component-wise effect-row wrapper (`generalize_functionEff_preserves_wf_of_component_no_domain_vars`) for `Ty.functionEff` generalization under split no-domain assumptions.
- **Phase 1 (active):** `WfGeneralize` now includes `instantiate_functionEff_preserves_wf`, aligning effect-row `instantiate` WF coverage with the `functionEff` component-wise `generalize` wrapper.
- **Phase 1 (active):** `WfGeneralize` now includes `functionEff` convenience wrappers for `generalize`/`instantiate` entrypoints (`generalize_functionEff_empty_preserves_wf`, `instantiate_functionEff_mono_preserves_wf`, `instantiate_functionEff_preserves_wf_of_mapping_respects_ctx`) so common mono/non-mono cases can be discharged directly.
- **Phase 2 (next):** Kea-specific effect typing and handler theorems.

The formal workspace lives at [`formal/`](formal/).

## Scope

### Phase 1: Core HM + Row Migration

Migrate and align these Lean modules with `kea-types` and `kea-infer`:

- `Kea/Ty.lean`
- `Kea/Substitution.lean`
- `Kea/FreeVars.lean`
- `Kea/OccursCheck.lean`
- `Kea/LacksConstraints.lean`
- `Kea/Unify.lean`
- `Kea/Generalize.lean`
- `Kea/Traits.lean`
- `Kea/Typing.lean`

### Phase 2: Kea Effect/Handler Formalization

Add Kea-native theorems for:

- Handler effect removal
- Resume linearity (at-most-once)
- Fail as zero-resume
- Fail/Result equivalence
- Effect polymorphism soundness

## Workflow Contract

Use MCP-first verification, mirroring the Rill protocol:

1. Predict (Lean conjecture + explicit preconditions)
2. Probe (`kea-mcp`: `type_check`, `diagnose`, `get_type`)
3. Classify (agreement / precondition gap / divergence)
4. Act (prove, revise, or log divergence)
5. Traceability (theorem + MCP evidence link)

All session evidence goes to [`formal/mcp-log.md`](formal/mcp-log.md).

## Build

```bash
cd formal && lake build
```

Lean runs independently of Rust checks.
