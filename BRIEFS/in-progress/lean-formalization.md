# Brief: Lean Formalization Migration

**Status:** active
**Priority:** Phase 0c-0e (parallel track — formal agent works alongside implementation)
**Depends on:** 0c-effect-handlers (effect rows must be in the type system before formalizing them)
**Blocks:** nothing directly — formal proofs validate but don't gate implementation

## Motivation

Rill has a substantial Lean 4 formalization: ~50 source files, 153 MCP-verified
log entries, covering HM inference, Rémy row unification, lacks constraints,
generalize/instantiate, supertrait graphs, declarative/algorithmic typing
soundness, evaluator soundness slices, and nominal/boundary typing bridges.

This work transfers to Kea because Kea's core type system *is* Rill's, extended
with effect rows. The Lean model's `Ty` inductive, `Subst`, `Unify`, `Generalize`,
`LacksConstraints`, and `Traits` modules map directly to kea-types and kea-infer.
The MCP-first verification workflow (predict → probe → classify → act → trace)
transfers unchanged — Kea already has `kea-mcp` with `type_check`, `diagnose`,
and `get_type`.

Migrating gives us:

1. **Formal backing during the riskiest phases.** 0d and 0e are where subtle
   type/effect interactions surface. Having machine-checked proofs for the
   underlying type system catches issues that proptests miss.
2. **Effect typing formalization as new work.** No language we know of has a
   Lean formalization of row-typed algebraic effect handlers. This is novel
   and publishable.
3. **Continuity.** The formal agent has 153 sessions of context and workflow
   discipline. Migrating while that context is fresh is cheaper than recreating
   it later.

## What Transfers (Phase 1: Core Type System)

Direct migration from `rill/formal/Rill/` — rename `Rill` → `Kea`, extend
`Ty` with effect rows.

### Definitions (migrate as-is, extend for effects)

| Rill module | Kea module | Migration notes |
|-------------|-----------|-----------------|
| `Ty.lean` | `Kea/Ty.lean` | Add `EffRow` to `Ty` inductive. Add effect variable kind. |
| `Substitution.lean` | `Kea/Substitution.lean` | Extend `applySubst` for effect rows. |
| `FreeVars.lean` | `Kea/FreeVars.lean` | Add `freeEffectVars` mutual case. |
| `OccursCheck.lean` | `Kea/OccursCheck.lean` | Extend occurs check to effect variables. |
| `LacksConstraints.lean` | `Kea/LacksConstraints.lean` | Transfer as-is. |
| `Unify.lean` | `Kea/Unify.lean` | Extend for effect row unification. |
| `Generalize.lean` | `Kea/Generalize.lean` | Quantify effect variables. |
| `Traits.lean` | `Kea/Traits.lean` | Transfer as-is. |
| `Typing.lean` | `Kea/Typing.lean` | Extend typing judgments with effect annotations. |

### Properties (migrate, re-prove after Ty extension)

Transfer all Properties/ files. Most proofs should survive the `Ty` extension
with minor fixups (additional cases in mutual recursion). Files that need
substantive rework:

- `UnifyReflexive.lean` — add effect row reflexivity case
- `UnifyConsistent.lean` — extend for effect unification
- `SubstIdempotent.lean` — additional effect substitution case
- `RemyPreservesLabels.lean` — effect rows use same Rémy decomposition
- `TraitBoundsPreserved.lean` — effect variables in trait bounds

Files that transfer unchanged:
- `LacksBlocksDuplicate.lean` — no effect interaction
- `RowFieldsSorted.lean` — structural, no effect interaction
- `DecomposeFields.lean` — structural

### Drop (Rill-specific, don't migrate)

- `ColExpr.lean` — Rill column expression DSL
- `DataFrame.lean` — Rill dataframe verb typing
- `Dimensions.lean` — Rill dimension model (Kea has its own in kea-types)
- `Eval.lean` — Rill evaluator semantics (Kea compiles, doesn't interpret)
- All `Properties/DataFrame*`, `Properties/ColumnBoundary*` — Rill domain
- All `Properties/*Parity*.lean` — Rill-specific type constructor parity slices
- All `Properties/*Boundary*.lean`, `Properties/*Bridge*.lean` — Rill boundary typing

### Maybe migrate later (if Kea adds equivalent features)

- `Eval.lean` evaluator soundness — could inform Kea REPL semantics or
  comptime evaluation, but not urgent

## What's New (Phase 2: Effect Typing Formalization)

This is genuinely new work — no Rill equivalent exists.

### Effect declarations and operations

```lean
-- Effect declaration typing
inductive EffectDecl where
  | mk : Name → List TypeParam → List OperationSig → EffectDecl

-- Effect operation typing: performing an operation adds the effect
-- to the current row
```

### Handler typing (KERNEL §5.13)

The core theorem to prove:

```
Given:
  expr : T  with effects {E, R...}
  handler for E covers all operations
  each handler body : _  with effects {H...}
Then:
  handle expr { ... } : T  with effects {H..., R...}
```

This is the **effect removal** theorem — the most important property
of the handler system.

### Target theorems (new)

| Theorem | Statement | Difficulty |
|---------|-----------|------------|
| `handle_removes_effect` | Handler for E removes E from effect row | Medium |
| `handle_adds_handler_effects` | Handler body effects appear in result | Medium |
| `handle_preserves_other_effects` | Unhandled effects pass through | Medium |
| `resume_at_most_once` | Static linearity check is sound | Hard |
| `fail_is_zero_resume` | Fail handler never resumes; equivalent to Result | Medium |
| `fail_result_equivalence` | `catch expr` ≡ Result-passing transformation | Hard |
| `nested_handlers_compose` | Inner handler shadows outer for same effect | Medium |
| `effect_polymorphism_sound` | Effect variable generalization/instantiation preserves soundness | Hard |
| `tail_resumptive_classification` | Tail-resumptive handler compiles equivalently to direct call | Medium |
| `capability_direct_call_sound` | Unintercepted capability effect = direct runtime call | Easy |

### MCP-first workflow

Same protocol as Rill:

1. **Predict**: State Lean conjecture + preconditions
2. **Probe**: Run kea-mcp checks (happy path, boundary, adversarial)
3. **Classify**: Agreement / precondition gap / model divergence
4. **Act**: Prove, revise, or log divergence
5. **Traceability**: Link theorems, file edits, MCP evidence

The formal agent should maintain `formal/mcp-log.md` in the same format.

## Scheduling: Parallel, Not Sequential

The formal agent should run **in parallel** with 0c/0d/0e implementation:

```
0c implementation ←→ Phase 1 migration (core type system)
0d implementation ←→ Phase 1 proof repair (Ty extension fixups)
0e implementation ←→ Phase 2 new work (effect typing proofs)
```

### Why parallel works

1. **Independent codebases.** Lean proofs don't depend on Rust compilation.
   The formal agent uses MCP to probe the running Kea compiler, same as
   it did with Rill.

2. **MCP-first absorbs design churn.** If effect typing rules change during
   0e, the formal agent discovers this via MCP probes before proving. The
   predict→probe→classify loop is designed for exactly this.

3. **The formal agent has context now.** 153 MCP log entries, deep familiarity
   with the Rémy/HM model, the two-judgment architecture, supertrait gaps.
   This context decays if we wait.

4. **Formal work feeds back into implementation.** The Rill formalization
   found real discrepancies (supertrait gap witnesses, substitution bridge
   issues). Same will happen with effect typing.

### Risk: design churn in effect typing

The main risk is that handler typing rules change during 0e prototyping
(e.g., switching from evidence passing to CPS changes how handlers compose).
Mitigation:

- Phase 1 (core migration) is zero risk — the HM+row core is stable.
- Phase 2 effect proofs should start with the **type-level** properties
  (effect removal, handler composition) which are strategy-independent.
  Compilation strategy (evidence vs CPS) only affects **codegen-level**
  properties, which are Phase 2 stretch goals anyway.

## Implementation Plan

### Phase 1: Core migration (start after 0c lands effect rows)

1. Create `kea/formal/` directory with Lake project, batteries dependency.
2. Copy `Rill/Ty.lean` → `Kea/Ty.lean`. Extend `Ty` inductive with effect
   row constructors.
3. Migrate `Substitution`, `FreeVars`, `OccursCheck` — extend mutual
   recursion for effect rows.
4. Migrate `Unify` — add effect row unification cases.
5. Migrate `Generalize` — add effect variable quantification.
6. Migrate `LacksConstraints`, `Traits` — transfer directly.
7. Re-prove all Properties/ theorems. Fix broken cases from Ty extension.
8. Migrate `Typing.lean` — extend with effect annotations.
9. Set up MCP-first workflow against kea-mcp. First log entries.

### Phase 2: Effect typing formalization (start during 0d/0e)

1. Model effect declarations and operation typing.
2. Model handler expressions and typing rule (§5.13).
3. Prove `handle_removes_effect` — the core property.
4. Prove handler composition (nested handlers).
5. Model resume and prove at-most-once linearity.
6. Model Fail as zero-resume and prove Result equivalence.
7. Prove effect polymorphism soundness.
8. (Stretch) Model tail-resumptive classification and prove
   compilation equivalence.

### Phase 2.5: Vertical integration (during/after 0e)

1. Connect effect typing to the existing typing soundness theorems.
2. Prove that the full type+effect system is sound (the big theorem).
3. If evaluator semantics exist in Kea, extend evaluator soundness.

## Testing / Verification

- `lake build` must succeed with zero `sorry` at each milestone.
- MCP log entries for every theorem that touches runtime behavior.
- Rust proptest↔Lean theorem mapping maintained in a FORMAL.md.
- CI integration: `lake build` in Kea CI (separate job, non-blocking
  initially, blocking after Phase 1 completes).

## Definition of Done

### Phase 1

- `kea/formal/` exists with Lake project.
- All core type system modules migrated and extended for effect rows.
- All transferable Properties/ theorems re-proved.
- Zero `sorry`.
- MCP-first workflow operational against kea-mcp.

### Phase 2

- Effect declaration/operation typing modeled.
- Handler typing rule (§5.13) modeled and effect removal proved.
- Resume at-most-once proved.
- Fail/Result equivalence proved.
- Nested handler composition proved.
- Effect polymorphism soundness proved.
- Zero `sorry`.
- FORMAL.md mapping maintained.

## Non-Goals

- Formalizing codegen / MIR lowering (too implementation-specific).
- Formalizing the actor/concurrency model (Phase 3+ work).
- Formalizing memory model / ownership (depends on 0f stabilizing).
- Blocking implementation on formal proofs (formal work validates,
  doesn't gate).

## Progress

- 2026-02-26: Brief moved from `todo/` to `in-progress/` to start Phase 1 migration in parallel with 0d codegen work.
- 2026-02-26: Bootstrapped `formal/` in Kea by cannibalizing `/Users/chris/Projects/rill/formal`, renaming the Lean namespace target from `Rill` to `Kea`, and preserving the roadmap + MCP verification history baseline.
- 2026-02-26: `cd formal && lake build` passes in Kea after namespace-portability proof repairs in `SubstBridge`, `UnifyReflexive`, `PrecisionLeafParity`, and `ShapeConstructorParity` (warning-only simp lint remains).
- 2026-02-26: Repository guardrail check passes after formalization bootstrap (`mise run check`).
- 2026-02-26: Aligned core formal typing surface with `kea-types` effect rows (`Ty.functionEff`, `EffectRow`, `Kind`) and propagated constructor coverage through `Substitution`, `FreeVars`, `OccursCheck`, `Unify`, `Generalize`, `Typing`, plus proof repair in `SubstCompose`/`SubstBridge`/`SubstIdempotent`/`UnifyReflexive`.
- 2026-02-26: Added phase-1 WF scaffold modules (`WellFormed`, `WfSubstitution`, `WfRename`, `WfGeneralize`) and integrated them into `formal/Kea.lean`.
- 2026-02-26: Added `WfUnify` unifier-update WF lemmas (`bindTypeVar_ok_preserves_wf_range`, row bind variants) and centralized `Subst.WellFormedRange` + bind-preservation lemmas in `WfSubstitution` for shared reuse across follow-on unifier proofs.
- 2026-02-26: Added row/effect WF constructor helper lemmas in `WellFormed` (`closed`, `mkOpen`, `emptyClosed`, `emptyOpen`, `pure`) and extended `WfUnify` with `unifyRows`-shaped WF helpers (`subst_bindClosedRow_preserves_wf_range`, `subst_bindOpenRows_preserves_wf_range`) to reduce branch-local proof boilerplate.
- 2026-02-26: Extended `WfUnify` with state-level WF range transport lemmas (`SubstWellFormedRange` wrappers for `freshTypeVar`, `freshRowVar`, and non-`subst` record updates) plus state-level bind wrappers (`bindTypeVar_ok_preserves_substWellFormedRange`, closed/open row update variants) to support direct `unifyRows` branch proof reuse.
- 2026-02-26: Added `unifyRows`-branch-oriented WF wrappers in `WfUnify` that compose substitution + lacks + fresh-row updates (`bindClosedRow_update_with_lacks_preserves_substWellFormedRange`, `bindOpenRows_update_with_lacks_preserves_substWellFormedRange`, `freshOpenRows_update_with_lacks_preserves_substWellFormedRange`) for direct use in open/closed row branch proofs.
- 2026-02-26: Added `WfUnifyExtends` bridge module to package row-branch updates as combined contracts (`ExtendsRowBindings` + `SubstWellFormedRange`) and integrated it into the top-level formal import surface.
- 2026-02-26: Extended `WfUnifyExtends` with branch-shaped `unifyRows` combined contracts under existing idempotence preconditions (open-closed, closed-open, open-open fresh branch) so extension and WF-range obligations can be discharged together from one theorem surface.
- 2026-02-26: Added full-state open-open combined contract in `WfUnifyExtends` (covers `lacks` + `traitBounds` + fresh counters) so branch proofs can preserve both extension and WF-range across all non-`subst` state updates in one step.
- 2026-02-26: Added a preconditioned combined dispatcher (`unifyRows_success_update_extendsAndWf_idempotent`) with explicit WF-annotated branch-shape predicate (`UnifyRowsSuccessUpdateShapeWf`), mirroring `UnifyExtends` while returning extension + WF-range as one reusable contract.
- 2026-02-26: Added canonical contract naming/projection in `WfUnifyExtends` (`unifyRows_contract_extendsAndWf`, `unifyRows_extends_rowMap_preconditioned_of_contract_extendsAndWf`) plus shape projection (`unifyRowsSuccessUpdateShapeWf_implies_shape`) to align with existing `UnifyExtends` contract ergonomics.
- 2026-02-26: Added `unifyRows_contract_full_wf` in `WfUnifyExtends`, composing the new extension+WF-range contract with existing compat/WF swap-invariance (`CompatWFAgreeOnDomainLookupsAcyclic`) into one downstream theorem surface.
- 2026-02-26: Strengthened `WfGeneralize` with a non-mono instantiation WF theorem (`instantiate_preserves_wf_of_mapping_respects_ctx`) that lifts instantiation WF through the rename mapping when mapping outputs are known to respect target kind/row contexts.
- 2026-02-26: Refactored `WfGeneralize` instantiate-WF machinery with reusable mapping helpers (`instantiateTypeFold`, `instantiateRowFold`, `instantiateVarMapping`) and added a cleaner primary theorem surface (`instantiate_preserves_wf_of_instantiateVarMapping_respects_ctx`).
- 2026-02-26: Added `WfSubstitution` extension-monotonicity bridge (`Subst.wellFormedRange_of_extends`) so WF-range invariants can be transported backward across established substitution extension relations.
- 2026-02-26: Added projection lemmas in `WfUnifyExtends` to recover both (a) direct `stNext` WF-range and (b) legacy `unifyRows_contract_wf` assumptions from the WF-annotated branch-shape contract.
- 2026-02-26: Added direct projection from WF-annotated branch-shape assumptions to the legacy unsplit contract (`unifyRows_extends_rowMap_preconditioned_wf_of_shape_wf`), avoiding manual shape conversion at call sites.
- 2026-02-26: Added bundled `UnifyState` WF transport over non-`subst` updates (`substWellFormedRange_with_non_subst_fields`) and used it to simplify full-state open-open WF contract proofs in `WfUnifyExtends`.
- 2026-02-26: Added substitution extension helpers in `WfSubstitution` (`extends_bindType_if_unbound`, `extends_bindRow_if_unbound`) to bridge unbound-bind updates into `Subst.Extends`, supporting future WF-range transport and extension-composition proofs.
- 2026-02-26: Added a direct single-state combined contract for unbound closed-row bind updates in `WfUnifyExtends` (`closedBind_extendsAndWfRange_if_unbound`) to reduce precondition threading at branch-call sites.
- 2026-02-26: Added a direct single-state open-open combined contract for two unbound row binds in `WfUnifyExtends` (`openOpenBind_extendsAndWfRange_if_unbound_twice`) to mirror the existing two-bind extension helper while preserving WF-range in the same theorem.
- 2026-02-26: Added boilerplate-reduction helpers in `WfUnifyExtends`: shape constructors (`unifyRowsSuccessUpdateShapeWf_*`) and no-update combined-contract wrappers (`noUpdate_extendsAndWfRange`, `noUpdate_with_non_subst_fields_extendsAndWfRange`) for faster branch proof assembly.
- 2026-02-26: Added identity renaming utilities in `WfRename` (`VarMapping.id`, lookup simplifications, `respectsCtx_id`, and rename-id WF corollaries across Ty/Row/TyList/RowFields/EffectRow) to streamline instantiate/generalize proof setup.
- 2026-02-26: Added structural identity lemmas for renaming (`renameType_id_eq`, `renameRow_id_eq`, `renameTyList_id_eq`, `renameRowFields_id_eq`, `renameEffectRow_id_eq`) so identity mappings can be eliminated by rewriting during later WF proofs.
- 2026-02-26: Exposed instantiation mapping helpers in `WfGeneralize` (`instantiateTypeFold`, `instantiateRowFold`, `instantiateVarMapping`) and added an ergonomic combined theorem (`instantiate_preserves_wf`) that discharges WF from either monomorphic instantiation or a mapping-context witness.
- 2026-02-26: Added single-bind branch wrappers in `WfUnifyExtends` that jump directly to the full contract surface (extension + WF-range + compat/WF acyclic agreement) for open-closed and closed-open successful `unifyRows` updates.
- 2026-02-26: Added the open-open fresh-branch full-contract wrapper in `WfUnifyExtends` (`unifyRows_open_open_contract_full_wf_idempotent_fresh`), completing branch-level access to extension + WF-range + compat/WF acyclic agreement.
- 2026-02-26: Added explicit no-update full-contract wrapper in `WfUnifyExtends` (`noUpdate_contract_full_wf`) so the no-subst-update branch has the same extension+WF+compat contract shape as bind-update branches.
- 2026-02-26: Re-ran MCP-first row-branch probes on restarted `kea-mcp` (`reset_session` + `get_type`/`type_check`/`diagnose`) for `WfUnifyExtends` no-update/single-bind/open-open wrappers; outcomes matched expected success/error boundaries (logged in `formal/mcp-log.md`).
- 2026-02-26: Added `bindTypeVar`-success combined contracts in `WfUnifyExtends` (`bindTypeVar_ok_extendsAndWfRange`, `bindTypeVar_ok_with_non_subst_fields_extendsAndWfRange`, `bindTypeVar_ok_contract_full_wf`) to extend the WF contract layer beyond row-branch updates.
- 2026-02-26: Added `unify` var-left bridge + lifted contracts in `WfUnifyExtends` (`unify_var_left_eq_bindTypeVar`, `unify_var_left_ok_contract_full_wf`, `unify_var_left_ok_with_non_subst_fields_contract_full_wf`) so var-branch unifier successes discharge the same full WF contract surface without manual `bindTypeVar` rewrites.
- 2026-02-26: Added one-hop projection lemmas for var-left unifier bridge contracts in `WfUnifyExtends` (base + non-`subst` state variants), exposing extension/WF-range/acyclic facets directly from `unify_var_left_ok_*_contract_full_wf`.
- 2026-02-26: Added safe var-right unifier bridge wrappers in `WfUnifyExtends` (`unify_var_right_*_of_non_var`) including non-`subst` full-state contract surfaces, making the bridge layer symmetric while preserving branch-sound preconditions.
- 2026-02-26: Added WF-empty corollaries for well-founded row/effect-row substitution in `WfSubstitution` (`applySubstRowWF_empty_preserves_wf`, `applySubstEffectRowWF_empty_preserves_wf`) to complete empty-substitution WF coverage across effect-row forms.
- 2026-02-26: Added `TyList`/`RowFields` WF-preservation and empty-substitution lemmas in `WfSubstitution` (`applySubstTyList_preserves_wf_of_no_domain_vars`, `applySubstRowFields_preserves_wf_of_no_domain_vars`, `applySubstTyList_empty_preserves_wf`, `applySubstRowFields_empty_preserves_wf`) to close container-level WF baseline gaps.
- 2026-02-26: Added full-state `bindTypeVar` contract packaging in `WfUnifyExtends` (`bindTypeVar_ok_with_non_subst_fields_contract_full_wf`) so type-var bind success paths retain extension + WF-range + compat/WF-acyclic agreement under non-`subst` state updates.
- 2026-02-26: Added `bindTypeVar` WF transport wrappers in `WfUnify` for non-`subst` state updates (`bindTypeVar_ok_with_lacks_preserves_substWellFormedRange`, `bindTypeVar_ok_with_non_subst_fields_preserves_substWellFormedRange`) to reduce downstream state-proof boilerplate.
- 2026-02-26: Added `WfGeneralize` component-wise effect-row wrapper (`generalize_functionEff_preserves_wf_of_component_no_domain_vars`) so `Ty.functionEff` generalization can be consumed from split param/effect/return no-domain assumptions.
- 2026-02-26: Added projection lemmas for `bindTypeVar` full contracts in `WfUnifyExtends` (extension-only and WF-range-only, including non-`subst` state variants) to reduce contract-destruct boilerplate at call sites.
- 2026-02-26: Added `instantiate_functionEff_preserves_wf` in `WfGeneralize`, completing the pair of effect-row-focused `functionEff` wrappers across both `generalize` and `instantiate`.
- 2026-02-26: Added explicit `functionEff` WF substitution wrappers in `WfSubstitution` (`applySubst_functionEff_preserves_wf_of_component_no_domain_vars`, `applySubstWF_functionEff_preserves_wf_of_component_no_domain_vars`) so effect-row function types have direct fuel/WF-preservation surfaces (not only compat alias coverage).
- 2026-02-26: Added effect-row compat surface in `Substitution` (`applySubstEffectRowCompat`) and corresponding `WfSubstitution` lemmas (`applySubstEffectRowCompat_preserves_wf_of_no_domain_vars`, `applySubstEffectRowCompat_empty_preserves_wf`) to keep effect-row proof call sites aligned with compat substitution APIs.
- 2026-02-26: Added `TyList`/`RowFields` compat substitution aliases in `Substitution` (`applySubstTyListCompat`, `applySubstRowFieldsCompat`) and matching `WfSubstitution` lemmas (`*_preserves_wf_of_no_domain_vars`, `*_empty_preserves_wf`) to complete container-level compat WF coverage.
- 2026-02-26: Added acyclic-agreement projection lemmas for `bindTypeVar` full contracts in `WfUnifyExtends` (base + non-`subst` state variants), so extension/WF-range/compat facets are each available via one-hop projections.
- 2026-02-26: Added `functionEff` convenience wrappers in `WfGeneralize` for common entrypoints (`generalize_functionEff_empty_preserves_wf`, `instantiate_functionEff_mono_preserves_wf`, `instantiate_functionEff_preserves_wf_of_mapping_respects_ctx`) to reduce boilerplate at effect-row call sites.
- 2026-02-26: Added new packaging module `WfEffectRowLadder` and wired it into `Kea.lean`, exposing citable `functionEff` WF slices (`FunctionEffSubstWfSlice`, `FunctionEffGenInstWfSlice`) that bundle substitution + generalize + instantiate obligations.
- 2026-02-26: Added immediate-use specializations in `WfEffectRowLadder` (`functionEff_subst_wf_slice_empty`, `functionEff_gen_inst_wf_slice_mono`) for empty-substitution and monomorphic-instantiation effect-row workflows.
- 2026-02-26: Re-ran MCP probes for effect-row annotation boundaries (`reset_session` + `type_check`/`get_type`/`diagnose`): declared `-[Log]>` effects are preserved, pure control remains pure, and too-weak declared effect rows (e.g. `-[IO]>` with `Log.log`) are rejected; logged in `formal/mcp-log.md`.
- 2026-02-26: Extended `WfEffectRowLadder` with `bindTypeVar` contract packaging for `Ty.functionEff` (`FunctionEffBindTypeVarContractSlice`, `functionEff_bindTypeVar_contract_slice`), linking effect-row WF assumptions to extension + WF-range + compat/WF-acyclic guarantees after successful type-var binding.
- 2026-02-26: Added projection helpers for `FunctionEffBindTypeVarContractSlice` in `WfEffectRowLadder` (extension, WF-range, and acyclic-agreement projections) to reduce destructuring boilerplate for downstream effect-row proofs.
- 2026-02-26: Added full-state `bindTypeVar` contract packaging/projections for `Ty.functionEff` in `WfEffectRowLadder` (`FunctionEffBindTypeVarFullStateContractSlice`, `functionEff_bindTypeVar_full_state_*`) so non-`subst` state updates are covered by the same packaged effect-row contract surface.
- 2026-02-26: Added base/full-state conversion lemmas for `WfEffectRowLadder` bind-contract slices (`functionEff_bindTypeVar_full_state_slice_to_base`, `functionEff_bindTypeVar_base_slice_to_full_state`) and routed full-state projections through the shared base projection path.
- 2026-02-26: Added capstone bundle theorem in `WfEffectRowLadder` (`functionEff_wf_ladder_bundle_of_bind_success`) to expose substitution + generalize/instantiate + bind-contract slices together from one `Ty.functionEff` proof entrypoint.
- 2026-02-26: Added full-state capstone bundle theorem in `WfEffectRowLadder` (`functionEff_wf_ladder_bundle_of_bind_success_full_state`) so the same one-shot `functionEff` WF ladder packaging is available after non-`subst` `UnifyState` updates.
- 2026-02-26: Added one-hop bundle projection helpers in `WfEffectRowLadder` (base + full-state) so extension, WF-range, and compat/WF-acyclic obligations can be extracted directly from bundled `functionEff` assumptions without extra destructuring.
- 2026-02-26: Added named bundle contracts in `WfEffectRowLadder` (`FunctionEffWfLadderBundle`, `FunctionEffWfLadderBundleFullState`) with constructor/projection helpers, stabilizing a single theorem-surface name for downstream effect-row WF consumers.
- 2026-02-26: Completed named bundle projection coverage in `WfEffectRowLadder` with direct extension/WF/acyclic extractors (base + full-state), yielding a complete one-hop API from bundle assumptions to all unifier contract facets.
- 2026-02-26: Added `unify` var-left entry wrappers in `WfEffectRowLadder` (`functionEff_unify_var_left_*`) plus bundle constructors (`functionEff_wf_ladder_bundle_of_unify_var_left_success*`), allowing effect-row WF contract packaging to start from successful unifier var-branches (with explicit reduced-form branch preconditions).
- 2026-02-26: Refined `WfEffectRowLadder` var-left `unify` wrappers to discharge the constructor-mismatch BEq premise internally via `beqTy` reduction, removing that manual precondition from downstream call sites.
- 2026-02-26: Added symmetric var-right `unify` entry wrappers/bundle constructors in `WfEffectRowLadder` (`functionEff_unify_var_right_*`, including full-state variants), grounded in the new `WfUnifyExtends` non-var right-branch bridge.
- 2026-02-26: `cd formal && lake build` passes after full `functionEff` exhaustiveness repair in remaining Phase-1 core proofs.
- 2026-02-26: Added explicit WF effect-row bridge lemmas in `SubstBridge` (`applySubstEffectRowWF_noop`, `applySubstEffectRowWF_empty`) so effect rows have the same no-domain-vars/empty-substitution identity surface as rows.
- 2026-02-26: Added fuel-vs-WF effect-row bridge lemmas in `SubstBridge` (`applySubstEffectRowCompat_eq_applySubstEffectRowWF_of_no_domain_vars`, `applySubstEffectRow_empty_eq_applySubstEffectRowWF_empty`) and introduced `Substitution.applySubstEffectRow` helper to make the effect-row substitution boundary explicit.
- 2026-02-26: Added explicit `Ty.functionEff` compat-vs-WF constructor corollary (`applySubstCompat_functionEff_eq_applySubstWF_of_no_domain_vars`) to expose a named bridge surface for effectful function types.
- 2026-02-26: Added component-wise `Ty.functionEff` bridge corollary (`applySubstCompat_functionEff_eq_applySubstWF_of_component_no_domain_vars`) so downstream proofs can consume separate no-domain assumptions for params/effects/return without flattening free-var lists manually.
- 2026-02-26: Added explicit WF judgment layer (`Kea/WellFormed.lean`) and WF-preservation lemmas for both fuel and WF substitution under no-domain-vars preconditions (`Kea/Properties/WfSubstitution.lean`), including effect-row variants.
- 2026-02-26: Extended WF substitution lemma surface with empty-substitution preservation theorems for type/row/effect-row forms to stabilize the WF baseline API for downstream unification/generalization work.
- 2026-02-26: Added `applySubstCompat`/`applySubstRowCompat` WF-preservation lemmas so existing compat substitution call sites can consume the WF layer without changing substitution entry points.
- 2026-02-26: Added component-wise `functionEff` WF-preservation lemma for compat substitution (`applySubstCompat_functionEff_preserves_wf_of_component_no_domain_vars`) to align the WF API with effect-row function decomposition used in existing bridge proofs.
- 2026-02-26: Added first `generalize/instantiate` WF theorems (`Kea/Properties/WfGeneralize.lean`): no-domain-vars/empty-substitution WF preservation for `generalize`, plus monomorphic `instantiate` equality and WF preservation.
- 2026-02-26: Added WF preservation for renaming (`Kea/Properties/WfRename.lean`) with explicit mapping-context assumptions (`VarMapping.RespectsCtx`), covering type/row/type-list/row-fields/effect-row renaming as groundwork for polymorphic `instantiate` WF proofs.
- 2026-02-26: Phase-2 kickoff landed in `Kea/Properties/HandlerEffectRemoval.lean` with row-level handler elimination model (`EffectRow.handleRemove`) and first capstone theorem surface: `handle_removes_effect`, `handle_preserves_other_effects`, row-tail preservation, idempotence, and WF preservation.
- 2026-02-26: MCP probe sweep for handler elimination confirmed non-overlap behavior (`[IO, Log] --handle Log--> [IO]`, `[Log] --handle Log--> []`) and logged an overlap divergence: when handler-body effects overlap with residual effects, inference currently emits duplicate labels (e.g. inferred `()-[IO, IO]> ()`), which cannot be expressed in declared effect-row annotations.
- 2026-02-26: Continued Phase-2 on the spec path by adding normalized composition semantics in `HandlerEffectRemoval` (`RowFields.insertIfAbsent`, `RowFields.unionIdem`, `EffectRow.handleComposeNormalized`) and proving preconditioned composition theorems (`handle_adds_handler_effects`, `handle_preserves_other_effects_normalized`, `handle_removes_effect_normalized_of_handler_absent`, `handleComposeNormalized_preserves_wellFormed`).
- 2026-02-26: Extended normalized-composition coverage with nested same-target handler consequences (`nested_same_target_outer_removal_noop_of_inner_absent`, `nested_same_target_remains_absent_of_outer_absent`) plus composed row-tail preservation (`handleComposeNormalized_preserves_row_tail`).
- 2026-02-26: Added `Kea/Properties/ResumeLinearity.lean` scaffold for Phase-2 resume linearity (`ResumeUse` summary algebra, `combine` composition, exclusivity-preserving at-most-once lemmas, and named `resume_at_most_once` surface) and imported it via `formal/Kea.lean`.
- 2026-02-26: Strengthened `ResumeLinearity` with exact combine characterization (`resume_combine_atMostOnce_iff`) and branch-exclusivity corollaries (`resume_combine_atMostOnce_implies_one_side_zero`, `resume_combine_one_one_not_atMostOnce`) to directly support "resume not in both branches" style obligations.
- 2026-02-26: Added explicit branch/loop legality surfaces in `ResumeLinearity` (`ResumeUse.conditionalLegal`, `ResumeUse.loopLift`, `ResumeUse.loopLegal`) with corresponding iff/corollary lemmas, and re-probed `kea-mcp`: zero-resume handler clauses typecheck while sequential and both-branch double-resume cases are rejected with `E0012`.
- 2026-02-26: Added `Kea/Properties/HandlerTypingContracts.lean` as the first integration layer connecting normalized handler effect composition and resume-linearity obligations via a clause-level contract (`HandleClauseContract.wellTypedSlice`) plus bridge theorems (`wellTypedSlice_implies_handled_removed`, branch exclusivity, loop legality).
- 2026-02-26: Refined `Kea/Properties/HandlerTypingContracts.lean` with concrete premises (`thenEffects`, `clauseCoverageComplete`), explicit effect-result assembly (`resultEffectsCore`, `applyThenEffects`, `resultEffects`), no-reintroduction invariants, and resume-provenance extraction lemmas; `cd formal && lake build` passes.
- 2026-02-26: Added `Kea/Properties/EffectOperationTyping.lean` (imported via `formal/Kea.lean`) with effect declaration/operation-call scaffold (`EffectDecl`, `operationCallTyping`, `performOperationEffects`) and capstones `operationCallTyping_adds_declared_effect` + `capability_direct_call_sound`; `cd formal && lake build` passes.
- 2026-02-26: Re-probed runtime alignment for `capability_direct_call_sound` on latest `kea-mcp`: from `body : () -[Log, Trace]> ()`, handling `Trace` yields `run : () -[Log]> ()` and handling `Log` yields `run2 : () -[Trace]> ()` (both `diagnose` clean); divergence none.
- 2026-02-26: Extended `EffectOperationTyping` with WF transport (`performOperationEffects_preserves_wellFormed`) so effect-row updates from operation calls now compose directly with the WF formalization ladder; `cd formal && lake build` passes.
- 2026-02-26: Re-probed operation-call effect-row behavior on latest `kea-mcp`: `call_log` infers `() -[Log]> ()`, while explicit too-weak declaration (`fn bad() -[Trace]> Unit` with `Log.log`) rejects with `E0001`; aligns with `EffectOperationTyping` contract surfaces.
- 2026-02-26: Added `Kea/Properties/TailResumptiveClassification.lean` (imported via `formal/Kea.lean`) with `TailResumptiveClass`/`classifyClause` and capstones `tail_resumptive_classification` + `tail_resumptive_direct_call_sound` for the tail-resumptive fast-path contract surface; `cd formal && lake build` passes.
- 2026-02-26: Extended `TailResumptiveClassification` with named bundle packaging (`TailResumptiveBundle`, `tail_resumptive_bundle_of_wellTyped`, `tail_resumptive_bundle_notInvalid`) so downstream proofs can consume tail-resumptive classification/provenance in one contract surface; `cd formal && lake build` passes.
- 2026-02-26: Re-probed tail-resumptive runtime alignment on latest `kea-mcp`: with `body : () -[Log]> ()`, both `run_no_then` and identity-`then` `run_then` infer `() -> ()` and diagnose clean, matching `tail_resumptive_direct_call_sound`.
- 2026-02-26: Added `Kea/Properties/TailCapabilityComposition.lean` (imported via `formal/Kea.lean`) to compose operation-call capability preservation with tail-resumptive equivalence (`tail_resumptive_eligible_capability_direct_call_sound`, plus a well-typed-clause wrapper); `cd formal && lake build` passes.
- 2026-02-26: MCP probe on handled-absent resumptive shape (`handle Log.log(1)` with `Trace` clause) rejects with `E0001` as expected for non-well-typed declarations (handler does not eliminate `Log`), so composition claims remain precondition-gated to well-typed clauses.
- 2026-02-26: Added `Kea/Properties/FailResultContracts.lean` and imported it via `formal/Kea.lean`; introduced Fail-specialized contract surfaces (`failAsZeroResume`, `resultLowering`, `FailResultContract`) with capstone consequences (`failResultContract_sound`, `failResultContract_loopLegal`); `cd formal && lake build` passes.
- 2026-02-26: Extended `FailResultContracts` with explicit function-type lowering/equivalence surfaces (`lowerFailEffects`, `lowerFailFunctionType`, `failResultFunctionEquivalent`) and preservation/removal lemmas (`lowerFailEffects_*`, `lowerFailFunctionType_noop_effect_of_absent`, `failResultFunctionEquivalent_implies_result_return`); `cd formal && lake build` passes.
- 2026-02-26: Added `Kea/Properties/EffectPolymorphismSoundness.lean` and imported it via `formal/Kea.lean`; introduced polymorphic effect-row soundness contracts (`rowTailStable`, `labelsPreservedExcept`, `EffectPolyFailLoweringContract`) with capstones (`lowerFailEffects_effectPoly_sound`, `effectPolyFailLowering_sound`, `effectPolyFailLowering_noop_if_fail_absent`); `cd formal && lake build` passes.
- 2026-02-26: Extended `EffectPolymorphismSoundness` with concrete handler-typing schema bridges (`EffectPolyHandlerSchema`, `effectPolyHandlerSchema_sound`, `effectPolyHandlerSchema_noop_if_fail_absent`) so `wellTypedSlice` + Fail-zero-resume premises now project directly into polymorphic function lowering guarantees; `cd formal && lake build` passes.
- 2026-02-26: Re-probed on `kea-mcp` after fix `cbb70b3`: Fail-absent `catch` now rejects with `E0012` (`expression cannot fail; catch is unnecessary`), while Fail-present and higher-order Fail-lowering probes remain aligned; divergence closed in `formal/mcp-log.md`.
- 2026-02-26: Added catch-admissibility formal surfaces in `FailResultContracts` (`catchAdmissible`, `catchUnnecessary`, exclusivity lemmas) and propagated them into `EffectPolymorphismSoundness` with precondition-gated wrappers (`effectPolyFailLowering_sound_of_catchAdmissible`, `catchUnnecessary_implies_no_admissible_poly_lowering`, schema variants); `cd formal && lake build` passes.
- 2026-02-26: Added runtime-aligned admissible wrappers in `EffectPolymorphismSoundness` (`AdmissibleEffectPolyFailLoweringContract`, `AdmissibleEffectPolyHandlerSchema`) and capstone entrypoints (`admissibleEffectPolyFailLowering_sound`, `admissibleEffectPolyHandlerSchema_sound`, `admissibleEffectPolyHandlerSchema_not_unnecessary`) so downstream usage is constrained to Fail-present `catch` cases by construction; `cd formal && lake build` passes.
- 2026-02-26: Added direct premise adapters in `EffectPolymorphismSoundness` (`mkAdmissibleEffectPolyFailLoweringContract`, `mkAdmissibleEffectPolyHandlerSchema`, plus `*_sound_of_premises`) so handler typing assumptions map to admissible capstones without manual structure assembly; `cd formal && lake build` passes.
- 2026-02-26: Added one-hop admissible projection helpers in `EffectPolymorphismSoundness` for both contracts and schemas (`*_rowTailStable`, `*_preserves_nonFail`, `*_failRemoved*`) to expose each guarantee independently from a single admissible assumption; `cd formal && lake build` passes.
- 2026-02-26: Added named admissible bundle contracts in `EffectPolymorphismSoundness` (`AdmissibleEffectPolyLoweringBundle`, `AdmissibleEffectPolyHandlerBundle`) with bundle constructors/projections (`admissibleEffectPoly*_bundle_*`) for stable one-name capstone consumption; `cd formal && lake build` passes.
- 2026-02-26: Added admissibility partition lemmas in `FailResultContracts` (`catchAdmissible_implies_not_unnecessary`, `catchAdmissible_xor_unnecessary`) and branch extractors in `EffectPolymorphismSoundness` (`admissibleEffectPoly*_*_admissibility_branch`) so runtime branch classification is explicit in theorem surfaces; `cd formal && lake build` passes.
- 2026-02-26: Added `Kea/Properties/CatchTypingBridge.lean` (imported via `formal/Kea.lean`) with a judgment-shaped premise bundle (`CatchTypingJudgment`) and direct theorem adapters (`catchTypingJudgment_sound`, row-tail/non-Fail projections, admissibility branch) into admissible effect-polymorphism capstones; `cd formal && lake build` passes.
- 2026-02-26: Extended `CatchTypingBridge` with judgment-level named bundle ergonomics (`CatchTypingBundle`, `catchTypingJudgment_bundle`, and `catchTypingJudgment_bundle_*` projections) for one-name consumption of clause-removal and lowered-effect guarantees; `cd formal && lake build` passes.
- 2026-02-26: Added direct premise adapters in `CatchTypingBridge` (`mkCatchTypingJudgment`, `catchTypingJudgment_sound_of_premises`, noncomputable `catchTypingJudgment_bundle_of_premises`) to enable judgment-free entry into the bridge capstones; `cd formal && lake build` passes.
- 2026-02-26: Added one-hop `of_premises` projections in `CatchTypingBridge` (`catchTypingJudgment_rowTailStable_of_premises`, `catchTypingJudgment_preserves_nonFail_of_premises`, and bundle-facet helpers) so raw-premise call sites can consume targeted guarantees directly; `cd formal && lake build` passes.
- 2026-02-26: Extended `CatchTypingBridge` with combined/classified premise surfaces (`CatchTypingCapstoneOutcome`, `catchTypingJudgment_capstone_of_premises`, `catchTypingJudgment_classify_of_premises`) plus Fail-presence/absence wrappers (`catchTypingJudgment_capstone_of_fail_present`, `catchTypingUnnecessary_of_fail_absent`) to match the higher-order runtime-aligned entry pattern; `cd formal && lake build` passes.
- 2026-02-26: Re-probed on latest restarted MCP binary: higher-order typed-Fail catch case now aligns (`(() -[Fail(String), Log]> Int) -[Log]> Result(Int, String)`), first-order typed case remains aligned, and fail-absent case still rejects with `E0012`; divergence closed in `formal/mcp-log.md`.
- 2026-02-26: Added `Kea/Properties/HigherOrderCatchContracts.lean` and imported it via `formal/Kea.lean`; introduced higher-order-specialized theorem surfaces (`higherOrderCatchType`, `HigherOrderCatchTypingJudgment`, soundness/admissibility theorems) so post-fix higher-order behavior is represented directly in formal APIs; `cd formal && lake build` passes.
- 2026-02-26: Extended `HigherOrderCatchContracts` with direct raw-premise adapters (`higherOrderCatchTypingJudgment_sound_of_premises`, `higherOrderCatchTypingJudgment_admissibility_branch_of_premises`) to avoid manual judgment assembly at higher-order call sites; `cd formal && lake build` passes.
- 2026-02-26: Added higher-order named bundle ergonomics in `HigherOrderCatchContracts` (`HigherOrderCatchBundle`, `higherOrderCatchTypingJudgment_bundle`, projection helpers, and `higherOrderCatchTypingJudgment_bundle_of_premises`) for stable one-name capstone consumption at higher-order call sites; `cd formal && lake build` passes.
- 2026-02-26: Added one-hop higher-order bundle `of_premises` projections in `HigherOrderCatchContracts` (`higherOrderCatchTypingJudgment_bundle_clauseFailRemoved_of_premises`, `*_rowTailStable_of_premises`, `*_preserves_nonFail_of_premises`) so raw-premise entrypoints expose targeted guarantees directly; `cd formal && lake build` passes.
- 2026-02-26: Added higher-order combined capstone `higherOrderCatchTypingJudgment_capstone_of_premises` (plus `higherOrderCatchTypingJudgment_bundle_failRemoved_of_premises`) so one raw-premise theorem now yields clause Fail removal, lowered-row guarantees, and admissibility branch facts together; `cd formal && lake build` passes.
- 2026-02-26: Added higher-order presence/absence entry wrappers (`higherOrderCatchTypingJudgment_capstone_of_fail_present`, `higherOrderCatchUnnecessary_of_fail_absent`) so consumers can enter the runtime-aligned capstone path directly from Fail-label evidence; `cd formal && lake build` passes.
- 2026-02-26: Added higher-order single-entry classification over `HigherOrderCatchCapstoneOutcome` (`higherOrderCatchTypingJudgment_classify_of_premises`) so raw typing premises now produce either full capstone consequences or the `catchUnnecessary` branch without a separate admissibility assumption; `cd formal && lake build` passes.
- **Next:** continue full Phase-2 runtime-aligned theorem packaging (including higher-order admissible catch paths) now that this regression is closed.
