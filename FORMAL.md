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
- **Phase 1 (active):** `WfUnifyExtends` now includes a direct `unify` var-left bridge (`unify_var_left_eq_bindTypeVar`) and lifted full-contract wrappers (`unify_var_left_ok_*_contract_full_wf`), so WF contracts can be discharged directly from var-branch unifier successes.
- **Phase 1 (active):** `WfUnifyExtends` now includes one-hop projections for the var-left unifier bridge contracts (base + non-`subst` state variants), exposing extension, WF-range, and acyclic compat/WF facets directly.
- **Phase 1 (active):** `WfUnifyExtends` now also includes a safe var-right bridge under explicit non-var preconditions (`unify_var_right_*_of_non_var`), with both base and non-`subst` full-contract wrappers.
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
- **Phase 1 (active):** Added `Kea/Properties/WfEffectRowLadder.lean` and imported it in `Kea.lean`; it packages effect-row `functionEff` WF obligations into citable slices (`FunctionEffSubstWfSlice`, `FunctionEffGenInstWfSlice`) spanning substitution, generalize, and instantiate.
- **Phase 1 (active):** `WfEffectRowLadder` now includes direct specializations (`functionEff_subst_wf_slice_empty`, `functionEff_gen_inst_wf_slice_mono`) for immediate empty-substitution and monomorphic instantiate use.
- **Phase 1 (active):** `WfEffectRowLadder` now includes a unifier-success contract slice for `Ty.functionEff` (`FunctionEffBindTypeVarContractSlice`, `functionEff_bindTypeVar_contract_slice`) linking effect-row WF premises to `bindTypeVar` extension/WF/acyclic-agreement guarantees.
- **Phase 1 (active):** `WfEffectRowLadder` now includes projection helpers for the `FunctionEffBindTypeVarContractSlice` (extension-only, WF-range-only, and acyclic-agreement) so packaged assumptions can be consumed directly.
- **Phase 1 (active):** `WfEffectRowLadder` now also provides full-state `bindTypeVar` contract packaging/projections (`FunctionEffBindTypeVarFullStateContractSlice` and `functionEff_bindTypeVar_full_state_*`) for non-`subst` state updates.
- **Phase 1 (active):** Added explicit conversion lemmas between base and full-state `functionEff` bind-contract slices (`functionEff_bindTypeVar_full_state_slice_to_base`, `functionEff_bindTypeVar_base_slice_to_full_state`) so either surface can be used interchangeably.
- **Phase 1 (active):** Added capstone bundle theorem `functionEff_wf_ladder_bundle_of_bind_success` to export substitution, generalize/instantiate, and bind-contract slices from one `functionEff` entrypoint.
- **Phase 1 (active):** Added full-state capstone bundle theorem `functionEff_wf_ladder_bundle_of_bind_success_full_state`, lifting the one-shot `functionEff` WF ladder packaging to the non-`subst` state-update surface.
- **Phase 1 (active):** `WfEffectRowLadder` now includes one-hop projection helpers from both bundle theorems (base + full-state), including direct extraction of extension, WF-range, and compat/WF-acyclic guarantees from a single packaged assumption.
- **Phase 1 (active):** `WfEffectRowLadder` now exposes named bundle contracts (`FunctionEffWfLadderBundle`, `FunctionEffWfLadderBundleFullState`) with constructor/projection helpers, so downstream proofs can depend on stable one-name theorem surfaces rather than raw conjunction shapes.
- **Phase 1 (active):** Named bundle contracts now include direct extension/WF/acyclic projection lemmas (base + full-state), giving a complete one-hop API from a bundle assumption to each unifier contract facet.
- **Phase 1 (active):** `WfEffectRowLadder` now also supports var-left `unify` entrypoints (`functionEff_unify_var_left_*`) and corresponding one-shot bundle constructors, so effect-row WF contracts can start from successful `unify` var-branches as well as direct `bindTypeVar`.
- **Phase 1 (active):** Var-left `unify` entry wrappers in `WfEffectRowLadder` now discharge the constructor-mismatch BEq premise internally (`beqTy` reduction), keeping downstream theorem calls on semantic WF assumptions only.
- **Phase 1 (active):** `WfEffectRowLadder` now includes symmetric var-right `unify` entry wrappers/bundles (`functionEff_unify_var_right_*`, including full-state variants), backed by the new non-var right-branch bridge.
- **Phase 1 (active):** M2 compat-first bridge refactor is now complete in `Kea/Properties/UnifyExtends.lean` (`unifyRows_preconditioned_contract_compat_first`), with `unifyRows_extends_rowMap_preconditioned_wf_split` routed through the compat-first layer.
- **Phase 1 (active):** M4 weak-hook app-equality bridge target is now closed in `Kea/Typing.lean` via the contract theorem family (`app_unify_result_eq_of_unify_success_contract_succ` and specializations) built on `AppUnifyNoopDomain` + resolved-shape packaging.
- **Phase 1 (active):** M4 DataFrame-verb typing follow-up is explicitly scoped out for Kea (tracked as N/A in `formal/ROADMAP.md`); remaining M4 scope is principal-typing extension on the Kea core language.
- **Phase 1 (active):** Added a packaged preconditioned principal-typing slice in `Kea/Typing.lean` (`PrincipalTypingSlicePreconditioned`, `principalTypingSlicePreconditioned_of_success`) to export determinism + declarative uniqueness + `inferExpr` agreement from one successful `inferExprUnify` run.
- **Phase 1 (active):** Added a hook-free no-unify principal/equivalence surface in `Kea/Typing.lean` (`inferExprUnify_complete_no_unify_branches`, `inferFieldsUnify_complete_no_unify_branches`, `inferExprUnify_ok_iff_inferExpr_no_unify_branches`, `inferFieldsUnify_ok_iff_inferFields_no_unify_branches`) with combined packaging in `PrincipalTypingNoUnifySlices`.
- **Phase 1 (active):** Added a no-unify bridge back into the preconditioned principal bundle (`principalTypingSlicePreconditioned_of_success_no_unify`), making hook assumptions vacuous on the no-unify fragment while preserving the same bundle API.
- **Phase 1 (active):** Added bundled-hook API entrypoints (`UnifyHookPremises`, `principalTypingSlicePreconditioned_of_success_from_bundle`, `principalTypingSlicePreconditioned_of_success_no_unify_from_bundle`) so principal bundle consumers can pass one hook package instead of separate app/proj assumptions.
- **Phase 1 (active):** Added core declarative principality packaging for syntax-directed inference (`hasType_unique`, `inferExpr_principal`, `PrincipalTypingSliceCore`, `principalTypingSliceCore_of_infer`) to expose a hook-free principal baseline on the core typing judgment itself.
- **Phase 1 (active):** Added no-unify success bridges from `inferExprUnify`/`inferFieldsUnify` into core principal packages (`principalTypingSliceCore_of_unify_success_no_unify`, `principalFieldTypingSliceCore_of_unify_success_no_unify`) so successful hook-free unify runs map directly to principal declarative slices.
- **Phase 1 (active):** Added a core-principal-to-preconditioned bridge (`principalTypingSlicePreconditioned_of_success_of_core_principal`) and routed the no-unify preconditioned theorem through it, reducing duplicated proof obligations and making hook assumptions explicitly vacuous once core principality is established.
- **Phase 1 (active):** Added the converse preconditioned-to-core bridge (`principalTypingSliceCore_of_preconditioned_success`, plus bundle entrypoint) so successful preconditioned inference runs can project directly to the core principal package.
- **Phase 1 (active):** Added a packaged no-unify bridge bundle (`PrincipalNoUnifyBridgeBundle`, constructors from direct hooks and hook bundles) that exports both core and preconditioned principal consequences from one successful no-unify run.
- **Phase 1 (active):** Added full field-side preconditioned principality parity (`inferFieldsUnify_deterministic`, `inferFieldsUnify_row_unique_preconditioned`, `PrincipalFieldTypingSlicePreconditioned`) with direct/bundle/no-unify/core-bridge entrypoints, mirroring the expression principal theorem stack.
- **Phase 1 (active):** Added packaged no-unify field bridge exports (`PrincipalFieldNoUnifyBridgeBundle`, direct and hook-bundle constructors) so one successful no-unify `inferFieldsUnify` run yields both core and preconditioned field principal packages.
- **Phase 1 (active):** Added the converse preconditioned-to-core field bridge (`principalFieldTypingSliceCore_of_preconditioned_success`, plus bundle entrypoint), completing expression/field symmetry for principal bridge directions.
- **Phase 1 (active):** Added a combined no-unify bridge slice capstone (`PrincipalNoUnifyBridgeSlices`, `principalNoUnifyBridgeSlices_proved`) that packages both expression and field no-unify bridge APIs into one proved theorem surface.
- **Phase 1 (active):** Added successful-run equivalence bridges between preconditioned and core principal slices (expression + field, direct and hook-bundle variants), tightening the M4 boundary to explicit `↔` contracts at fixed successful runs.
- **Phase 1 (active):** Added combined successful-run preconditioned↔core capstone packaging (`PrincipalPreconditionedCoreIffSlices`, `principalPreconditionedCoreIffSlices_proved`) for expression+field principality under bundled hooks.
- **Phase 1 (active):** Added one-hop projection helpers from the combined capstones (`principalNoUnifyBridgeSlices_expr/field`, `principalPreconditionedCoreIffSlices_expr/field`) so downstream proofs can consume expression or field slices directly.
- **Phase 1 (active):** Added top-level principal boundary suite packaging (`PrincipalBoundaryBridgeSuite`, `principalBoundaryBridgeSuite_proved`) with one-hop projections for no-unify and preconditioned↔core branches across expressions and fields.
- **Phase 1 (active):** Added suite-based convenience entrypoints (`principalNoUnifyCoreExpr/Field_of_success_via_suite`, `principalNoUnifyPreconditionedExpr/Field_of_success_via_suite`) for direct extraction of core/preconditioned principality from successful no-unify runs.
- **Phase 1 (active):** Added suite-based successful-run conversion wrappers in both directions (`principalCore*/principalPreconditioned*_*_via_suite`) for expressions and fields, making preconditioned↔core transport one-step at call sites.
- **Phase 1 (active):** Added suite coherence lemmas (`principalBoundaryBridgeSuite_noUnify_*_coherent_*`) showing the no-unify bundle witnesses and preconditioned↔core equivalence witnesses inter-derive each other for expressions and fields.
- **Phase 1 (active):** Added no-unify principal capstone packaging (`PrincipalBoundaryNoUnifyExprCapstone`, `PrincipalBoundaryNoUnifyFieldCapstone`, `PrincipalBoundaryNoUnifyCapstoneSlices`) with suite-derived constructors and one-hop projections/coherence wrappers so one successful no-unify run exposes both witnesses and their successful-run equivalence surface.
- **Phase 1 (active):** Added one-hop projection helpers from the combined no-unify capstone slices (`principalBoundaryNoUnifyCapstoneSlices_expr_*`, `principalBoundaryNoUnifyCapstoneSlices_field_*`) for direct extraction of core/preconditioned/`↔` witnesses at expression and field call sites.
- **Phase 1 (active):** Added unbundled-hook and hook-bundle capstone entrypoints (`principalBoundaryNoUnifyExpr/FieldCapstone_of_success`, `principalBoundaryNoUnifyExpr/FieldCapstone_of_success_from_hook_bundle`) so no-unify capstone construction works uniformly with either hook-passing style.
- **Phase 1 (active):** Added fixed-run hook-transport/irrelevance theorems for preconditioned principality (`principalTypingSlicePreconditioned_transport_hooks_of_success`, `principalTypingSlicePreconditioned_hook_irrelevant_of_success`, field analogues), making hook-witness independence explicit once inference success is fixed.
- **Phase 1 (active):** Added combined hook-irrelevance slice packaging (`PrincipalPreconditionedHookIrrelevanceSlices`, `principalPreconditionedHookIrrelevanceSlices_proved`) with expression/field one-hop projections for direct fixed-run hook-independence consumption.
- **Phase 2 (next):** Kea-specific effect typing and handler theorems.
- **Phase 2 (active):** Added `Kea/Properties/HandlerEffectRemoval.lean` with a first handler-elimination core model (`EffectRow.handleRemove`) and capstone theorem surfaces (`handle_removes_effect`, `handle_preserves_other_effects`, row-tail/WF preservation, idempotence).
- **Phase 2 (active):** Latest MCP re-probe confirms overlap normalization closure (`[Trace] ∪ [Trace] = [Trace]`, prior duplicate-label regression shapes now infer normalized rows), so runtime behavior aligns with spec idempotent union on current handler probes.
- **Phase 2 (active):** Formal handler-composition proofs proceed on spec-normalized idempotent union via `EffectRow.handleComposeNormalized` (remove handled effect, then idempotent union with handler-body effects), and current MCP probes now confirm implementation-side overlap dedup for the tracked cases.
- **Phase 2 (active):** Added nested same-target handler consequences on the normalized model (`nested_same_target_outer_removal_noop_of_inner_absent`, `nested_same_target_remains_absent_of_outer_absent`) and row-tail preservation for composed handlers.
- **Phase 2 (active):** Added `Kea/Properties/HandlerAbsentEffectNoop.lean` with closed-row-aware no-op contracts (`handleComposeClosedAware`, `handle_absent_effect_noop`) to model absent-effect handler no-op behavior explicitly.
- **Phase 2 (active):** Added `Kea/Properties/HandlerClosedAwareContracts.lean` to lift absent-effect no-op semantics into clause-level APIs (`resultEffectsCoreClosedAware`, `resultEffectsClosedAware`, normalized/closed-case bridge theorems), then extended it with branch-classification + bundle surfaces (`resultEffectsCoreClosedAware_branch_classification`, `ClosedAwareCoreBundle`, `closedAwareCoreBundle_of_classification`) and typing-facing consequences (`resultEffectsClosedAware_preserves_row_tail`, `wellTypedSlice_implies_handled_removed_closedAware`) for direct downstream composition.
- **Phase 2 (active):** `HandlerClosedAwareContracts` now provides a shared Phase-2 entry API (`handleComposeClosedAware_removes_target_of_handler_absent`, `handleComposeClosedAware_preserves_row_tail`, `ClosedAwareResultBundle`, `closedAwareResultBundle_of_wellTyped`, `wellTypedSlice_implies_handled_removed_legacy_via_closedAware`) so downstream capstones can consume one closed-aware contract surface.
- **Phase 2 (active):** Added `Kea/Properties/ResumeLinearity.lean` as a no-`sorry` scaffold for `resume_at_most_once` reasoning (`ResumeUse`, saturating composition, exclusivity-preserving lemmas, and named `resume_at_most_once` contract surface).
- **Phase 2 (active):** `ResumeLinearity` now includes exact composition characterization (`resume_combine_atMostOnce_iff`) and exclusivity corollaries (`resume_combine_atMostOnce_implies_one_side_zero`, `resume_combine_one_one_not_atMostOnce`) for branch-level linearity reasoning.
- **Phase 2 (active):** MCP re-probes confirm runtime `E0012` enforcement aligns with the resume summary model: zero-resume clauses typecheck; sequential and both-branch double-resume cases are rejected.
- **Phase 2 (active):** Added `Kea/Properties/HandlerTypingContracts.lean` to integrate effect-removal and resume-linearity tracks through a clause-level contract surface (`wellTypedSlice`) with bridge theorems for handled-effect removal, branch exclusivity, and loop legality.
- **Phase 2 (active):** Refined `HandlerTypingContracts` from abstract summaries to concrete contract premises (`thenEffects`, `clauseCoverageComplete`) with explicit result-effect assembly (`resultEffectsCore`/`applyThenEffects`/`resultEffects`), non-reintroduction guarantees, and resume-provenance extraction from linearity assumptions.
- **Phase 2 (active):** Added `Kea/Properties/EffectOperationTyping.lean` to model effect declarations and operation-call typing (`EffectDecl`, `operationCallTyping`, `performOperationEffects`) with capstones `operationCallTyping_adds_declared_effect` and `capability_direct_call_sound`.
- **Phase 2 (active):** MCP re-probes for cross-handled capability calls now align with `EffectOperationTyping`: handling `Trace` from `-[Log, Trace]>` leaves `-[Log]`, and handling `Log` leaves `-[Trace]` (diagnostics clean).
- **Phase 2 (active):** `EffectOperationTyping` now includes WF transport (`performOperationEffects_preserves_wellFormed`), linking operation-call row updates to the Phase-1/2 well-formedness track.
- **Phase 2 (active):** MCP operation-call probes align with the declaration/update model: `call_log` infers `() -[Log]> ()`, and explicit too-weak annotations (e.g. `-[Trace]` body `Log.log`) are rejected with `E0001`.
- **Phase 2 (active):** `EffectOperationTyping` now includes named operation-call bundles (`OperationCallBundle`, `operationCallBundle_of_typing`) so declaration witness, effect-addition, and row-tail stability are available from one theorem surface.
- **Phase 2 (active):** Added `Kea/Properties/TailResumptiveClassification.lean` to classify clause resume shapes (`TailResumptiveClass`, `classifyClause`) with capstones `tail_resumptive_classification` and `tail_resumptive_direct_call_sound`.
- **Phase 2 (active):** `TailResumptiveClassification` now includes named bundle packaging (`TailResumptiveBundle`, `tail_resumptive_bundle_of_wellTyped`) with a one-hop non-invalid projection (`tail_resumptive_bundle_notInvalid`).
- **Phase 2 (active):** `TailResumptiveClassification` now includes closed-aware direct-call equivalence (`directCallEquivalentClosedAware`, `tail_resumptive_direct_call_sound_closedAware`) to align tail-resumptive fast-path contracts with the shared closed-aware handler surface.
- **Phase 2 (active):** `TailResumptiveClassification` now packages closed-aware fast-path reasoning in a named bundle (`TailResumptiveClosedAwareBundle`, `tail_resumptive_closedAware_bundle_of_wellTyped`) with one-hop eligible projection.
- **Phase 2 (active):** MCP probe alignment now covers the tail-resumptive slice: `run_no_then` and identity-`then` `run_then` both infer `() -> ()` with clean diagnostics, matching the direct-call contract surface.
- **Phase 2 (active):** Added `Kea/Properties/TailCapabilityComposition.lean` to compose operation-call capability preservation with tail-resumptive equivalence (`tail_resumptive_eligible_capability_direct_call_sound`, well-typed wrapper included).
- **Phase 2 (active):** `TailCapabilityComposition` now includes a general well-typed lift (`resultEffects_preserves_core_label_true`, `wellTyped_capability_direct_call_sound`) so capability preservation composes through full clause result effects (including `then`-union), with the tail-resumptive theorem retained as a corollary surface.
- **Phase 2 (active):** `TailCapabilityComposition` now also has named bundle packaging (`TailCapabilityBundle`, `tailCapabilityBundle_of_wellTyped`) with one-hop projections for full-result capability preservation under well-typed boundaries.
- **Phase 2 (active):** `TailCapabilityComposition` now also exposes closed-aware capability surfaces (`wellTyped_capability_direct_call_sound_closedAware`, `TailCapabilityClosedAwareBundle`, `tailCapabilityClosedAwareBundle_of_wellTyped`) so capability-preservation reasoning aligns with the shared closed-aware entry API.
- **Phase 2 (active):** `TailCapabilityComposition` now includes closed-aware tail-resumptive fast-path corollaries (`tail_resumptive_eligible_capability_direct_call_sound_closedAware`, `tail_resumptive_wellTyped_capability_direct_call_sound_closedAware`) and routes closed-aware `notInvalid` through `TailResumptiveClosedAwareBundle`.
- **Phase 2 (active):** Added `Kea/Properties/NestedHandlerCompositionContracts.lean` with explicit nested same-target theorem surfaces (`nested_handlers_compose`, row-tail/other-label preservation, and `NestedHandlerBundle` packaging).
- **Phase 2 (active):** Extended `NestedHandlerCompositionContracts` with closed-aware nested capstones (`nestedComposeClosedAware`, `nested_handlers_compose_closedAware`, `nested_handlers_compose_closedAware_row_tail`, `NestedHandlerClosedAwareBundle`) aligned to the shared closed-aware entry API.
- **Phase 2 (active):** MCP probe for a valid nested same-target shape (`nested_same` with inner handle bound then handled again) infers `() -> ()` with clean diagnostics, aligning with the nested composition contract boundary.
- **Phase 2 (active):** After phantom-IO fix (commits `746a4cb`, `9812380`) and MCP restart, handled-absent closed-row probes now align with no-op semantics: mismatched handlers preserve body effects (`probe_log : () -[Log]> ()`, `probe_trace : () -[Trace]> ()`) with clean diagnostics.
- **Phase 2 (active):** Added `Kea/Properties/FailResultContracts.lean`, specializing handler contracts to Fail-as-zero-resume and Result-lowering (`resultLowering`, `FailResultContract`, `failResultContract_sound`, `failResultContract_loopLegal`) to start the Fail/Result equivalence track.
- **Phase 2 (active):** `FailResultContracts` now also exports a closed-aware clause-output capstone (`failResultContract_sound_closedAware`) alongside the legacy `resultEffects` contract.
- **Phase 2 (active):** Extended `FailResultContracts` with explicit lowering/equivalence slices (`lowerFailEffects`, `lowerFailFunctionType`, `failResultFunctionEquivalent`) plus preservation/removal lemmas to bridge from contract-level Fail handling into function-type `Result` lowering.
- **Phase 2 (active):** Added `Kea/Properties/FailResultEquivalence.lean` with explicit `fail_result_equivalence` theorem/bundle surfaces (including catch-premise adapters), so the Fail/Result equivalence target now has a named capstone API.
- **Phase 2 (active):** Added `Kea/Properties/EffectPolymorphismSoundness.lean` with reusable soundness contracts for Fail lowering over polymorphic effect rows (`rowTailStable`, `labelsPreservedExcept`, `effectPolyFailLowering_sound`, no-op-if-absent), proving Fail removal while preserving non-Fail labels and row tails.
- **Phase 2 (active):** `EffectPolymorphismSoundness` now includes concrete handler-schema bridges (`EffectPolyHandlerSchema`, `effectPolyHandlerSchema_sound`, `effectPolyHandlerSchema_noop_if_fail_absent`) linking `wellTypedSlice` + Fail-zero-resume premises to polymorphic function-type lowering guarantees.
- **Phase 2 (active):** Divergence on Fail-absent `catch` is now closed (runtime now rejects with `E0012`: `expression cannot fail; catch is unnecessary`), so no-op-if-absent theorem claims are aligned as vacuous runtime cases rather than pending implementation fix.
- **Phase 2 (active):** Added explicit catch-admissibility contracts (`catchAdmissible`, `catchUnnecessary`) and precondition-gated effect-polymorphism wrappers (`effectPolyFailLowering_sound_of_catchAdmissible`, `catchUnnecessary_implies_no_admissible_*`), making the `E0012` fail-absent runtime behavior first-class in the formal theorem surface.
- **Phase 2 (active):** Added runtime-aligned admissible contract/schema wrappers (`AdmissibleEffectPolyFailLoweringContract`, `AdmissibleEffectPolyHandlerSchema`) and capstone entrypoints (`admissibleEffectPolyFailLowering_sound`, `admissibleEffectPolyHandlerSchema_sound`) so downstream proofs can consume only `catch`-admissible (`Fail`-present) cases.
- **Phase 2 (active):** Added premise-to-capstone adapters in `EffectPolymorphismSoundness` (`mkAdmissibleEffectPoly*`, `*_sound_of_premises`) to eliminate manual structure assembly and expose direct theorem entrypoints from handler typing assumptions.
- **Phase 2 (active):** Added one-hop admissible projection helpers for both contract and schema surfaces (`*_rowTailStable`, `*_preserves_nonFail`, `*_failRemoved*`) so downstream chaining can consume each guarantee independently from a single admissible assumption.
- **Phase 2 (active):** Added named admissible bundle contracts (`AdmissibleEffectPolyLoweringBundle`, `AdmissibleEffectPolyHandlerBundle`) with constructor/projection helpers, giving stable one-name theorem outputs for full capstone consequences.
- **Phase 2 (active):** Added admissibility partition theorems (`catchAdmissible_xor_unnecessary`) and admissible-branch extractors on contract/schema wrappers, making the runtime “admissible vs E0012-unnecessary” split explicit in theorem assumptions.
- **Phase 2 (active):** Added `Kea/Properties/CatchTypingBridge.lean`, a judgment-shaped bridge (`CatchTypingJudgment`) from typing-style catch premises into admissible effect-polymorphism capstones (`catchTypingJudgment_sound`, row-tail/non-Fail projections, admissibility branch).
- **Phase 2 (active):** `CatchTypingBridge` now includes judgment-level named bundles/projections (`CatchTypingBundle`, `catchTypingJudgment_bundle_*`) for one-name consumption of clause-removal and lowered-effect guarantees.
- **Phase 2 (active):** Added direct premise adapters in `CatchTypingBridge` (`mkCatchTypingJudgment`, `catchTypingJudgment_sound_of_premises`, noncomputable `catchTypingJudgment_bundle_of_premises`) for judgment-free entry into the bridge surface.
- **Phase 2 (active):** `CatchTypingBridge` now includes one-hop `of_premises` projections for row-tail/non-Fail preservation and bundle facets, so raw-premise call sites can consume specific guarantees without intermediate destructuring.
- **Phase 2 (active):** `CatchTypingBridge` now includes combined/classified premise surfaces (`CatchTypingCapstoneOutcome`, `catchTypingJudgment_capstone_of_premises`, `catchTypingJudgment_classify_of_premises`) plus Fail-presence/absence entry wrappers, aligning generic catch APIs with the higher-order runtime-admissibility pattern.
- **Phase 2 (active):** Higher-order typed-Fail catch regression is now closed on latest MCP probes: `catch` over `fn() -[Log, Fail String]> Int` is accepted with residual `Log`, while fail-absent paths still correctly reject with `E0012`.
- **Phase 2 (active):** Added `Kea/Properties/HigherOrderCatchContracts.lean` to specialize higher-order catch theorem surfaces (`higherOrderCatchType`, `HigherOrderCatchTypingJudgment`, soundness/admissibility theorems) and align formal APIs with the now-fixed higher-order MCP behavior.
- **Phase 2 (active):** Fail/catch bridge layers now consume the shared closed-aware entry API for clause-level handled-effect removal (`FailResultContracts.failResultContract_sound`, `EffectPolymorphismSoundness.effectPolyHandlerSchema_sound` now route through `wellTypedSlice_implies_handled_removed_legacy_via_closedAware`).
- **Phase 2 (active):** Catch layers now expose direct closed-aware clause-removal adapters (`CatchTypingBridge.catchTypingJudgment_clauseFailRemoved_via_closedAware`, `HigherOrderCatchContracts.higherOrderCatchTypingJudgment_clauseFailRemoved_via_closedAware`) so higher-order and first-order catch capstones consume the same entry contract explicitly.
- **Phase 2 (active):** Catch layers now additionally expose closed-aware clause row-tail adapters (`catchTypingJudgment_clauseRowTailStable_closedAware`, `higherOrderCatchTypingJudgment_clauseRowTailStable_closedAware`) to align clause-output shape reasoning across first-order and higher-order catch paths.
- **Phase 2 (active):** `HigherOrderCatchContracts` now includes direct raw-premise adapters (`higherOrderCatchTypingJudgment_sound_of_premises`, `higherOrderCatchTypingJudgment_admissibility_branch_of_premises`) for judgment-free entry into higher-order theorem surfaces.
- **Phase 2 (active):** `HigherOrderCatchContracts` now also includes named bundle contracts/projections (`HigherOrderCatchBundle`, `higherOrderCatchTypingJudgment_bundle*`) for stable one-name consumption of higher-order capstone consequences.
- **Phase 2 (active):** `HigherOrderCatchContracts` now includes one-hop bundle `of_premises` projections (`higherOrderCatchTypingJudgment_bundle_*_of_premises`) so raw-premise higher-order call sites can extract clause-removal/row-tail/non-Fail guarantees directly.
- **Phase 2 (active):** `HigherOrderCatchContracts` now includes a combined raw-premise capstone (`higherOrderCatchTypingJudgment_capstone_of_premises`) that packages clause Fail-removal, lowered-row guarantees, and admissibility-vs-unnecessary branch facts in one theorem surface.
- **Phase 2 (active):** Added higher-order practical entry wrappers (`higherOrderCatchTypingJudgment_capstone_of_fail_present`, `higherOrderCatchUnnecessary_of_fail_absent`) so call sites can start from direct Fail-label presence/absence evidence.
- **Phase 2 (active):** Added a higher-order single-entry classifier (`higherOrderCatchTypingJudgment_classify_of_premises`) over `HigherOrderCatchCapstoneOutcome`, returning either full capstone consequences or the runtime-aligned `catchUnnecessary` branch without requiring an explicit admissibility premise.

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
