import Kea.Properties.EffectOperationTyping
import Kea.Properties.TailResumptiveClassification
import Kea.Properties.HandlerClosedAwareContracts

/-!
  Kea.Properties.TailCapabilityComposition

  Phase-2 composition layer connecting:
  - operation-call capability preservation (`EffectOperationTyping`)
  - tail-resumptive direct-call equivalence (`TailResumptiveClassification`)
-/

namespace Kea
namespace TailCapabilityComposition

theorem core_capability_direct_call_sound
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
      capability = true := by
  unfold HandleClauseContract.resultEffectsCore
  simpa [h_expr] using
    (EffectOperationTyping.capability_direct_call_sound
      baseEffects
      c.handlerEffects
      capability
      c.handled
      h_ne)

theorem resultEffects_preserves_core_label_true
    (c : HandleClauseContract)
    (label : Label)
    (h_core :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
        label = true) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects c))
      label = true := by
  cases h_then : c.thenEffects with
  | none =>
      simpa [HandleClauseContract.resultEffects, HandleClauseContract.applyThenEffects, h_then] using h_core
  | some te =>
      have h_union :
          RowFields.has
            (RowFields.unionIdem
              (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
              (EffectRow.fields te))
            label = true :=
        RowFields.has_unionIdem_of_has_left_true
          (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
          (EffectRow.fields te)
          label
          h_core
      simpa [HandleClauseContract.resultEffects, HandleClauseContract.applyThenEffects, h_then] using h_union

theorem wellTyped_capability_direct_call_sound
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects c))
      capability = true := by
  have _h_boundary :=
    TailResumptiveClassification.tail_resumptive_bundle_notInvalid c h_wellTyped
  have h_core :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
        capability = true :=
    core_capability_direct_call_sound c baseEffects capability h_expr h_ne
  exact resultEffects_preserves_core_label_true c capability h_core

/--
Cross-module capstone:
if a clause is tail-resumptive-eligible (so full result effects equal core
result effects), capability preservation proven for the core path lifts to the
full clause result effects.
-/
theorem tail_resumptive_eligible_capability_direct_call_sound
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_eligible : TailResumptiveClassification.tailResumptiveEligible c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects c))
      capability = true := by
  have h_core :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
        capability = true :=
    core_capability_direct_call_sound c baseEffects capability h_expr h_ne
  have h_result_eq_core :
      HandleClauseContract.resultEffects c =
        HandleClauseContract.resultEffectsCore c :=
    TailResumptiveClassification.tail_resumptive_direct_call_sound c h_eligible
  rw [h_result_eq_core]
  exact h_core

/--
Runtime-aligned wrapper:
requires the clause-level well-typed slice in addition to tail-resumptive
eligibility, making the precondition boundary explicit for MCP correlation.
-/
theorem tail_resumptive_wellTyped_capability_direct_call_sound
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_eligible : TailResumptiveClassification.tailResumptiveEligible c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects c))
      capability = true := by
  have _h_eligible_atMostOnce :=
    TailResumptiveClassification.tail_resumptive_eligible_implies_atMostOnce c h_eligible
  exact wellTyped_capability_direct_call_sound
    c baseEffects capability h_wellTyped h_expr h_ne

theorem wellTyped_capability_direct_call_sound_closedAware
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (_h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware c))
      capability = true := by
  have h_expr_capability :
      RowFields.has (EffectRow.fields c.exprEffects) capability = true := by
    rw [h_expr]
    exact EffectOperationTyping.performOperation_adds_effect baseEffects capability
  exact HandlerClosedAwareContracts.resultEffectsClosedAware_preserves_other_effects
    c capability h_ne h_expr_capability

theorem tail_resumptive_eligible_capability_direct_call_sound_closedAware
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_eligible : TailResumptiveClassification.tailResumptiveEligible c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware c))
      capability = true := by
  have h_expr_capability :
      RowFields.has (EffectRow.fields c.exprEffects) capability = true := by
    rw [h_expr]
    exact EffectOperationTyping.performOperation_adds_effect baseEffects capability
  have h_core_closed :
      RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsCoreClosedAware c))
        capability = true := by
    unfold HandlerClosedAwareContracts.resultEffectsCoreClosedAware
    exact HandlerClosedAwareContracts.handleComposeClosedAware_preserves_other_effects
      c.exprEffects c.handlerEffects c.handled capability h_ne h_expr_capability
  have h_eq :
      HandlerClosedAwareContracts.resultEffectsClosedAware c =
        HandlerClosedAwareContracts.resultEffectsCoreClosedAware c :=
    TailResumptiveClassification.tail_resumptive_direct_call_sound_closedAware c h_eligible
  rw [h_eq]
  exact h_core_closed

theorem tail_resumptive_wellTyped_capability_direct_call_sound_closedAware
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_eligible : TailResumptiveClassification.tailResumptiveEligible c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware c))
      capability = true := by
  have _h_not_invalid :=
    (TailResumptiveClassification.tail_resumptive_closedAware_bundle_of_wellTyped c h_wellTyped).notInvalid
  exact tail_resumptive_eligible_capability_direct_call_sound_closedAware
    c baseEffects capability h_eligible h_expr h_ne

structure TailCapabilityBundle
    (c : HandleClauseContract)
    (capability : Label) where
  coreCapability :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
      capability = true
  resultCapability :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects c))
      capability = true
  notInvalid :
    TailResumptiveClassification.classifyClause c ≠
      TailResumptiveClassification.TailResumptiveClass.invalid

theorem tailCapabilityBundle_of_wellTyped
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    TailCapabilityBundle c capability := by
  have h_core :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffectsCore c))
        capability = true :=
    core_capability_direct_call_sound c baseEffects capability h_expr h_ne
  have h_result :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects c))
        capability = true :=
    wellTyped_capability_direct_call_sound c baseEffects capability
      h_wellTyped h_expr h_ne
  have h_not_invalid :
      TailResumptiveClassification.classifyClause c ≠
        TailResumptiveClassification.TailResumptiveClass.invalid :=
    TailResumptiveClassification.tail_resumptive_bundle_notInvalid c h_wellTyped
  exact {
    coreCapability := h_core
    resultCapability := h_result
    notInvalid := h_not_invalid
  }

theorem tailCapabilityBundle_resultCapability_of_wellTyped
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects c))
      capability = true :=
  (tailCapabilityBundle_of_wellTyped c baseEffects capability h_wellTyped h_expr h_ne).resultCapability

structure TailCapabilityClosedAwareBundle
    (c : HandleClauseContract)
    (capability : Label) where
  closedAwareResultCapability :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware c))
      capability = true
  notInvalid :
    TailResumptiveClassification.classifyClause c ≠
      TailResumptiveClassification.TailResumptiveClass.invalid

theorem tailCapabilityClosedAwareBundle_of_wellTyped
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    TailCapabilityClosedAwareBundle c capability := by
  have h_result :
      RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware c))
        capability = true :=
    wellTyped_capability_direct_call_sound_closedAware
      c baseEffects capability h_wellTyped h_expr h_ne
  have h_not_invalid :
      TailResumptiveClassification.classifyClause c ≠
        TailResumptiveClassification.TailResumptiveClass.invalid :=
    (TailResumptiveClassification.tail_resumptive_closedAware_bundle_of_wellTyped c h_wellTyped).notInvalid
  exact {
    closedAwareResultCapability := h_result
    notInvalid := h_not_invalid
  }

theorem tailCapabilityClosedAwareBundle_resultCapability_of_wellTyped
    (c : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (h_wellTyped : HandleClauseContract.wellTypedSlice c)
    (h_expr :
      c.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ c.handled) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware c))
      capability = true :=
  (tailCapabilityClosedAwareBundle_of_wellTyped
    c baseEffects capability h_wellTyped h_expr h_ne).closedAwareResultCapability

end TailCapabilityComposition
end Kea
