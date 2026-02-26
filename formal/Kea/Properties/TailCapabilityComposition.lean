import Kea.Properties.EffectOperationTyping
import Kea.Properties.TailResumptiveClassification

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
  have _h_not_invalid :=
    TailResumptiveClassification.tail_resumptive_bundle_notInvalid c h_wellTyped
  exact tail_resumptive_eligible_capability_direct_call_sound
    c baseEffects capability h_eligible h_expr h_ne

end TailCapabilityComposition
end Kea
