/-
  Kea.Properties.HigherOrderCatchContracts

  Phase-2 specialization layer for higher-order catch shapes:
  - parameter is a nullary effectful function
  - wrapper returns `Result`
  - wrapper effects are Fail-lowered from the parameter effect row

  This module packages reusable theorem surfaces after the higher-order
  catch admissibility divergence closure.
-/

import Kea.Properties.CatchTypingBridge

namespace Kea
namespace HigherOrderCatchContracts

/-- Type of a higher-order catch parameter `f` where `f : () -[e]> a`. -/
def higherOrderParamType (innerEffects : EffectRow) (okTy : Ty) : Ty :=
  .functionEff .nil innerEffects okTy

/-- Wrapper function type for `catch f()` in the higher-order shape. -/
def higherOrderCatchType
    (innerEffects : EffectRow)
    (okTy errTy : Ty) : Ty :=
  .functionEff
    (.cons (higherOrderParamType innerEffects okTy) .nil)
    (FailResultContracts.lowerFailEffects innerEffects)
    (.result okTy errTy)

theorem higherOrderCatchType_unfold
    (innerEffects : EffectRow) (okTy errTy : Ty) :
    higherOrderCatchType innerEffects okTy errTy =
      .functionEff
        (.cons (.functionEff .nil innerEffects okTy) .nil)
        (FailResultContracts.lowerFailEffects innerEffects)
        (.result okTy errTy) := rfl

theorem higherOrderCatchType_failRemoved
    (innerEffects : EffectRow) :
    RowFields.has
      (EffectRow.fields (FailResultContracts.lowerFailEffects innerEffects))
      FailResultContracts.failLabel = false := by
  exact FailResultContracts.lowerFailEffects_removes_fail innerEffects

theorem higherOrderCatchType_rowTailStable
    (innerEffects : EffectRow) :
    EffectPolymorphismSoundness.rowTailStable
      innerEffects
      (FailResultContracts.lowerFailEffects innerEffects) := by
  exact EffectPolymorphismSoundness.lowerFailEffects_rowTailStable innerEffects

theorem higherOrderCatchType_preserves_nonFail
    (innerEffects : EffectRow)
    (other : Label)
    (h_ne : other ≠ FailResultContracts.failLabel) :
    RowFields.has
      (EffectRow.fields (FailResultContracts.lowerFailEffects innerEffects))
      other =
      RowFields.has (EffectRow.fields innerEffects) other := by
  exact FailResultContracts.lowerFailEffects_preserves_other innerEffects other h_ne

/--
Judgment-shaped specialization for higher-order catch:
the wrapped function has one parameter `f : () -[innerEffects]> okTy`.
-/
structure HigherOrderCatchTypingJudgment where
  judgment : CatchTypingBridge.CatchTypingJudgment
  innerEffects : EffectRow
  h_params :
    judgment.params = .cons (higherOrderParamType innerEffects judgment.okTy) .nil
  h_clauseEffects :
    judgment.clause.exprEffects = innerEffects

theorem higherOrderCatchTypingJudgment_sound
    (j : HigherOrderCatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.judgment.clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        j.judgment.loweredTy =
          .functionEff
            (.cons (higherOrderParamType j.innerEffects j.judgment.okTy) .nil)
            loweredEffects
            (.result j.judgment.okTy j.judgment.errTy) ∧
        EffectPolymorphismSoundness.rowTailStable j.innerEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          j.innerEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  rcases CatchTypingBridge.catchTypingJudgment_sound j.judgment with
    ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed⟩
  refine ⟨h_clause_removed, loweredEffects, ?_, ?_, ?_, h_removed⟩
  · simpa [higherOrderParamType, j.h_params] using h_ty
  · simpa [j.h_clauseEffects] using h_tail
  · simpa [j.h_clauseEffects] using h_preserve

theorem higherOrderCatchTypingJudgment_admissibility_branch
    (j : HigherOrderCatchTypingJudgment) :
    FailResultContracts.catchAdmissible j.innerEffects ∧
      ¬ FailResultContracts.catchUnnecessary j.innerEffects := by
  have h_branch := CatchTypingBridge.catchTypingJudgment_admissibility_branch j.judgment
  simpa [j.h_clauseEffects] using h_branch

end HigherOrderCatchContracts
end Kea
