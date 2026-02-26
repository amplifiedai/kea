/-
  Kea.Properties.CatchTypingBridge

  Phase-2 bridge from typing-style catch premises to the admissible
  effect-polymorphism capstone surfaces.

  This keeps the current formal layer aligned with runtime admissibility
  (`catch` requires Fail presence) while exposing theorem entrypoints in a
  judgment-shaped API.
-/

import Kea.Properties.EffectPolymorphismSoundness

namespace Kea
namespace CatchTypingBridge

/--
Typing-style premise bundle for a catch-lowered function schema.

This is intentionally judgment-shaped and mirrors the assumptions expected from
future concrete handler typing rules.
-/
structure CatchTypingJudgment where
  clause : HandleClauseContract
  params : TyList
  okTy : Ty
  errTy : Ty
  loweredTy : Ty
  h_wellTyped : HandleClauseContract.wellTypedSlice clause
  h_failZero : FailResultContracts.failAsZeroResume clause
  h_admissible : FailResultContracts.catchAdmissible clause.exprEffects
  h_lowered :
    loweredTy =
      FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy

def toAdmissibleEffectPolyHandlerSchema
    (j : CatchTypingJudgment) :
    EffectPolymorphismSoundness.AdmissibleEffectPolyHandlerSchema := {
  clause := j.clause
  params := j.params
  okTy := j.okTy
  errTy := j.errTy
  loweredTy := j.loweredTy
  h_wellTyped := j.h_wellTyped
  h_failZero := j.h_failZero
  h_lowered := j.h_lowered
  h_admissible := j.h_admissible
}

theorem catchTypingJudgment_sound
    (j : CatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        j.loweredTy = .functionEff j.params loweredEffects (.result j.okTy j.errTy) ∧
        EffectPolymorphismSoundness.rowTailStable j.clause.exprEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          j.clause.exprEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  exact EffectPolymorphismSoundness.admissibleEffectPolyHandlerSchema_sound
    (toAdmissibleEffectPolyHandlerSchema j)

theorem catchTypingJudgment_rowTailStable
    (j : CatchTypingJudgment) :
    ∃ loweredEffects,
      j.loweredTy = .functionEff j.params loweredEffects (.result j.okTy j.errTy) ∧
      EffectPolymorphismSoundness.rowTailStable j.clause.exprEffects loweredEffects := by
  exact EffectPolymorphismSoundness.admissibleEffectPolyHandlerSchema_rowTailStable
    (toAdmissibleEffectPolyHandlerSchema j)

theorem catchTypingJudgment_preserves_nonFail
    (j : CatchTypingJudgment) :
    ∃ loweredEffects,
      j.loweredTy = .functionEff j.params loweredEffects (.result j.okTy j.errTy) ∧
      EffectPolymorphismSoundness.labelsPreservedExcept
        j.clause.exprEffects loweredEffects FailResultContracts.failLabel := by
  exact EffectPolymorphismSoundness.admissibleEffectPolyHandlerSchema_preserves_nonFail
    (toAdmissibleEffectPolyHandlerSchema j)

theorem catchTypingJudgment_admissibility_branch
    (j : CatchTypingJudgment) :
    FailResultContracts.catchAdmissible j.clause.exprEffects ∧
      ¬ FailResultContracts.catchUnnecessary j.clause.exprEffects := by
  exact EffectPolymorphismSoundness.admissibleEffectPolyHandlerSchema_admissibility_branch
    (toAdmissibleEffectPolyHandlerSchema j)

end CatchTypingBridge
end Kea
