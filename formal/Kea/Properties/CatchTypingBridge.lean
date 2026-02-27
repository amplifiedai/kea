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

def mkCatchTypingJudgment
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    CatchTypingJudgment := {
  clause := clause
  params := params
  okTy := okTy
  errTy := errTy
  loweredTy := loweredTy
  h_wellTyped := h_wellTyped
  h_failZero := h_failZero
  h_admissible := h_admissible
  h_lowered := h_lowered
}

/--
Combined catch-lowering capstone outcome used by premise-level classifier theorems.
-/
def CatchTypingCapstoneOutcome
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty) : Prop :=
  RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
    ∃ loweredEffects,
      loweredTy = .functionEff params loweredEffects (.result okTy errTy) ∧
      EffectPolymorphismSoundness.rowTailStable clause.exprEffects loweredEffects ∧
      EffectPolymorphismSoundness.labelsPreservedExcept
        clause.exprEffects loweredEffects FailResultContracts.failLabel ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false ∧
      FailResultContracts.catchAdmissible clause.exprEffects ∧
      ¬ FailResultContracts.catchUnnecessary clause.exprEffects

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

abbrev CatchTypingClosedAwareBundle (j : CatchTypingJudgment) :=
  HandlerClosedAwareContracts.ClosedAwareResultBundle j.clause

def catchTypingJudgment_closedAwareBundle
    (j : CatchTypingJudgment) :
    CatchTypingClosedAwareBundle j :=
  HandlerClosedAwareContracts.closedAwareResultBundle_of_wellTyped
    j.clause j.h_wellTyped

theorem catchTypingJudgment_clauseHandledRemoved_closedAware
    (j : CatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware j.clause))
      j.clause.handled = false :=
  (catchTypingJudgment_closedAwareBundle j).closedAwareHandledRemoved

theorem catchTypingJudgment_clauseRowTailStable_closedAware
    (j : CatchTypingJudgment) :
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware j.clause) =
      EffectRow.rest j.clause.exprEffects :=
  (catchTypingJudgment_closedAwareBundle j).closedAwareRowTailStable

theorem catchTypingJudgment_clauseFailRemoved_via_closedAware
    (j : CatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.clause))
      FailResultContracts.failLabel = false := by
  have h_removed_handled :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects j.clause))
        j.clause.handled = false :=
    (catchTypingJudgment_closedAwareBundle j).legacyHandledRemoved
  simpa [FailResultContracts.failLabel, j.h_failZero.1] using h_removed_handled

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

theorem catchTypingJudgment_sound_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        loweredTy = .functionEff params loweredEffects (.result okTy errTy) ∧
        EffectPolymorphismSoundness.rowTailStable clause.exprEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          clause.exprEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  let j := mkCatchTypingJudgment
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered
  exact catchTypingJudgment_sound j

theorem catchTypingJudgment_capstone_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    CatchTypingCapstoneOutcome clause params okTy errTy loweredTy := by
  rcases catchTypingJudgment_sound_of_premises
      clause params okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_lowered with
    ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed⟩
  have h_branch :
      FailResultContracts.catchAdmissible clause.exprEffects ∧
        ¬ FailResultContracts.catchUnnecessary clause.exprEffects :=
    catchTypingJudgment_admissibility_branch
      (mkCatchTypingJudgment
        clause params okTy errTy loweredTy
        h_wellTyped h_failZero h_admissible h_lowered)
  exact ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed, h_branch.1, h_branch.2⟩

theorem catchTypingJudgment_capstone_of_fail_present
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    CatchTypingCapstoneOutcome clause params okTy errTy loweredTy := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact catchTypingJudgment_capstone_of_premises
    clause params okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_lowered

theorem catchTypingUnnecessary_of_fail_absent
    (effects : EffectRow)
    (h_fail_absent :
      RowFields.has (EffectRow.fields effects) FailResultContracts.failLabel = false) :
    FailResultContracts.catchUnnecessary effects := by
  exact (FailResultContracts.catchUnnecessary_iff_fail_absent effects).2 h_fail_absent

theorem catchTypingJudgment_classify_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    CatchTypingCapstoneOutcome clause params okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary clause.exprEffects := by
  rcases FailResultContracts.catchAdmissible_or_unnecessary clause.exprEffects with h_adm | h_unnecessary
  · left
    exact catchTypingJudgment_capstone_of_premises
      clause params okTy errTy loweredTy
      h_wellTyped h_failZero h_adm h_lowered
  · exact Or.inr h_unnecessary

theorem catchTypingJudgment_rowTailStable_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    ∃ loweredEffects,
      loweredTy = .functionEff params loweredEffects (.result okTy errTy) ∧
      EffectPolymorphismSoundness.rowTailStable clause.exprEffects loweredEffects := by
  let j := mkCatchTypingJudgment
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered
  exact catchTypingJudgment_rowTailStable j

theorem catchTypingJudgment_preserves_nonFail_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    ∃ loweredEffects,
      loweredTy = .functionEff params loweredEffects (.result okTy errTy) ∧
      EffectPolymorphismSoundness.labelsPreservedExcept
        clause.exprEffects loweredEffects FailResultContracts.failLabel := by
  let j := mkCatchTypingJudgment
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered
  exact catchTypingJudgment_preserves_nonFail j

abbrev CatchTypingBundle (j : CatchTypingJudgment) :=
  EffectPolymorphismSoundness.AdmissibleEffectPolyHandlerBundle
    (toAdmissibleEffectPolyHandlerSchema j)

noncomputable def catchTypingJudgment_bundle
    (j : CatchTypingJudgment) :
    CatchTypingBundle j :=
  EffectPolymorphismSoundness.admissibleEffectPolyHandler_bundle
    (toAdmissibleEffectPolyHandlerSchema j)

noncomputable def catchTypingJudgment_bundle_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    CatchTypingBundle
      (mkCatchTypingJudgment
        clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered) := by
  let j := mkCatchTypingJudgment
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered
  exact catchTypingJudgment_bundle j

theorem catchTypingJudgment_bundle_clauseFailRemoved_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false := by
  let j := mkCatchTypingJudgment
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered
  exact catchTypingJudgment_clauseFailRemoved_via_closedAware j

theorem catchTypingJudgment_bundle_rowTailStable_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy) :
    EffectPolymorphismSoundness.rowTailStable clause.exprEffects
      (catchTypingJudgment_bundle_of_premises
        clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered).lowering.loweredEffects := by
  let j := mkCatchTypingJudgment
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_admissible h_lowered
  exact EffectPolymorphismSoundness.admissibleEffectPolyHandler_bundle_rowTailStable
    (toAdmissibleEffectPolyHandlerSchema j)

theorem catchTypingJudgment_bundle_clauseFailRemoved
    (j : CatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.clause))
      FailResultContracts.failLabel = false :=
  catchTypingJudgment_clauseFailRemoved_via_closedAware j

theorem catchTypingJudgment_bundle_rowTailStable
    (j : CatchTypingJudgment) :
    EffectPolymorphismSoundness.rowTailStable j.clause.exprEffects
      (catchTypingJudgment_bundle j).lowering.loweredEffects :=
  (catchTypingJudgment_bundle j).lowering.rowTailStable

theorem catchTypingJudgment_bundle_preserves_nonFail
    (j : CatchTypingJudgment) :
    EffectPolymorphismSoundness.labelsPreservedExcept
      j.clause.exprEffects
      (catchTypingJudgment_bundle j).lowering.loweredEffects
      FailResultContracts.failLabel :=
  (catchTypingJudgment_bundle j).lowering.preservesNonFail

theorem catchTypingJudgment_bundle_failRemoved_in_lowered
    (j : CatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (catchTypingJudgment_bundle j).lowering.loweredEffects)
      FailResultContracts.failLabel = false :=
  (catchTypingJudgment_bundle j).lowering.failRemoved

end CatchTypingBridge
end Kea
