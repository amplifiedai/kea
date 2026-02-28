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
Combined higher-order capstone outcome used by premise-level classifier theorems.
-/
def HigherOrderCatchCapstoneOutcome
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop :=
  RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
    ∃ loweredEffects,
      loweredTy =
        .functionEff
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          loweredEffects
          (.result okTy errTy) ∧
      EffectPolymorphismSoundness.rowTailStable innerEffects loweredEffects ∧
      EffectPolymorphismSoundness.labelsPreservedExcept
        innerEffects loweredEffects FailResultContracts.failLabel ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false ∧
      FailResultContracts.catchAdmissible innerEffects ∧
      ¬ FailResultContracts.catchUnnecessary innerEffects

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
  have h_clause_removed :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects j.judgment.clause))
        FailResultContracts.failLabel = false :=
    CatchTypingBridge.catchTypingJudgment_clauseFailRemoved_via_closedAware j.judgment
  rcases CatchTypingBridge.catchTypingJudgment_sound j.judgment with
    ⟨_h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed⟩
  refine ⟨h_clause_removed, loweredEffects, ?_, ?_, ?_, h_removed⟩
  · simpa [higherOrderParamType, j.h_params] using h_ty
  · simpa [j.h_clauseEffects] using h_tail
  · simpa [j.h_clauseEffects] using h_preserve

theorem higherOrderCatchTypingJudgment_clauseFailRemoved_via_closedAware
    (j : HigherOrderCatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.judgment.clause))
      FailResultContracts.failLabel = false :=
  CatchTypingBridge.catchTypingJudgment_clauseFailRemoved_via_closedAware j.judgment

theorem higherOrderCatchTypingJudgment_clauseRowTailStable_closedAware
    (j : HigherOrderCatchTypingJudgment) :
    EffectRow.rest
      (HandlerClosedAwareContracts.resultEffectsClosedAware j.judgment.clause) =
      EffectRow.rest j.innerEffects := by
  have h_tail :
      EffectRow.rest
        (HandlerClosedAwareContracts.resultEffectsClosedAware j.judgment.clause) =
        EffectRow.rest j.judgment.clause.exprEffects :=
    CatchTypingBridge.catchTypingJudgment_clauseRowTailStable_closedAware j.judgment
  simpa [j.h_clauseEffects] using h_tail

theorem higherOrderCatchTypingJudgment_admissibility_branch
    (j : HigherOrderCatchTypingJudgment) :
    FailResultContracts.catchAdmissible j.innerEffects ∧
      ¬ FailResultContracts.catchUnnecessary j.innerEffects := by
  have h_branch := CatchTypingBridge.catchTypingJudgment_admissibility_branch j.judgment
  simpa [j.h_clauseEffects] using h_branch

theorem higherOrderCatchTypingJudgment_sound_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        loweredTy =
          .functionEff
            (.cons (higherOrderParamType innerEffects okTy) .nil)
            loweredEffects
            (.result okTy errTy) ∧
        EffectPolymorphismSoundness.rowTailStable innerEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          innerEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  let cj : CatchTypingBridge.CatchTypingJudgment :=
    CatchTypingBridge.mkCatchTypingJudgment
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  let hj : HigherOrderCatchTypingJudgment := {
    judgment := cj
    innerEffects := innerEffects
    h_params := rfl
    h_clauseEffects := h_clauseEffects
  }
  exact higherOrderCatchTypingJudgment_sound hj

theorem higherOrderCatchTypingJudgment_sound_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        loweredTy =
          .functionEff
            (.cons (higherOrderParamType innerEffects okTy) .nil)
            loweredEffects
            (.result okTy errTy) ∧
        EffectPolymorphismSoundness.rowTailStable innerEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          innerEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact higherOrderCatchTypingJudgment_sound_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered

theorem higherOrderCatchTypingJudgment_admissibility_branch_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    FailResultContracts.catchAdmissible innerEffects ∧
      ¬ FailResultContracts.catchUnnecessary innerEffects := by
  let cj : CatchTypingBridge.CatchTypingJudgment :=
    CatchTypingBridge.mkCatchTypingJudgment
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  let hj : HigherOrderCatchTypingJudgment := {
    judgment := cj
    innerEffects := innerEffects
    h_params := rfl
    h_clauseEffects := h_clauseEffects
  }
  exact higherOrderCatchTypingJudgment_admissibility_branch hj

theorem higherOrderCatchTypingJudgment_admissibility_branch_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    FailResultContracts.catchAdmissible innerEffects ∧
      ¬ FailResultContracts.catchUnnecessary innerEffects := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact higherOrderCatchTypingJudgment_admissibility_branch_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered

structure HigherOrderCatchBundle (j : HigherOrderCatchTypingJudgment) where
  clauseFailRemoved :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.judgment.clause))
      FailResultContracts.failLabel = false
  loweredEffects : EffectRow
  loweredEq :
    j.judgment.loweredTy =
      .functionEff
        (.cons (higherOrderParamType j.innerEffects j.judgment.okTy) .nil)
        loweredEffects
        (.result j.judgment.okTy j.judgment.errTy)
  rowTailStable :
    EffectPolymorphismSoundness.rowTailStable j.innerEffects loweredEffects
  preservesNonFail :
    EffectPolymorphismSoundness.labelsPreservedExcept
      j.innerEffects loweredEffects FailResultContracts.failLabel
  failRemoved :
    RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false

/--
One-hop decomposition of the type-valued higher-order catch bundle into explicit
existential components.
-/
theorem higherOrderCatchBundle_as_components
    (j : HigherOrderCatchTypingJudgment)
    (h_bundle : HigherOrderCatchBundle j) :
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
  exact ⟨
    h_bundle.clauseFailRemoved,
    h_bundle.loweredEffects,
    h_bundle.loweredEq,
    h_bundle.rowTailStable,
    h_bundle.preservesNonFail,
    h_bundle.failRemoved
  ⟩

/-- Constructor helper from explicit existential higher-order bundle components. -/
noncomputable def higherOrderCatchBundle_of_components
    (j : HigherOrderCatchTypingJudgment)
    (h_comp :
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
          RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false) :
    HigherOrderCatchBundle j :=
  let h_clause_removed := h_comp.1
  let h_lowering := h_comp.2
  let loweredEffects := Classical.choose h_lowering
  let hspec := Classical.choose_spec h_lowering
  {
    clauseFailRemoved := h_clause_removed
    loweredEffects := loweredEffects
    loweredEq := hspec.1
    rowTailStable := hspec.2.1
    preservesNonFail := hspec.2.2.1
    failRemoved := hspec.2.2.2
  }

/--
Structural decomposition for the type-valued higher-order catch bundle, phrased
at `Nonempty` to stay in `Prop`.
-/
theorem higherOrderCatchBundle_iff_components
    (j : HigherOrderCatchTypingJudgment) :
    Nonempty (HigherOrderCatchBundle j)
      ↔
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
  constructor
  · intro h_nonempty
    rcases h_nonempty with ⟨h_bundle⟩
    exact higherOrderCatchBundle_as_components j h_bundle
  · intro h_comp
    exact ⟨higherOrderCatchBundle_of_components j h_comp⟩

noncomputable def higherOrderCatchTypingJudgment_bundle
    (j : HigherOrderCatchTypingJudgment) :
    HigherOrderCatchBundle j :=
  let h := higherOrderCatchTypingJudgment_sound j
  let h_clause_removed := h.1
  let h_lowering := h.2
  let loweredEffects := Classical.choose h_lowering
  let hspec := Classical.choose_spec h_lowering
  {
    clauseFailRemoved := h_clause_removed
    loweredEffects := loweredEffects
    loweredEq := hspec.1
    rowTailStable := hspec.2.1
    preservesNonFail := hspec.2.2.1
    failRemoved := hspec.2.2.2
  }

theorem higherOrderCatchTypingJudgment_bundle_clauseFailRemoved
    (j : HigherOrderCatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects j.judgment.clause))
      FailResultContracts.failLabel = false :=
  (higherOrderCatchTypingJudgment_bundle j).clauseFailRemoved

theorem higherOrderCatchTypingJudgment_bundle_rowTailStable
    (j : HigherOrderCatchTypingJudgment) :
    EffectPolymorphismSoundness.rowTailStable
      j.innerEffects
      (higherOrderCatchTypingJudgment_bundle j).loweredEffects :=
  (higherOrderCatchTypingJudgment_bundle j).rowTailStable

theorem higherOrderCatchTypingJudgment_bundle_preserves_nonFail
    (j : HigherOrderCatchTypingJudgment) :
    EffectPolymorphismSoundness.labelsPreservedExcept
      j.innerEffects
      (higherOrderCatchTypingJudgment_bundle j).loweredEffects
      FailResultContracts.failLabel :=
  (higherOrderCatchTypingJudgment_bundle j).preservesNonFail

theorem higherOrderCatchTypingJudgment_bundle_failRemoved
    (j : HigherOrderCatchTypingJudgment) :
    RowFields.has
      (EffectRow.fields (higherOrderCatchTypingJudgment_bundle j).loweredEffects)
      FailResultContracts.failLabel = false :=
  (higherOrderCatchTypingJudgment_bundle j).failRemoved

noncomputable def higherOrderCatchTypingJudgment_bundle_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchBundle
      {
        judgment := CatchTypingBridge.mkCatchTypingJudgment
          clause
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          okTy
          errTy
          loweredTy
          h_wellTyped
          h_failZero
          h_admissible
          h_lowered
        innerEffects := innerEffects
        h_params := rfl
        h_clauseEffects := h_clauseEffects
      } := by
  let cj : CatchTypingBridge.CatchTypingJudgment :=
    CatchTypingBridge.mkCatchTypingJudgment
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  let hj : HigherOrderCatchTypingJudgment := {
    judgment := cj
    innerEffects := innerEffects
    h_params := rfl
    h_clauseEffects := h_clauseEffects
  }
  exact higherOrderCatchTypingJudgment_bundle hj

theorem higherOrderCatchTypingJudgment_bundle_as_components_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        loweredTy =
          .functionEff
            (.cons (higherOrderParamType innerEffects okTy) .nil)
            loweredEffects
            (.result okTy errTy) ∧
        EffectPolymorphismSoundness.rowTailStable innerEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          innerEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  let cj : CatchTypingBridge.CatchTypingJudgment :=
    CatchTypingBridge.mkCatchTypingJudgment
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  let hj : HigherOrderCatchTypingJudgment := {
    judgment := cj
    innerEffects := innerEffects
    h_params := rfl
    h_clauseEffects := h_clauseEffects
  }
  simpa [hj] using higherOrderCatchBundle_as_components hj (higherOrderCatchTypingJudgment_bundle hj)

noncomputable def higherOrderCatchTypingJudgment_bundle_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchBundle
      {
        judgment := CatchTypingBridge.mkCatchTypingJudgment
          clause
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          okTy
          errTy
          loweredTy
          h_wellTyped
          h_failZero
          ((FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present)
          h_lowered
        innerEffects := innerEffects
        h_params := rfl
        h_clauseEffects := h_clauseEffects
      } := by
  let h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact higherOrderCatchTypingJudgment_bundle_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered

theorem higherOrderCatchTypingJudgment_bundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        loweredTy =
          .functionEff
            (.cons (higherOrderParamType innerEffects okTy) .nil)
            loweredEffects
            (.result okTy errTy) ∧
        EffectPolymorphismSoundness.rowTailStable innerEffects loweredEffects ∧
        EffectPolymorphismSoundness.labelsPreservedExcept
          innerEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  let h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact higherOrderCatchTypingJudgment_bundle_as_components_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered

theorem higherOrderCatchTypingJudgment_bundle_clauseFailRemoved_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false := by
  exact (higherOrderCatchTypingJudgment_bundle_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).clauseFailRemoved

theorem higherOrderCatchTypingJudgment_bundle_rowTailStable_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    EffectPolymorphismSoundness.rowTailStable
      innerEffects
      (higherOrderCatchTypingJudgment_bundle_of_premises
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).loweredEffects := by
  exact (higherOrderCatchTypingJudgment_bundle_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).rowTailStable

theorem higherOrderCatchTypingJudgment_bundle_preserves_nonFail_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    EffectPolymorphismSoundness.labelsPreservedExcept
      innerEffects
      (higherOrderCatchTypingJudgment_bundle_of_premises
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).loweredEffects
      FailResultContracts.failLabel := by
  exact (higherOrderCatchTypingJudgment_bundle_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).preservesNonFail

theorem higherOrderCatchTypingJudgment_bundle_failRemoved_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields
        (higherOrderCatchTypingJudgment_bundle_of_premises
          clause innerEffects okTy errTy loweredTy
          h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).loweredEffects)
      FailResultContracts.failLabel = false := by
  exact (higherOrderCatchTypingJudgment_bundle_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).failRemoved

theorem higherOrderCatchTypingJudgment_bundle_clauseFailRemoved_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false := by
  exact (higherOrderCatchTypingJudgment_bundle_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).clauseFailRemoved

theorem higherOrderCatchTypingJudgment_bundle_rowTailStable_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    EffectPolymorphismSoundness.rowTailStable
      innerEffects
      (higherOrderCatchTypingJudgment_bundle_of_fail_present
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).loweredEffects := by
  exact (higherOrderCatchTypingJudgment_bundle_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).rowTailStable

theorem higherOrderCatchTypingJudgment_bundle_preserves_nonFail_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    EffectPolymorphismSoundness.labelsPreservedExcept
      innerEffects
      (higherOrderCatchTypingJudgment_bundle_of_fail_present
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).loweredEffects
      FailResultContracts.failLabel := by
  exact (higherOrderCatchTypingJudgment_bundle_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).preservesNonFail

theorem higherOrderCatchTypingJudgment_bundle_failRemoved_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    RowFields.has
      (EffectRow.fields
        (higherOrderCatchTypingJudgment_bundle_of_fail_present
          clause innerEffects okTy errTy loweredTy
          h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).loweredEffects)
      FailResultContracts.failLabel = false := by
  exact (higherOrderCatchTypingJudgment_bundle_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).failRemoved

theorem higherOrderCatchTypingJudgment_capstone_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  rcases higherOrderCatchTypingJudgment_sound_of_premises
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered with
    ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed⟩
  rcases higherOrderCatchTypingJudgment_admissibility_branch_of_premises
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered with
    ⟨h_adm_inner, h_not_unnecessary⟩
  exact ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed, h_adm_inner, h_not_unnecessary⟩

theorem higherOrderCatchTypingJudgment_capstone_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact higherOrderCatchTypingJudgment_capstone_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered

theorem higherOrderCatchUnnecessary_of_fail_absent
    (innerEffects : EffectRow)
    (h_fail_absent :
      RowFields.has (EffectRow.fields innerEffects) FailResultContracts.failLabel = false) :
    FailResultContracts.catchUnnecessary innerEffects := by
  exact (FailResultContracts.catchUnnecessary_iff_fail_absent innerEffects).2 h_fail_absent

theorem higherOrderCatchTypingJudgment_classify_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  rcases FailResultContracts.catchAdmissible_or_unnecessary innerEffects with h_adm | h_unnecessary
  · have h_admissible_clause : FailResultContracts.catchAdmissible clause.exprEffects := by
      simpa [h_clauseEffects] using h_adm
    left
    exact higherOrderCatchTypingJudgment_capstone_of_premises
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible_clause h_clauseEffects h_lowered
  · exact Or.inr h_unnecessary

theorem higherOrderCatchTypingJudgment_classify_of_fail_present
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  exact Or.inl <|
    higherOrderCatchTypingJudgment_capstone_of_fail_present
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered

/--
Bridge generic catch capstone outcomes into the higher-order specialized
capstone shape under the clause-effects identification.
-/
theorem higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_cap :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  rcases h_cap with
    ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed, h_adm, h_not_unnecessary⟩
  refine ⟨h_clause_removed, loweredEffects, h_ty, ?_, ?_, h_removed, ?_, ?_⟩
  · simpa [EffectPolymorphismSoundness.rowTailStable, h_clauseEffects] using h_tail
  · simpa [EffectPolymorphismSoundness.labelsPreservedExcept, h_clauseEffects] using h_preserve
  · simpa [h_clauseEffects] using h_adm
  · simpa [h_clauseEffects] using h_not_unnecessary

/--
Bridge higher-order specialized capstone outcomes into the generic catch
capstone shape under the clause-effects identification.
-/
theorem higherOrderCatchCapstoneOutcome_to_catchTypingCapstoneOutcome
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_cap : HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy := by
  rcases h_cap with
    ⟨h_clause_removed, loweredEffects, h_ty, h_tail, h_preserve, h_removed, h_adm, h_not_unnecessary⟩
  refine ⟨h_clause_removed, loweredEffects, h_ty, ?_, ?_, h_removed, ?_, ?_⟩
  · simpa [EffectPolymorphismSoundness.rowTailStable, h_clauseEffects] using h_tail
  · simpa [EffectPolymorphismSoundness.labelsPreservedExcept, h_clauseEffects] using h_preserve
  · simpa [h_clauseEffects] using h_adm
  · simpa [h_clauseEffects] using h_not_unnecessary

/--
Specialized/generic capstone equivalence for higher-order catch under the
clause-effects identification.
-/
theorem higherOrderCatchCapstoneOutcome_iff_catchTypingCapstoneOutcome
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ↔ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          okTy
          errTy
          loweredTy := by
  constructor
  · intro h_cap
    exact higherOrderCatchCapstoneOutcome_to_catchTypingCapstoneOutcome
      clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap
  · intro h_cap
    exact higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
      clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap

/--
Route higher-order capstone construction explicitly through the generic
`CatchTypingBridge` capstone theorem.
-/
theorem higherOrderCatchTypingJudgment_capstone_of_premises_via_catchTypingBridge
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  have h_cap :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy :=
    CatchTypingBridge.catchTypingJudgment_capstone_of_premises
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  exact higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap

theorem higherOrderCatchTypingJudgment_capstone_of_fail_present_via_catchTypingBridge
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  have h_cap :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy :=
    CatchTypingBridge.catchTypingJudgment_capstone_of_fail_present
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_fail_present
      h_lowered
  exact higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap

/--
Route higher-order classification explicitly through the generic
`CatchTypingBridge` classifier theorem.
-/
theorem higherOrderCatchTypingJudgment_classify_of_premises_via_catchTypingBridge
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  have h_class :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
    CatchTypingBridge.catchTypingJudgment_classify_of_premises
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_lowered
  cases h_class with
  | inl h_cap =>
      exact Or.inl
        (higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
          clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap)
  | inr h_unnecessary =>
      exact Or.inr (by simpa [h_clauseEffects] using h_unnecessary)

theorem higherOrderCatchTypingJudgment_classify_of_fail_present_via_catchTypingBridge
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  have h_class :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
    CatchTypingBridge.catchTypingJudgment_classify_of_fail_present
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_fail_present
      h_lowered
  cases h_class with
  | inl h_cap =>
      exact Or.inl
        (higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
          clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap)
  | inr h_unnecessary =>
      exact Or.inr (by simpa [h_clauseEffects] using h_unnecessary)

/--
Transport a generic catch classifier outcome to the higher-order classifier
surface under the clause-effects identification.
-/
theorem higherOrderCatchClassification_of_catchTypingClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_class :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  cases h_class with
  | inl h_cap =>
      exact Or.inl
        (higherOrderCatchCapstoneOutcome_of_catchTypingCapstoneOutcome
          clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap)
  | inr h_unnecessary =>
      exact Or.inr (by simpa [h_clauseEffects] using h_unnecessary)

/--
Transport a higher-order classifier outcome to the generic catch classifier
surface under the clause-effects identification.
-/
theorem catchTypingClassification_of_higherOrderCatchClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_class :
      HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
        FailResultContracts.catchUnnecessary innerEffects) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects := by
  cases h_class with
  | inl h_cap =>
      exact Or.inl
        (higherOrderCatchCapstoneOutcome_to_catchTypingCapstoneOutcome
          clause innerEffects okTy errTy loweredTy h_clauseEffects h_cap)
  | inr h_unnecessary =>
      exact Or.inr (by simpa [h_clauseEffects] using h_unnecessary)

/--
Classifier-level equivalence between higher-order and generic catch surfaces
under the clause-effects identification.
-/
theorem higherOrderCatchClassification_iff_catchTypingClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects) :
    (HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects)
      ↔
    (CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects) := by
  constructor
  · intro h_class
    exact catchTypingClassification_of_higherOrderCatchClassification
      clause innerEffects okTy errTy loweredTy h_clauseEffects h_class
  · intro h_class
    exact higherOrderCatchClassification_of_catchTypingClassification
      clause innerEffects okTy errTy loweredTy h_clauseEffects h_class

/--
Packaged bridge-law surface linking higher-order and generic catch outcomes
under clause-effect identification.
-/
structure HigherOrderCatchBridgeLaws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop where
  capstoneIff :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ↔ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          okTy
          errTy
          loweredTy
  classificationIff :
    (HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects)
      ↔
    (CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects)

/-- Construct packaged higher-order catch bridge laws from clause-effect identification. -/
theorem higherOrderCatchBridgeLaws_of_clauseEffects
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects) :
    HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  refine {
    capstoneIff :=
      higherOrderCatchCapstoneOutcome_iff_catchTypingCapstoneOutcome
        clause innerEffects okTy errTy loweredTy h_clauseEffects
    classificationIff :=
      higherOrderCatchClassification_iff_catchTypingClassification
        clause innerEffects okTy errTy loweredTy h_clauseEffects
  }

/-- One-hop projection: capstone equivalence from packaged higher-order catch bridge laws. -/
theorem higherOrderCatchBridgeLaws_capstoneIff
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_laws : HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ↔ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          okTy
          errTy
          loweredTy :=
  h_laws.capstoneIff

/-- One-hop projection: classifier equivalence from packaged higher-order catch bridge laws. -/
theorem higherOrderCatchBridgeLaws_classificationIff
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_laws : HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy) :
    (HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects)
      ↔
    (CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :=
  h_laws.classificationIff

/-- Transport a higher-order capstone to generic form via packaged bridge laws. -/
theorem higherOrderCatchBridgeLaws_capstone_to_generic
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_laws : HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy)
    (h_cap : HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy :=
  (h_laws.capstoneIff).1 h_cap

/-- Transport a generic capstone to higher-order form via packaged bridge laws. -/
theorem higherOrderCatchBridgeLaws_generic_to_capstone
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_laws : HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy)
    (h_cap :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  (h_laws.capstoneIff).2 h_cap

/-- Transport a higher-order classifier to generic form via packaged bridge laws. -/
theorem higherOrderCatchBridgeLaws_classification_to_generic
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_laws : HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy)
    (h_class :
      HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
        FailResultContracts.catchUnnecessary innerEffects) :
    (CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :=
  (h_laws.classificationIff).1 h_class

/-- Transport a generic classifier to higher-order form via packaged bridge laws. -/
theorem higherOrderCatchBridgeLaws_generic_to_classification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_laws : HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy)
    (h_class :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    (HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects) :=
  (h_laws.classificationIff).2 h_class

/--
Route higher-order capstone construction through packaged bridge laws and the
generic catch capstone theorem.
-/
theorem higherOrderCatchTypingJudgment_capstone_of_premises_via_bridgeLaws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  let h_laws :=
    higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  have h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy :=
    CatchTypingBridge.catchTypingJudgment_capstone_of_premises
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  exact higherOrderCatchBridgeLaws_generic_to_capstone
    clause innerEffects okTy errTy loweredTy h_laws h_generic

theorem higherOrderCatchTypingJudgment_capstone_of_fail_present_via_bridgeLaws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  let h_laws :=
    higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  have h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy :=
    CatchTypingBridge.catchTypingJudgment_capstone_of_fail_present
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_fail_present
      h_lowered
  exact higherOrderCatchBridgeLaws_generic_to_capstone
    clause innerEffects okTy errTy loweredTy h_laws h_generic

/--
Route higher-order classification through packaged bridge laws and the generic
catch classifier theorem.
-/
theorem higherOrderCatchTypingJudgment_classify_of_premises_via_bridgeLaws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  let h_laws :=
    higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  have h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
    CatchTypingBridge.catchTypingJudgment_classify_of_premises
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_lowered
  exact higherOrderCatchBridgeLaws_generic_to_classification
    clause innerEffects okTy errTy loweredTy h_laws h_generic

theorem higherOrderCatchTypingJudgment_classify_of_fail_present_via_bridgeLaws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (.cons (higherOrderParamType innerEffects okTy) .nil)
          clause.exprEffects
          okTy
          errTy) :
    HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy ∨
      FailResultContracts.catchUnnecessary innerEffects := by
  let h_laws :=
    higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  have h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause
        (.cons (higherOrderParamType innerEffects okTy) .nil)
        okTy
        errTy
        loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
    CatchTypingBridge.catchTypingJudgment_classify_of_fail_present
      clause
      (.cons (higherOrderParamType innerEffects okTy) .nil)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_fail_present
      h_lowered
  exact higherOrderCatchBridgeLaws_generic_to_classification
    clause innerEffects okTy errTy loweredTy h_laws h_generic

end HigherOrderCatchContracts
end Kea
