/-
  Kea.Properties.FailResultContracts

  Phase-2 contract layer for:
  - Fail-as-zero-resume
  - Fail handler lowering to `Result`

  This module stays at the contract/invariant level and reuses the existing
  handler-typing integration surface.
-/

import Kea.Properties.HandlerTypingContracts

namespace Kea
namespace FailResultContracts

abbrev failLabel : Label := "Fail"

/-- A Fail handler clause is modeled as handling `Fail` with zero resume usage. -/
def failAsZeroResume (c : HandleClauseContract) : Prop :=
  c.handled = failLabel ∧ c.resumeUse = .zero

/-- Return-type lowering for Fail handlers: ordinary return becomes `Result`. -/
def resultLowering (okTy errTy loweredTy : Ty) : Prop :=
  loweredTy = .result okTy errTy

theorem failAsZeroResume_implies_linearityOk
    (c : HandleClauseContract)
    (h : failAsZeroResume c) :
    HandleClauseContract.linearityOk c := by
  have h_zero : c.resumeUse = .zero := h.2
  simp [HandleClauseContract.linearityOk, h_zero]

theorem failAsZeroResume_implies_resumeProvenance
    (c : HandleClauseContract)
    (h : failAsZeroResume c) :
    HandleClauseContract.resumeProvenance c := by
  exact Or.inl h.2

theorem failAsZeroResume_implies_loopLegal
    (c : HandleClauseContract)
    (h : failAsZeroResume c) :
    ResumeUse.loopLegal c.resumeUse := by
  simpa [h.2] using (resume_loop_zero_body_is_legal : ResumeUse.loopLegal .zero)

theorem resultLowering_iff
    (okTy errTy loweredTy : Ty) :
    resultLowering okTy errTy loweredTy ↔ loweredTy = .result okTy errTy := Iff.rfl

/-- Fail-effect lowering on effect rows. -/
def lowerFailEffects (effects : EffectRow) : EffectRow :=
  EffectRow.handleRemove effects failLabel

theorem lowerFailEffects_removes_fail
    (effects : EffectRow) :
    RowFields.has (EffectRow.fields (lowerFailEffects effects)) failLabel = false := by
  unfold lowerFailEffects
  exact EffectRow.handle_removes_effect effects failLabel

theorem lowerFailEffects_preserves_other
    (effects : EffectRow)
    (other : Label)
    (h_ne : other ≠ failLabel) :
    RowFields.has (EffectRow.fields (lowerFailEffects effects)) other =
      RowFields.has (EffectRow.fields effects) other := by
  simpa [lowerFailEffects, failLabel] using
    (EffectRow.handle_preserves_other_effects effects failLabel other h_ne)

theorem lowerFailEffects_noop_of_absent
    (effects : EffectRow)
    (h_abs : RowFields.has (EffectRow.fields effects) failLabel = false) :
    lowerFailEffects effects = effects := by
  simpa [lowerFailEffects, failLabel] using
    (EffectRow.handleRemove_noop_of_absent effects failLabel h_abs)

/-- Type-level lowering of a function that handles `Fail` into `Result`. -/
def lowerFailFunctionType
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy : Ty) : Ty :=
  .functionEff params (lowerFailEffects effects) (.result okTy errTy)

theorem lowerFailFunctionType_return_is_result
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy : Ty) :
    lowerFailFunctionType params effects okTy errTy =
      .functionEff params (lowerFailEffects effects) (.result okTy errTy) := rfl

theorem lowerFailFunctionType_noop_effect_of_absent
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy : Ty)
    (h_abs : RowFields.has (EffectRow.fields effects) failLabel = false) :
    lowerFailFunctionType params effects okTy errTy =
      .functionEff params effects (.result okTy errTy) := by
  simp [lowerFailFunctionType, lowerFailEffects_noop_of_absent, h_abs]

/--
Function-type equivalence slice:
`lowered` is the Fail-to-Result lowering of `original`.
-/
def failResultFunctionEquivalent (original lowered : Ty) : Prop :=
  ∃ params effects okTy errTy,
    original = .functionEff params effects okTy ∧
    lowered = lowerFailFunctionType params effects okTy errTy

theorem failResultFunctionEquivalent_implies_result_return
    (original lowered : Ty)
    (h_eqv : failResultFunctionEquivalent original lowered) :
    ∃ params eff okTy errTy,
      lowered = .functionEff params eff (.result okTy errTy) := by
  rcases h_eqv with ⟨params, effects, okTy, errTy, _h_orig, h_lowered⟩
  refine ⟨params, lowerFailEffects effects, okTy, errTy, ?_⟩
  simpa [lowerFailFunctionType] using h_lowered

/-- Combined contract for Fail-handler lowering to `Result`. -/
structure FailResultContract where
  clause : HandleClauseContract
  okTy : Ty
  errTy : Ty
  loweredTy : Ty
  h_wellTyped : HandleClauseContract.wellTypedSlice clause
  h_failZero : failAsZeroResume clause
  h_lowered : resultLowering okTy errTy loweredTy

/--
Capstone contract consequence:
- handled `Fail` effect is removed from final effects
- resume provenance is zero/one (specialized to zero from Fail contract)
- return type is explicitly `Result ok err`
-/
theorem failResultContract_sound
    (fc : FailResultContract) :
    RowFields.has (EffectRow.fields (HandleClauseContract.resultEffects fc.clause)) failLabel = false ∧
      HandleClauseContract.resumeProvenance fc.clause ∧
      fc.loweredTy = .result fc.okTy fc.errTy := by
  have h_removed_handled :
      RowFields.has (EffectRow.fields (HandleClauseContract.resultEffects fc.clause))
        fc.clause.handled = false :=
    HandleClauseContract.wellTypedSlice_implies_handled_removed fc.clause fc.h_wellTyped
  have h_removed_fail :
      RowFields.has (EffectRow.fields (HandleClauseContract.resultEffects fc.clause)) failLabel = false := by
    simpa [failLabel, fc.h_failZero.1] using h_removed_handled
  exact ⟨h_removed_fail, failAsZeroResume_implies_resumeProvenance fc.clause fc.h_failZero, fc.h_lowered⟩

theorem failResultContract_loopLegal
    (fc : FailResultContract) :
    ResumeUse.loopLegal fc.clause.resumeUse := by
  exact failAsZeroResume_implies_loopLegal fc.clause fc.h_failZero

end FailResultContracts
end Kea
