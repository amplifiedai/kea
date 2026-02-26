/-
  Kea.Properties.EffectPolymorphismSoundness

  Phase-2 contract surfaces for effect-polymorphism soundness under Fail
  lowering:
  - remove only the handled `Fail` label
  - preserve all non-`Fail` labels
  - preserve row-tail openness (rest variable)
-/

import Kea.Properties.FailResultContracts

namespace Kea
namespace EffectPolymorphismSoundness

/-- Row-tail stability relation between two effect rows. -/
def rowTailStable (before after : EffectRow) : Prop :=
  EffectRow.rest after = EffectRow.rest before

/-- Label-preservation relation except for one handled target label. -/
def labelsPreservedExcept
    (before after : EffectRow)
    (target : Label) : Prop :=
  ∀ other, other ≠ target →
    RowFields.has (EffectRow.fields after) other =
      RowFields.has (EffectRow.fields before) other

theorem lowerFailEffects_rowTailStable
    (effects : EffectRow) :
    rowTailStable effects (FailResultContracts.lowerFailEffects effects) := by
  unfold rowTailStable FailResultContracts.lowerFailEffects
  exact EffectRow.handle_preserves_row_tail effects FailResultContracts.failLabel

theorem lowerFailEffects_labelsPreservedExceptFail
    (effects : EffectRow) :
    labelsPreservedExcept effects
      (FailResultContracts.lowerFailEffects effects)
      FailResultContracts.failLabel := by
  intro other h_ne
  exact FailResultContracts.lowerFailEffects_preserves_other effects other h_ne

theorem lowerFailEffects_failRemoved
    (effects : EffectRow) :
    RowFields.has
      (EffectRow.fields (FailResultContracts.lowerFailEffects effects))
      FailResultContracts.failLabel = false := by
  exact FailResultContracts.lowerFailEffects_removes_fail effects

/-- Combined effect-polymorphism soundness slice for Fail lowering on effect rows. -/
theorem lowerFailEffects_effectPoly_sound
    (effects : EffectRow) :
    rowTailStable effects (FailResultContracts.lowerFailEffects effects) ∧
      labelsPreservedExcept effects
        (FailResultContracts.lowerFailEffects effects)
        FailResultContracts.failLabel ∧
      RowFields.has
        (EffectRow.fields (FailResultContracts.lowerFailEffects effects))
        FailResultContracts.failLabel = false := by
  exact ⟨
    lowerFailEffects_rowTailStable effects,
    lowerFailEffects_labelsPreservedExceptFail effects,
    lowerFailEffects_failRemoved effects
  ⟩

/-- Contract for a polymorphic function type lowered by Fail handling. -/
structure EffectPolyFailLoweringContract where
  params : TyList
  effects : EffectRow
  okTy : Ty
  errTy : Ty
  lowered : Ty
  h_lowered :
    lowered = FailResultContracts.lowerFailFunctionType params effects okTy errTy

/--
Capstone: lowered polymorphic function type preserves tail polymorphism and all
non-`Fail` effects while removing `Fail`.
-/
theorem effectPolyFailLowering_sound
    (c : EffectPolyFailLoweringContract) :
    ∃ loweredEffects,
      c.lowered = .functionEff c.params loweredEffects (.result c.okTy c.errTy) ∧
      rowTailStable c.effects loweredEffects ∧
      labelsPreservedExcept c.effects loweredEffects FailResultContracts.failLabel ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  refine ⟨FailResultContracts.lowerFailEffects c.effects, ?_⟩
  refine ⟨?h_ty, ?h_tail, ?h_preserve, ?h_removed⟩
  · simpa [FailResultContracts.lowerFailFunctionType] using c.h_lowered
  · exact lowerFailEffects_rowTailStable c.effects
  · exact lowerFailEffects_labelsPreservedExceptFail c.effects
  · exact lowerFailEffects_failRemoved c.effects

theorem effectPolyFailLowering_noop_if_fail_absent
    (c : EffectPolyFailLoweringContract)
    (h_abs :
      RowFields.has (EffectRow.fields c.effects) FailResultContracts.failLabel = false) :
    c.lowered = .functionEff c.params c.effects (.result c.okTy c.errTy) := by
  exact c.h_lowered.trans
    (FailResultContracts.lowerFailFunctionType_noop_effect_of_absent
      c.params c.effects c.okTy c.errTy h_abs)

/-- Concrete handler-typing premises for polymorphic Fail-lowered function schemas. -/
structure EffectPolyHandlerSchema where
  clause : HandleClauseContract
  params : TyList
  okTy : Ty
  errTy : Ty
  loweredTy : Ty
  h_wellTyped : HandleClauseContract.wellTypedSlice clause
  h_failZero : FailResultContracts.failAsZeroResume clause
  h_lowered :
    loweredTy =
      FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy

/--
Bridge theorem: concrete handler typing premises imply the polymorphic
Fail-lowering soundness slice and handled-effect removal at the clause result.
-/
theorem effectPolyHandlerSchema_sound
    (s : EffectPolyHandlerSchema) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects s.clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        s.loweredTy = .functionEff s.params loweredEffects (.result s.okTy s.errTy) ∧
        rowTailStable s.clause.exprEffects loweredEffects ∧
        labelsPreservedExcept s.clause.exprEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  have h_removed_handled :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects s.clause))
        s.clause.handled = false :=
    HandleClauseContract.wellTypedSlice_implies_handled_removed s.clause s.h_wellTyped
  have h_removed_fail :
      RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects s.clause))
        FailResultContracts.failLabel = false := by
    simpa [FailResultContracts.failLabel, s.h_failZero.1] using h_removed_handled
  let poly : EffectPolyFailLoweringContract := {
    params := s.params
    effects := s.clause.exprEffects
    okTy := s.okTy
    errTy := s.errTy
    lowered := s.loweredTy
    h_lowered := s.h_lowered
  }
  have h_poly := effectPolyFailLowering_sound poly
  exact ⟨h_removed_fail, h_poly⟩

theorem effectPolyHandlerSchema_noop_if_fail_absent
    (s : EffectPolyHandlerSchema)
    (h_abs :
      RowFields.has (EffectRow.fields s.clause.exprEffects)
        FailResultContracts.failLabel = false) :
    s.loweredTy = .functionEff s.params s.clause.exprEffects (.result s.okTy s.errTy) := by
  let poly : EffectPolyFailLoweringContract := {
    params := s.params
    effects := s.clause.exprEffects
    okTy := s.okTy
    errTy := s.errTy
    lowered := s.loweredTy
    h_lowered := s.h_lowered
  }
  exact effectPolyFailLowering_noop_if_fail_absent poly h_abs

end EffectPolymorphismSoundness
end Kea
