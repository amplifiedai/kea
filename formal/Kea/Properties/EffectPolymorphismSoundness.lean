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
Runtime-aligned strengthening of `EffectPolyFailLoweringContract`:
`catch` is only modeled on effect rows that contain `Fail`.
-/
structure AdmissibleEffectPolyFailLoweringContract extends EffectPolyFailLoweringContract where
  h_admissible : FailResultContracts.catchAdmissible effects

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

theorem effectPolyFailLowering_sound_of_catchAdmissible
    (c : EffectPolyFailLoweringContract)
    (_h_adm : FailResultContracts.catchAdmissible c.effects) :
    ∃ loweredEffects,
      c.lowered = .functionEff c.params loweredEffects (.result c.okTy c.errTy) ∧
      rowTailStable c.effects loweredEffects ∧
      labelsPreservedExcept c.effects loweredEffects FailResultContracts.failLabel ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  exact effectPolyFailLowering_sound c

theorem admissibleEffectPolyFailLowering_sound
    (c : AdmissibleEffectPolyFailLoweringContract) :
    ∃ loweredEffects,
      c.lowered = .functionEff c.params loweredEffects (.result c.okTy c.errTy) ∧
      rowTailStable c.effects loweredEffects ∧
      labelsPreservedExcept c.effects loweredEffects FailResultContracts.failLabel ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  exact effectPolyFailLowering_sound_of_catchAdmissible c.toEffectPolyFailLoweringContract c.h_admissible

theorem admissibleEffectPolyFailLowering_rowTailStable
    (c : AdmissibleEffectPolyFailLoweringContract) :
    ∃ loweredEffects,
      c.lowered = .functionEff c.params loweredEffects (.result c.okTy c.errTy) ∧
      rowTailStable c.effects loweredEffects := by
  rcases admissibleEffectPolyFailLowering_sound c with
    ⟨loweredEffects, h_ty, h_tail, _h_preserve, _h_removed⟩
  exact ⟨loweredEffects, h_ty, h_tail⟩

theorem admissibleEffectPolyFailLowering_preserves_nonFail
    (c : AdmissibleEffectPolyFailLoweringContract) :
    ∃ loweredEffects,
      c.lowered = .functionEff c.params loweredEffects (.result c.okTy c.errTy) ∧
      labelsPreservedExcept c.effects loweredEffects FailResultContracts.failLabel := by
  rcases admissibleEffectPolyFailLowering_sound c with
    ⟨loweredEffects, h_ty, _h_tail, h_preserve, _h_removed⟩
  exact ⟨loweredEffects, h_ty, h_preserve⟩

theorem admissibleEffectPolyFailLowering_failRemoved
    (c : AdmissibleEffectPolyFailLoweringContract) :
    ∃ loweredEffects,
      c.lowered = .functionEff c.params loweredEffects (.result c.okTy c.errTy) ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  rcases admissibleEffectPolyFailLowering_sound c with
    ⟨loweredEffects, h_ty, _h_tail, _h_preserve, h_removed⟩
  exact ⟨loweredEffects, h_ty, h_removed⟩

structure AdmissibleEffectPolyLoweringBundle
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy lowered : Ty) where
  loweredEffects : EffectRow
  loweredEq :
    lowered = .functionEff params loweredEffects (.result okTy errTy)
  rowTailStable :
    rowTailStable effects loweredEffects
  preservesNonFail :
    labelsPreservedExcept effects loweredEffects FailResultContracts.failLabel
  failRemoved :
    RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false

noncomputable def admissibleEffectPolyFailLowering_bundle
    (c : AdmissibleEffectPolyFailLoweringContract) :
    AdmissibleEffectPolyLoweringBundle c.params c.effects c.okTy c.errTy c.lowered :=
  let h := admissibleEffectPolyFailLowering_sound c
  let loweredEffects := Classical.choose h
  let hspec := Classical.choose_spec h
  {
    loweredEffects := loweredEffects
    loweredEq := hspec.1
    rowTailStable := hspec.2.1
    preservesNonFail := hspec.2.2.1
    failRemoved := hspec.2.2.2
  }

theorem admissibleEffectPolyFailLowering_bundle_rowTailStable
    (c : AdmissibleEffectPolyFailLoweringContract) :
    rowTailStable c.effects
      (admissibleEffectPolyFailLowering_bundle c).loweredEffects :=
  (admissibleEffectPolyFailLowering_bundle c).rowTailStable

theorem admissibleEffectPolyFailLowering_bundle_preserves_nonFail
    (c : AdmissibleEffectPolyFailLoweringContract) :
    labelsPreservedExcept c.effects
      (admissibleEffectPolyFailLowering_bundle c).loweredEffects
      FailResultContracts.failLabel :=
  (admissibleEffectPolyFailLowering_bundle c).preservesNonFail

theorem admissibleEffectPolyFailLowering_bundle_failRemoved
    (c : AdmissibleEffectPolyFailLoweringContract) :
    RowFields.has
      (EffectRow.fields (admissibleEffectPolyFailLowering_bundle c).loweredEffects)
      FailResultContracts.failLabel = false :=
  (admissibleEffectPolyFailLowering_bundle c).failRemoved

def mkAdmissibleEffectPolyFailLoweringContract
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy lowered : Ty)
    (h_lowered :
      lowered = FailResultContracts.lowerFailFunctionType params effects okTy errTy)
    (h_admissible : FailResultContracts.catchAdmissible effects) :
    AdmissibleEffectPolyFailLoweringContract := {
  params := params
  effects := effects
  okTy := okTy
  errTy := errTy
  lowered := lowered
  h_lowered := h_lowered
  h_admissible := h_admissible
}

theorem admissibleEffectPolyFailLowering_sound_of_premises
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy lowered : Ty)
    (h_lowered :
      lowered = FailResultContracts.lowerFailFunctionType params effects okTy errTy)
    (h_admissible : FailResultContracts.catchAdmissible effects) :
    ∃ loweredEffects,
      lowered = .functionEff params loweredEffects (.result okTy errTy) ∧
      rowTailStable effects loweredEffects ∧
      labelsPreservedExcept effects loweredEffects FailResultContracts.failLabel ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  let c := mkAdmissibleEffectPolyFailLoweringContract
    params effects okTy errTy lowered h_lowered h_admissible
  exact admissibleEffectPolyFailLowering_sound c

theorem effectPolyFailLowering_noop_if_fail_absent
    (c : EffectPolyFailLoweringContract)
    (h_abs :
      RowFields.has (EffectRow.fields c.effects) FailResultContracts.failLabel = false) :
    c.lowered = .functionEff c.params c.effects (.result c.okTy c.errTy) := by
  exact c.h_lowered.trans
    (FailResultContracts.lowerFailFunctionType_noop_effect_of_absent
      c.params c.effects c.okTy c.errTy h_abs)

theorem effectPolyFailLowering_noop_if_catch_unnecessary
    (c : EffectPolyFailLoweringContract)
    (h_unnecessary : FailResultContracts.catchUnnecessary c.effects) :
    c.lowered = .functionEff c.params c.effects (.result c.okTy c.errTy) := by
  exact effectPolyFailLowering_noop_if_fail_absent c h_unnecessary

theorem catchUnnecessary_implies_no_admissible_poly_lowering
    (c : EffectPolyFailLoweringContract)
    (h_unnecessary : FailResultContracts.catchUnnecessary c.effects) :
    ¬ FailResultContracts.catchAdmissible c.effects := by
  exact FailResultContracts.catchUnnecessary_implies_not_admissible c.effects h_unnecessary

theorem admissibleEffectPolyFailLowering_admissibility_branch
    (c : AdmissibleEffectPolyFailLoweringContract) :
    FailResultContracts.catchAdmissible c.effects ∧
      ¬ FailResultContracts.catchUnnecessary c.effects := by
  exact ⟨
    c.h_admissible,
    FailResultContracts.catchAdmissible_implies_not_unnecessary
      c.effects c.h_admissible
  ⟩

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
Runtime-aligned schema specialization: handler schema + `catch` admissibility.
-/
structure AdmissibleEffectPolyHandlerSchema extends EffectPolyHandlerSchema where
  h_admissible : FailResultContracts.catchAdmissible clause.exprEffects

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
    HandlerClosedAwareContracts.wellTypedSlice_implies_handled_removed_legacy_via_closedAware
      s.clause s.h_wellTyped
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

theorem effectPolyHandlerSchema_noop_if_catch_unnecessary
    (s : EffectPolyHandlerSchema)
    (h_unnecessary :
      FailResultContracts.catchUnnecessary s.clause.exprEffects) :
    s.loweredTy = .functionEff s.params s.clause.exprEffects (.result s.okTy s.errTy) := by
  exact effectPolyHandlerSchema_noop_if_fail_absent s h_unnecessary

theorem catchUnnecessary_implies_no_admissible_schema
    (s : EffectPolyHandlerSchema)
    (h_unnecessary :
      FailResultContracts.catchUnnecessary s.clause.exprEffects) :
    ¬ FailResultContracts.catchAdmissible s.clause.exprEffects := by
  exact FailResultContracts.catchUnnecessary_implies_not_admissible
    s.clause.exprEffects h_unnecessary

theorem admissibleEffectPolyHandlerSchema_sound
    (s : AdmissibleEffectPolyHandlerSchema) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects s.clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        s.loweredTy = .functionEff s.params loweredEffects (.result s.okTy s.errTy) ∧
        rowTailStable s.clause.exprEffects loweredEffects ∧
        labelsPreservedExcept s.clause.exprEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  exact effectPolyHandlerSchema_sound s.toEffectPolyHandlerSchema

theorem admissibleEffectPolyHandlerSchema_rowTailStable
    (s : AdmissibleEffectPolyHandlerSchema) :
    ∃ loweredEffects,
      s.loweredTy = .functionEff s.params loweredEffects (.result s.okTy s.errTy) ∧
      rowTailStable s.clause.exprEffects loweredEffects := by
  rcases admissibleEffectPolyHandlerSchema_sound s with
    ⟨_h_clause_removed, loweredEffects, h_ty, h_tail, _h_preserve, _h_removed⟩
  exact ⟨loweredEffects, h_ty, h_tail⟩

theorem admissibleEffectPolyHandlerSchema_preserves_nonFail
    (s : AdmissibleEffectPolyHandlerSchema) :
    ∃ loweredEffects,
      s.loweredTy = .functionEff s.params loweredEffects (.result s.okTy s.errTy) ∧
      labelsPreservedExcept s.clause.exprEffects loweredEffects FailResultContracts.failLabel := by
  rcases admissibleEffectPolyHandlerSchema_sound s with
    ⟨_h_clause_removed, loweredEffects, h_ty, _h_tail, h_preserve, _h_removed⟩
  exact ⟨loweredEffects, h_ty, h_preserve⟩

theorem admissibleEffectPolyHandlerSchema_failRemoved_in_lowered_effects
    (s : AdmissibleEffectPolyHandlerSchema) :
    ∃ loweredEffects,
      s.loweredTy = .functionEff s.params loweredEffects (.result s.okTy s.errTy) ∧
      RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  rcases admissibleEffectPolyHandlerSchema_sound s with
    ⟨_h_clause_removed, loweredEffects, h_ty, _h_tail, _h_preserve, h_removed⟩
  exact ⟨loweredEffects, h_ty, h_removed⟩

structure AdmissibleEffectPolyHandlerBundle
    (s : AdmissibleEffectPolyHandlerSchema) where
  clauseFailRemoved :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects s.clause))
      FailResultContracts.failLabel = false
  lowering :
    AdmissibleEffectPolyLoweringBundle
      s.params s.clause.exprEffects s.okTy s.errTy s.loweredTy

noncomputable def admissibleEffectPolyHandler_bundle
    (s : AdmissibleEffectPolyHandlerSchema) :
    AdmissibleEffectPolyHandlerBundle s :=
  let h := admissibleEffectPolyHandlerSchema_sound s
  let h_clause_removed := h.1
  let h_lowering := h.2
  let loweredEffects := Classical.choose h_lowering
  let hspec := Classical.choose_spec h_lowering
  {
    clauseFailRemoved := h_clause_removed
    lowering := {
      loweredEffects := loweredEffects
      loweredEq := hspec.1
      rowTailStable := hspec.2.1
      preservesNonFail := hspec.2.2.1
      failRemoved := hspec.2.2.2
    }
  }

theorem admissibleEffectPolyHandler_bundle_clauseFailRemoved
    (s : AdmissibleEffectPolyHandlerSchema) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects s.clause))
      FailResultContracts.failLabel = false :=
  (admissibleEffectPolyHandler_bundle s).clauseFailRemoved

theorem admissibleEffectPolyHandler_bundle_rowTailStable
    (s : AdmissibleEffectPolyHandlerSchema) :
    rowTailStable s.clause.exprEffects
      (admissibleEffectPolyHandler_bundle s).lowering.loweredEffects :=
  (admissibleEffectPolyHandler_bundle s).lowering.rowTailStable

theorem admissibleEffectPolyHandler_bundle_preserves_nonFail
    (s : AdmissibleEffectPolyHandlerSchema) :
    labelsPreservedExcept s.clause.exprEffects
      (admissibleEffectPolyHandler_bundle s).lowering.loweredEffects
      FailResultContracts.failLabel :=
  (admissibleEffectPolyHandler_bundle s).lowering.preservesNonFail

theorem admissibleEffectPolyHandler_bundle_failRemoved_in_lowered
    (s : AdmissibleEffectPolyHandlerSchema) :
    RowFields.has
      (EffectRow.fields (admissibleEffectPolyHandler_bundle s).lowering.loweredEffects)
      FailResultContracts.failLabel = false :=
  (admissibleEffectPolyHandler_bundle s).lowering.failRemoved

theorem admissibleEffectPolyHandlerSchema_not_unnecessary
    (s : AdmissibleEffectPolyHandlerSchema) :
    ¬ FailResultContracts.catchUnnecessary s.clause.exprEffects := by
  intro h_unnecessary
  have h_not_adm :=
    FailResultContracts.catchUnnecessary_implies_not_admissible
      s.clause.exprEffects h_unnecessary
  exact h_not_adm s.h_admissible

theorem admissibleEffectPolyHandlerSchema_admissibility_branch
    (s : AdmissibleEffectPolyHandlerSchema) :
    FailResultContracts.catchAdmissible s.clause.exprEffects ∧
      ¬ FailResultContracts.catchUnnecessary s.clause.exprEffects := by
  exact ⟨s.h_admissible, admissibleEffectPolyHandlerSchema_not_unnecessary s⟩

def mkAdmissibleEffectPolyHandlerSchema
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects) :
    AdmissibleEffectPolyHandlerSchema := {
  clause := clause
  params := params
  okTy := okTy
  errTy := errTy
  loweredTy := loweredTy
  h_wellTyped := h_wellTyped
  h_failZero := h_failZero
  h_lowered := h_lowered
  h_admissible := h_admissible
}

theorem admissibleEffectPolyHandlerSchema_sound_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType params clause.exprEffects okTy errTy)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      FailResultContracts.failLabel = false ∧
      ∃ loweredEffects,
        loweredTy = .functionEff params loweredEffects (.result okTy errTy) ∧
        rowTailStable clause.exprEffects loweredEffects ∧
        labelsPreservedExcept clause.exprEffects loweredEffects FailResultContracts.failLabel ∧
        RowFields.has (EffectRow.fields loweredEffects) FailResultContracts.failLabel = false := by
  let s := mkAdmissibleEffectPolyHandlerSchema
    clause params okTy errTy loweredTy h_wellTyped h_failZero h_lowered h_admissible
  exact admissibleEffectPolyHandlerSchema_sound s

end EffectPolymorphismSoundness
end Kea
