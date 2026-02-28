import Kea.Properties.CatchTypingBridge

/-!
  Kea.Properties.FailResultEquivalence

  Phase-2 theorem surfaces for catch/result equivalence packaging.
-/

namespace Kea
namespace FailResultEquivalence

theorem fail_result_equivalence
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy : Ty) :
    FailResultContracts.failResultFunctionEquivalent
      (.functionEff params effects okTy)
      (FailResultContracts.lowerFailFunctionType params effects okTy errTy) := by
  refine ⟨params, effects, okTy, errTy, rfl, rfl⟩

theorem fail_result_equivalence_implies_result_return
    (original lowered : Ty)
    (h_eqv : FailResultContracts.failResultFunctionEquivalent original lowered) :
    ∃ params eff okTy errTy,
      lowered = .functionEff params eff (.result okTy errTy) := by
  exact FailResultContracts.failResultFunctionEquivalent_implies_result_return
    original lowered h_eqv

structure FailResultEquivalenceBundle (original lowered : Ty) where
  equivalence : FailResultContracts.failResultFunctionEquivalent original lowered
  resultReturn :
    ∃ params eff okTy errTy,
      lowered = .functionEff params eff (.result okTy errTy)

/-- Structural decomposition for fail-result equivalence bundle. -/
theorem failResultEquivalenceBundle_iff_components
    (original lowered : Ty) :
    FailResultEquivalenceBundle original lowered
      ↔
      FailResultContracts.failResultFunctionEquivalent original lowered
      ∧
      (∃ params eff okTy errTy,
        lowered = .functionEff params eff (.result okTy errTy)) := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.equivalence, h_bundle.resultReturn⟩
  · intro h_comp
    exact {
      equivalence := h_comp.1
      resultReturn := h_comp.2
    }

/-- Constructor helper for fail-result equivalence bundle decomposition. -/
theorem failResultEquivalenceBundle_of_components
    (original lowered : Ty)
    (h_comp :
      FailResultContracts.failResultFunctionEquivalent original lowered
      ∧
      (∃ params eff okTy errTy,
        lowered = .functionEff params eff (.result okTy errTy))) :
    FailResultEquivalenceBundle original lowered :=
  (failResultEquivalenceBundle_iff_components original lowered).2 h_comp

theorem failResultEquivalenceBundle_as_components_of_components
    (original lowered : Ty)
    (h_comp :
      FailResultContracts.failResultFunctionEquivalent original lowered
      ∧
      (∃ params eff okTy errTy,
        lowered = .functionEff params eff (.result okTy errTy))) :
    FailResultContracts.failResultFunctionEquivalent original lowered
    ∧
    (∃ params eff okTy errTy,
      lowered = .functionEff params eff (.result okTy errTy)) :=
  (failResultEquivalenceBundle_iff_components original lowered).1
    (failResultEquivalenceBundle_of_components original lowered h_comp)

/-- One-hop decomposition of fail-result equivalence bundle. -/
theorem failResultEquivalenceBundle_as_components
    (original lowered : Ty)
    (h_bundle : FailResultEquivalenceBundle original lowered) :
    FailResultContracts.failResultFunctionEquivalent original lowered
    ∧
    (∃ params eff okTy errTy,
      lowered = .functionEff params eff (.result okTy errTy)) :=
  (failResultEquivalenceBundle_iff_components original lowered).1 h_bundle

theorem fail_result_equivalence_bundle
    (original lowered : Ty)
    (h_eqv : FailResultContracts.failResultFunctionEquivalent original lowered) :
    FailResultEquivalenceBundle original lowered := by
  exact {
    equivalence := h_eqv
    resultReturn := fail_result_equivalence_implies_result_return original lowered h_eqv
  }

theorem lowerFailFunctionType_equivalence_bundle
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy : Ty) :
    FailResultEquivalenceBundle
      (.functionEff params effects okTy)
      (FailResultContracts.lowerFailFunctionType params effects okTy errTy) := by
  exact fail_result_equivalence_bundle
    (.functionEff params effects okTy)
    (FailResultContracts.lowerFailFunctionType params effects okTy errTy)
    (fail_result_equivalence params effects okTy errTy)

theorem lowerFailFunctionType_equivalence_bundle_as_components
    (params : TyList)
    (effects : EffectRow)
    (okTy errTy : Ty) :
    FailResultContracts.failResultFunctionEquivalent
      (.functionEff params effects okTy)
      (FailResultContracts.lowerFailFunctionType params effects okTy errTy)
    ∧
    (∃ params' eff' okTy' errTy',
      FailResultContracts.lowerFailFunctionType params effects okTy errTy =
        .functionEff params' eff' (.result okTy' errTy')) :=
  failResultEquivalenceBundle_as_components
    (.functionEff params effects okTy)
    (FailResultContracts.lowerFailFunctionType params effects okTy errTy)
    (lowerFailFunctionType_equivalence_bundle params effects okTy errTy)

theorem catchTyping_fail_result_equivalence_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    FailResultContracts.failResultFunctionEquivalent
      (.functionEff params clause.exprEffects okTy)
      loweredTy := by
  have _h_catch_sound :=
    CatchTypingBridge.catchTypingJudgment_sound_of_premises
      clause params okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_lowered
  refine ⟨params, clause.exprEffects, okTy, errTy, rfl, ?_⟩
  exact h_lowered

theorem catchTyping_fail_result_equivalence_of_fail_present
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    FailResultContracts.failResultFunctionEquivalent
      (.functionEff params clause.exprEffects okTy)
      loweredTy := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact catchTyping_fail_result_equivalence_of_premises
    clause params okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_lowered

theorem catchTyping_fail_result_equivalence_bundle_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    FailResultEquivalenceBundle
      (.functionEff params clause.exprEffects okTy)
      loweredTy := by
  exact fail_result_equivalence_bundle
    (.functionEff params clause.exprEffects okTy)
    loweredTy
    (catchTyping_fail_result_equivalence_of_premises
      clause params okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_lowered)

theorem catchTyping_fail_result_equivalence_bundle_of_fail_present
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    FailResultEquivalenceBundle
      (.functionEff params clause.exprEffects okTy)
      loweredTy := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact catchTyping_fail_result_equivalence_bundle_of_premises
    clause params okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_lowered

theorem catchTyping_fail_result_equivalence_bundle_as_components_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    FailResultContracts.failResultFunctionEquivalent
      (.functionEff params clause.exprEffects okTy)
      loweredTy
    ∧
    (∃ params' eff' okTy' errTy',
      loweredTy = .functionEff params' eff' (.result okTy' errTy')) :=
  failResultEquivalenceBundle_as_components
    (.functionEff params clause.exprEffects okTy)
    loweredTy
    (catchTyping_fail_result_equivalence_bundle_of_premises
      clause params okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_lowered)

theorem catchTyping_fail_result_equivalence_bundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    FailResultContracts.failResultFunctionEquivalent
      (.functionEff params clause.exprEffects okTy)
      loweredTy
    ∧
    (∃ params' eff' okTy' errTy',
      loweredTy = .functionEff params' eff' (.result okTy' errTy')) := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact catchTyping_fail_result_equivalence_bundle_as_components_of_premises
    clause params okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_lowered

theorem catchTyping_fail_result_equivalence_result_return_of_premises
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    ∃ params' eff' okTy' errTy',
      loweredTy = .functionEff params' eff' (.result okTy' errTy') :=
  (catchTyping_fail_result_equivalence_bundle_of_premises
    clause params okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_lowered).resultReturn

theorem catchTyping_fail_result_equivalence_result_return_of_fail_present
    (clause : HandleClauseContract)
    (params : TyList)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          params
          clause.exprEffects
          okTy
          errTy) :
    ∃ params' eff' okTy' errTy',
      loweredTy = .functionEff params' eff' (.result okTy' errTy') := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact catchTyping_fail_result_equivalence_result_return_of_premises
    clause params okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_lowered

end FailResultEquivalence
end Kea
