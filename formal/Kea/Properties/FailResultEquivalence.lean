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

end FailResultEquivalence
end Kea
