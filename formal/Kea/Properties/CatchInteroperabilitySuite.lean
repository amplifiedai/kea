import Kea.Properties.HigherOrderCatchContracts

/-!
  Kea.Properties.CatchInteroperabilitySuite

  Packaged interoperability surfaces between generic catch bridge outcomes and
  higher-order catch specialization outcomes.
-/

namespace Kea
namespace CatchInteroperabilitySuite

/-- Canonical higher-order parameter shape used by interoperability suites. -/
abbrev higherOrderParams (innerEffects : EffectRow) (okTy : Ty) : TyList :=
  .cons (HigherOrderCatchContracts.higherOrderParamType innerEffects okTy) .nil

/--
Classifier-level interoperability suite: generic and higher-order classifiers
plus their bridge laws under clause-effect identification.
-/
structure CatchClassifierInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop where
  laws : HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
  genericClassified :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects
  higherClassified :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects

/--
Capstone-level interoperability suite: generic and higher-order capstones plus
their bridge laws under clause-effect identification.
-/
structure CatchCapstoneInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop where
  laws : HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
  genericCapstone :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
  higherCapstone :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy

/-- Build classifier interoperability suite from premise-level classifier inputs. -/
theorem catchClassifierInteropSuite_of_premises
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy := by
  let laws :=
    HigherOrderCatchContracts.higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  let genericClassified :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
    CatchTypingBridge.catchTypingJudgment_classify_of_premises
      clause
      (higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_lowered
  refine {
    laws := laws
    genericClassified := genericClassified
    higherClassified := ?_
  }
  exact HigherOrderCatchContracts.higherOrderCatchBridgeLaws_generic_to_classification
    clause innerEffects okTy errTy loweredTy laws genericClassified

/-- Build capstone interoperability suite from premise-level capstone inputs. -/
theorem catchCapstoneInteropSuite_of_premises
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
          (higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy := by
  let laws :=
    HigherOrderCatchContracts.higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  let genericCapstone :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy :=
    CatchTypingBridge.catchTypingJudgment_capstone_of_premises
      clause
      (higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      h_wellTyped
      h_failZero
      h_admissible
      h_lowered
  refine {
    laws := laws
    genericCapstone := genericCapstone
    higherCapstone := ?_
  }
  exact HigherOrderCatchContracts.higherOrderCatchBridgeLaws_generic_to_capstone
    clause innerEffects okTy errTy loweredTy laws genericCapstone

/-- Capstone interoperability implies classifier interoperability by left-injection. -/
theorem catchClassifierInteropSuite_of_capstoneInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy := by
  refine {
    laws := h_cap.laws
    genericClassified := Or.inl h_cap.genericCapstone
    higherClassified := Or.inl h_cap.higherCapstone
  }

/-- One-hop projection: generic classifier branch from classifier interoperability suite. -/
theorem catchClassifierInteropSuite_generic
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  h_suite.genericClassified

/-- One-hop projection: higher-order classifier branch from classifier interoperability suite. -/
theorem catchClassifierInteropSuite_higher
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  h_suite.higherClassified

end CatchInteroperabilitySuite
end Kea
