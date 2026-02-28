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

/-- Build capstone interoperability suite from direct Fail-presence evidence. -/
theorem catchCapstoneInteropSuite_of_fail_present
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
          (higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy := by
  have h_admissible : FailResultContracts.catchAdmissible clause.exprEffects :=
    (FailResultContracts.catchAdmissible_iff_fail_present clause.exprEffects).2 h_fail_present
  exact catchCapstoneInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered

/-- Build classifier interoperability suite from direct Fail-presence evidence. -/
theorem catchClassifierInteropSuite_of_fail_present
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
          (higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy :=
  catchClassifierInteropSuite_of_capstoneInteropSuite
    clause innerEffects okTy errTy loweredTy
    (catchCapstoneInteropSuite_of_fail_present
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered)

/-- Build classifier interoperability suite from a generic classifier outcome. -/
theorem catchClassifierInteropSuite_of_genericClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy := by
  let laws :=
    HigherOrderCatchContracts.higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  refine {
    laws := laws
    genericClassified := h_generic
    higherClassified := ?_
  }
  exact HigherOrderCatchContracts.higherOrderCatchBridgeLaws_generic_to_classification
    clause innerEffects okTy errTy loweredTy laws h_generic

/-- Build classifier interoperability suite from a higher-order classifier outcome. -/
theorem catchClassifierInteropSuite_of_higherClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_higher :
      HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary innerEffects) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy := by
  let laws :=
    HigherOrderCatchContracts.higherOrderCatchBridgeLaws_of_clauseEffects
      clause innerEffects okTy errTy loweredTy h_clauseEffects
  refine {
    laws := laws
    genericClassified := ?_
    higherClassified := h_higher
  }
  exact HigherOrderCatchContracts.higherOrderCatchBridgeLaws_classification_to_generic
    clause innerEffects okTy errTy loweredTy laws h_higher

/-- One-hop projection: generic capstone branch from capstone interoperability suite. -/
theorem catchCapstoneInteropSuite_generic
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy :=
  h_suite.genericCapstone

/-- One-hop projection: higher-order capstone branch from capstone interoperability suite. -/
theorem catchCapstoneInteropSuite_higher
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  h_suite.higherCapstone

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
