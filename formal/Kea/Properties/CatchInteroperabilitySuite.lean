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

/-- Classifier interoperability suite is equivalent to explicit component fields. -/
theorem catchClassifierInteropSuite_iff_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy
      ↔ (HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
          ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
                clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
                ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
          ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
                clause innerEffects okTy errTy loweredTy
                ∨ FailResultContracts.catchUnnecessary innerEffects)) := by
  constructor
  · intro h_suite
    exact ⟨h_suite.laws, h_suite.genericClassified, h_suite.higherClassified⟩
  · intro h_comp
    exact ⟨h_comp.1, h_comp.2.1, h_comp.2.2⟩

/-- Build classifier interoperability suite from explicit components. -/
theorem catchClassifierInteropSuite_of_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
        ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
              clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
              ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
        ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
              clause innerEffects okTy errTy loweredTy
              ∨ FailResultContracts.catchUnnecessary innerEffects)) :
    CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy :=
  (catchClassifierInteropSuite_iff_components clause innerEffects okTy errTy loweredTy).2 h_comp

theorem catchClassifierInteropSuite_as_components_of_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
        ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
              clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
              ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
        ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
              clause innerEffects okTy errTy loweredTy
              ∨ FailResultContracts.catchUnnecessary innerEffects)) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) :=
  (catchClassifierInteropSuite_iff_components clause innerEffects okTy errTy loweredTy).1
    (catchClassifierInteropSuite_of_components clause innerEffects okTy errTy loweredTy h_comp)

/-- One-hop decomposition of classifier interoperability suite into explicit components. -/
theorem catchClassifierInteropSuite_as_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) :=
  (catchClassifierInteropSuite_iff_components clause innerEffects okTy errTy loweredTy).1 h_suite

/-- Capstone interoperability suite is equivalent to explicit component fields. -/
theorem catchCapstoneInteropSuite_iff_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy
      ↔ (HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
          ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
              clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
          ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
              clause innerEffects okTy errTy loweredTy) := by
  constructor
  · intro h_suite
    exact ⟨h_suite.laws, h_suite.genericCapstone, h_suite.higherCapstone⟩
  · intro h_comp
    exact ⟨h_comp.1, h_comp.2.1, h_comp.2.2⟩

/-- Build capstone interoperability suite from explicit components. -/
theorem catchCapstoneInteropSuite_of_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
        ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy) :
    CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy :=
  (catchCapstoneInteropSuite_iff_components clause innerEffects okTy errTy loweredTy).2 h_comp

theorem catchCapstoneInteropSuite_as_components_of_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
        ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
          clause innerEffects okTy errTy loweredTy :=
  (catchCapstoneInteropSuite_iff_components clause innerEffects okTy errTy loweredTy).1
    (catchCapstoneInteropSuite_of_components clause innerEffects okTy errTy loweredTy h_comp)

/-- One-hop decomposition of capstone interoperability suite into explicit components. -/
theorem catchCapstoneInteropSuite_as_components
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
          clause innerEffects okTy errTy loweredTy :=
  (catchCapstoneInteropSuite_iff_components clause innerEffects okTy errTy loweredTy).1 h_suite

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

theorem catchClassifierInteropSuite_generic_of_premises
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects := by
  exact (catchClassifierInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_clauseEffects h_lowered).genericClassified

theorem catchClassifierInteropSuite_higher_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects := by
  exact (catchClassifierInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_clauseEffects h_lowered).higherClassified

theorem catchClassifierInteropSuite_laws_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchClassifierInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_clauseEffects h_lowered).laws

theorem catchClassifierInteropSuite_as_components_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) := by
  exact catchClassifierInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchClassifierInteropSuite_of_premises
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_clauseEffects h_lowered)

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

theorem catchCapstoneInteropSuite_generic_of_premises
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy := by
  exact (catchCapstoneInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).genericCapstone

theorem catchCapstoneInteropSuite_higher_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  exact (catchCapstoneInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).higherCapstone

theorem catchCapstoneInteropSuite_laws_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchCapstoneInteropSuite_of_premises
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered).laws

theorem catchCapstoneInteropSuite_as_components_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
          clause innerEffects okTy errTy loweredTy := by
  exact catchCapstoneInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchCapstoneInteropSuite_of_premises
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered)

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

theorem catchClassifierInteropSuite_generic_of_capstoneInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects := by
  exact (catchClassifierInteropSuite_of_capstoneInteropSuite
    clause innerEffects okTy errTy loweredTy h_cap).genericClassified

theorem catchClassifierInteropSuite_higher_of_capstoneInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects := by
  exact (catchClassifierInteropSuite_of_capstoneInteropSuite
    clause innerEffects okTy errTy loweredTy h_cap).higherClassified

theorem catchClassifierInteropSuite_laws_of_capstoneInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchClassifierInteropSuite_of_capstoneInteropSuite
    clause innerEffects okTy errTy loweredTy h_cap).laws

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

theorem catchCapstoneInteropSuite_generic_of_fail_present
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy := by
  exact (catchCapstoneInteropSuite_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).genericCapstone

theorem catchCapstoneInteropSuite_higher_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy := by
  exact (catchCapstoneInteropSuite_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).higherCapstone

theorem catchCapstoneInteropSuite_laws_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchCapstoneInteropSuite_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).laws

theorem catchCapstoneInteropSuite_as_components_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ CatchTypingBridge.CatchTypingCapstoneOutcome
          clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∧ HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
          clause innerEffects okTy errTy loweredTy := by
  exact catchCapstoneInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchCapstoneInteropSuite_of_fail_present
      clause innerEffects okTy errTy loweredTy
      h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered)

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

theorem catchClassifierInteropSuite_generic_of_fail_present
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects := by
  exact (catchClassifierInteropSuite_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).genericClassified

theorem catchClassifierInteropSuite_higher_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects := by
  exact (catchClassifierInteropSuite_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).higherClassified

theorem catchClassifierInteropSuite_laws_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchClassifierInteropSuite_of_fail_present
    clause innerEffects okTy errTy loweredTy
    h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered).laws

theorem catchClassifierInteropSuite_as_components_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) := by
  exact catchClassifierInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchClassifierInteropSuite_of_fail_present
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

theorem catchClassifierInteropSuite_generic_of_genericClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects := by
  exact (catchClassifierInteropSuite_of_genericClassification
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_generic).genericClassified

theorem catchClassifierInteropSuite_higher_of_genericClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects := by
  exact (catchClassifierInteropSuite_of_genericClassification
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_generic).higherClassified

theorem catchClassifierInteropSuite_laws_of_genericClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchClassifierInteropSuite_of_genericClassification
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_generic).laws

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

theorem catchClassifierInteropSuite_generic_of_higherClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_higher :
      HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary innerEffects) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects := by
  exact (catchClassifierInteropSuite_of_higherClassification
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_higher).genericClassified

theorem catchClassifierInteropSuite_higher_of_higherClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_higher :
      HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary innerEffects) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects := by
  exact (catchClassifierInteropSuite_of_higherClassification
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_higher).higherClassified

theorem catchClassifierInteropSuite_laws_of_higherClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_higher :
      HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary innerEffects) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy := by
  exact (catchClassifierInteropSuite_of_higherClassification
    clause innerEffects okTy errTy loweredTy h_clauseEffects h_higher).laws

theorem catchClassifierInteropSuite_as_components_of_genericClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_generic :
      CatchTypingBridge.CatchTypingCapstoneOutcome
        clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary clause.exprEffects) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) := by
  exact catchClassifierInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchClassifierInteropSuite_of_genericClassification
      clause innerEffects okTy errTy loweredTy h_clauseEffects h_generic)

theorem catchClassifierInteropSuite_as_components_of_higherClassification
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_higher :
      HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
        ∨ FailResultContracts.catchUnnecessary innerEffects) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) := by
  exact catchClassifierInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchClassifierInteropSuite_of_higherClassification
      clause innerEffects okTy errTy loweredTy h_clauseEffects h_higher)

theorem catchClassifierInteropSuite_as_components_of_capstoneInteropSuite
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy
      ∧ (CatchTypingBridge.CatchTypingCapstoneOutcome
            clause (higherOrderParams innerEffects okTy) okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary clause.exprEffects)
      ∧ (HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome
            clause innerEffects okTy errTy loweredTy
            ∨ FailResultContracts.catchUnnecessary innerEffects) := by
  exact catchClassifierInteropSuite_as_components
    clause innerEffects okTy errTy loweredTy
    (catchClassifierInteropSuite_of_capstoneInteropSuite
      clause innerEffects okTy errTy loweredTy h_cap)

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

/-- One-hop projection: packaged bridge laws from capstone interoperability suite. -/
theorem catchCapstoneInteropSuite_laws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchCapstoneInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  h_suite.laws

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

/-- One-hop projection: packaged bridge laws from classifier interoperability suite. -/
theorem catchClassifierInteropSuite_laws
    (clause : HandleClauseContract)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : CatchClassifierInteropSuite clause innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  h_suite.laws

end CatchInteroperabilitySuite
end Kea
