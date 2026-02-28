import Kea.Properties.HandlerClosedAwareContracts
import Kea.Properties.TailCapabilityComposition
import Kea.Properties.CatchInteroperabilitySuite

/-!
  Kea.Properties.EffectHandlerContractSuite

  Phase-2 aggregate package that combines:
  - closed-aware clause guarantees
  - closed-aware capability preservation
  - generic<->higher-order catch interoperability
-/

namespace Kea
namespace EffectHandlerContractSuite

/--
Aggregate Phase-2 suite for one clause:
- closed-aware handler guarantees
- closed-aware capability preservation for one capability label
- catch classifier interoperability for one lowering schema
-/
structure EffectHandlerSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop where
  closedAware :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
  capabilityClosedAware :
    TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
  catchInterop :
    CatchInteroperabilitySuite.CatchClassifierInteropSuite
      clause innerEffects okTy errTy loweredTy

/-- Aggregate suite is equivalent to explicit component bundles. -/
theorem effectHandlerSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy
      ↔ (HandlerClosedAwareContracts.ClosedAwareResultBundle clause
          ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
          ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
              clause innerEffects okTy errTy loweredTy) := by
  constructor
  · intro h_suite
    exact ⟨h_suite.closedAware, h_suite.capabilityClosedAware, h_suite.catchInterop⟩
  · intro h_comp
    exact ⟨h_comp.1, h_comp.2.1, h_comp.2.2⟩

/-- Build aggregate suite directly from explicit component bundles. -/
theorem effectHandlerSuite_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      HandlerClosedAwareContracts.ClosedAwareResultBundle clause
        ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
        ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
            clause innerEffects okTy errTy loweredTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerSuite_iff_components clause capability innerEffects okTy errTy loweredTy).2 h_comp

/-- One-hop decomposition of aggregate suite into explicit component bundles. -/
theorem effectHandlerSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  (effectHandlerSuite_iff_components clause capability innerEffects okTy errTy loweredTy).1 h_suite

/-- Build the aggregate suite from well-typed + catch premise inputs. -/
theorem effectHandlerSuite_of_premises
    (clause : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_cap_ne : capability ≠ clause.handled)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy := by
  refine {
    closedAware :=
      HandlerClosedAwareContracts.closedAwareResultBundle_of_wellTyped clause h_wellTyped
    capabilityClosedAware :=
      TailCapabilityComposition.tailCapabilityClosedAwareBundle_of_wellTyped
        clause baseEffects capability h_wellTyped h_expr h_cap_ne
    catchInterop :=
      CatchInteroperabilitySuite.catchClassifierInteropSuite_of_premises
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_clauseEffects h_lowered
  }

/-- Build the aggregate suite from direct Fail-presence evidence. -/
theorem effectHandlerSuite_of_fail_present
    (clause : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_cap_ne : capability ≠ clause.handled)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy := by
  refine {
    closedAware :=
      HandlerClosedAwareContracts.closedAwareResultBundle_of_wellTyped clause h_wellTyped
    capabilityClosedAware :=
      TailCapabilityComposition.tailCapabilityClosedAwareBundle_of_wellTyped
        clause baseEffects capability h_wellTyped h_expr h_cap_ne
    catchInterop :=
      CatchInteroperabilitySuite.catchClassifierInteropSuite_of_fail_present
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered
  }

/-- One-hop projection: closed-aware handled-removal guarantee from aggregate suite. -/
theorem effectHandlerSuite_closedAwareHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  h_suite.closedAware.closedAwareHandledRemoved

/-- One-hop projection: closed-aware capability preservation from aggregate suite. -/
theorem effectHandlerSuite_closedAwareCapability
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  h_suite.capabilityClosedAware.closedAwareResultCapability

/-- One-hop projection: closed-aware row-tail stability from aggregate suite. -/
theorem effectHandlerSuite_closedAwareRowTailStable
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  h_suite.closedAware.closedAwareRowTailStable

/-- One-hop projection: legacy handled-removal guarantee from aggregate suite. -/
theorem effectHandlerSuite_legacyHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  h_suite.closedAware.legacyHandledRemoved

/-- One-hop projection: non-invalid tail classification from aggregate suite. -/
theorem effectHandlerSuite_tailNotInvalid
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  h_suite.capabilityClosedAware.notInvalid

/-- One-hop projection: generic catch classifier branch from aggregate suite. -/
theorem effectHandlerSuite_genericCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  CatchInteroperabilitySuite.catchClassifierInteropSuite_generic
    clause innerEffects okTy errTy loweredTy h_suite.catchInterop

/-- One-hop projection: higher-order catch classifier branch from aggregate suite. -/
theorem effectHandlerSuite_higherCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  CatchInteroperabilitySuite.catchClassifierInteropSuite_higher
    clause innerEffects okTy errTy loweredTy h_suite.catchInterop

end EffectHandlerContractSuite
end Kea
