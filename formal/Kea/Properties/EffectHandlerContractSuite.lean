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
