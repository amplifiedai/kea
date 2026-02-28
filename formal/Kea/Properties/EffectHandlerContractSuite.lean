import Kea.Properties.HandlerClosedAwareContracts
import Kea.Properties.TailCapabilityComposition
import Kea.Properties.CatchInteroperabilitySuite
import Kea.Properties.NestedHandlerCompositionContracts

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

/--
Stricter aggregate Phase-2 suite for one clause:
- closed-aware handler guarantees
- closed-aware capability preservation for one capability label
- catch capstone interoperability for one lowering schema
-/
structure EffectHandlerCapstoneSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop where
  closedAware :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
  capabilityClosedAware :
    TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
  catchInteropCapstone :
    CatchInteroperabilitySuite.CatchCapstoneInteropSuite
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

/-- Capstone aggregate suite is equivalent to explicit component bundles. -/
theorem effectHandlerCapstoneSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
      ↔ (HandlerClosedAwareContracts.ClosedAwareResultBundle clause
          ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
          ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
              clause innerEffects okTy errTy loweredTy) := by
  constructor
  · intro h_suite
    exact ⟨h_suite.closedAware, h_suite.capabilityClosedAware, h_suite.catchInteropCapstone⟩
  · intro h_comp
    exact ⟨h_comp.1, h_comp.2.1, h_comp.2.2⟩

/-- Build capstone aggregate suite directly from explicit component bundles. -/
theorem effectHandlerCapstoneSuite_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      HandlerClosedAwareContracts.ClosedAwareResultBundle clause
        ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
        ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
            clause innerEffects okTy errTy loweredTy) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerCapstoneSuite_iff_components clause capability innerEffects okTy errTy loweredTy).2 h_comp

/-- One-hop decomposition of capstone aggregate suite into explicit component bundles. -/
theorem effectHandlerCapstoneSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  (effectHandlerCapstoneSuite_iff_components clause capability innerEffects okTy errTy loweredTy).1 h_suite

/--
Capstone aggregate suite downgrades to the classifier aggregate suite via the
capstone-to-classifier interoperability route.
-/
theorem effectHandlerSuite_of_capstoneSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy := by
  refine {
    closedAware := h_cap.closedAware
    capabilityClosedAware := h_cap.capabilityClosedAware
    catchInterop :=
      CatchInteroperabilitySuite.catchClassifierInteropSuite_of_capstoneInteropSuite
        clause innerEffects okTy errTy loweredTy h_cap.catchInteropCapstone
  }

/--
Coherent aggregate suite that carries both classifier-level and capstone-level
catch interoperability witnesses for the same clause/capability surface.
-/
structure EffectHandlerCatchPairSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop where
  capstone :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
  classifier :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy
  classifierFromCapstone :
    classifier =
      effectHandlerSuite_of_capstoneSuite
        clause capability innerEffects okTy errTy loweredTy capstone

/-- Build coherent pair suite directly from a capstone aggregate witness. -/
theorem effectHandlerCatchPairSuite_of_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy := by
  refine {
    capstone := h_cap
    classifier :=
      effectHandlerSuite_of_capstoneSuite
        clause capability innerEffects okTy errTy loweredTy h_cap
    classifierFromCapstone := rfl
  }

/-- Coherent pair suite is equivalent to its capstone aggregate witness. -/
theorem effectHandlerCatchPairSuite_iff_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ↔ EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy := by
  constructor
  · intro h_pair
    exact h_pair.capstone
  · intro h_cap
    exact effectHandlerCatchPairSuite_of_capstone
      clause capability innerEffects okTy errTy loweredTy h_cap

/--
Master Phase-2 composition suite that combines:
- coherent clause-level classifier+capstone catch aggregation
- nested closed-aware same-target composition for an outer handler row
-/
structure EffectHandlerCompositionSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) : Prop where
  catchPair :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
  nestedClosedAware :
    NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled

/-- Master composition suite is equivalent to explicit pair+nested components. -/
theorem effectHandlerCompositionSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler
      ↔ (EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
          ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
              clause.exprEffects
              clause.handlerEffects
              outerHandler
              clause.handled) := by
  constructor
  · intro h_suite
    exact ⟨h_suite.catchPair, h_suite.nestedClosedAware⟩
  · intro h_comp
    exact ⟨h_comp.1, h_comp.2⟩

/-- Build master composition suite from explicit pair+nested components. -/
theorem effectHandlerCompositionSuite_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
        ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).2 h_comp

/-- One-hop decomposition of master composition suite into explicit components. -/
theorem effectHandlerCompositionSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  (effectHandlerCompositionSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1 h_suite

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

/-- Build the capstone aggregate suite from well-typed + catch premise inputs. -/
theorem effectHandlerCapstoneSuite_of_premises
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
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy := by
  refine {
    closedAware :=
      HandlerClosedAwareContracts.closedAwareResultBundle_of_wellTyped clause h_wellTyped
    capabilityClosedAware :=
      TailCapabilityComposition.tailCapabilityClosedAwareBundle_of_wellTyped
        clause baseEffects capability h_wellTyped h_expr h_cap_ne
    catchInteropCapstone :=
      CatchInteroperabilitySuite.catchCapstoneInteropSuite_of_premises
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_admissible h_clauseEffects h_lowered
  }

/-- Build the capstone aggregate suite from direct Fail-presence evidence. -/
theorem effectHandlerCapstoneSuite_of_fail_present
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy := by
  refine {
    closedAware :=
      HandlerClosedAwareContracts.closedAwareResultBundle_of_wellTyped clause h_wellTyped
    capabilityClosedAware :=
      TailCapabilityComposition.tailCapabilityClosedAwareBundle_of_wellTyped
        clause baseEffects capability h_wellTyped h_expr h_cap_ne
    catchInteropCapstone :=
      CatchInteroperabilitySuite.catchCapstoneInteropSuite_of_fail_present
        clause innerEffects okTy errTy loweredTy
        h_wellTyped h_failZero h_fail_present h_clauseEffects h_lowered
  }

/-- Build coherent classifier+capstone pair suite from premise-level capstone inputs. -/
theorem effectHandlerCatchPairSuite_of_premises
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
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy := by
  exact effectHandlerCatchPairSuite_of_capstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

/-- Build coherent classifier+capstone pair suite from direct Fail-presence evidence. -/
theorem effectHandlerCatchPairSuite_of_fail_present
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy := by
  exact effectHandlerCatchPairSuite_of_capstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

/-- Build master composition suite from explicit pair witness and outer-absence premise. -/
theorem effectHandlerCompositionSuite_of_pair_outer_absent
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler := by
  refine {
    catchPair := h_pair
    nestedClosedAware :=
      NestedHandlerCompositionContracts.nested_handler_closedAware_bundle_of_outer_absent
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled
        h_outer_abs
  }

/-- Build master composition suite from premise-level capstone inputs and outer-absence. -/
theorem effectHandlerCompositionSuite_of_premises
    (clause : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_cap_ne : capability ≠ clause.handled)
    (h_failZero : FailResultContracts.failAsZeroResume clause)
    (h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (h_clauseEffects : clause.exprEffects = innerEffects)
    (h_lowered :
      loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
          clause.exprEffects
          okTy
          errTy)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler := by
  exact effectHandlerCompositionSuite_of_pair_outer_absent
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCatchPairSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)
    h_outer_abs

/-- Build master composition suite from Fail-presence evidence and outer-absence. -/
theorem effectHandlerCompositionSuite_of_fail_present
    (clause : HandleClauseContract)
    (baseEffects : EffectRow)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
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
          errTy)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler := by
  exact effectHandlerCompositionSuite_of_pair_outer_absent
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCatchPairSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)
    h_outer_abs

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

/-- One-hop projection: catch bridge laws from aggregate classifier suite. -/
theorem effectHandlerSuite_catchLaws
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  CatchInteroperabilitySuite.catchClassifierInteropSuite_laws
    clause innerEffects okTy errTy loweredTy h_suite.catchInterop

/-- One-hop projection: closed-aware handled-removal guarantee from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_closedAwareHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  h_suite.closedAware.closedAwareHandledRemoved

/-- One-hop projection: closed-aware capability preservation from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_closedAwareCapability
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  h_suite.capabilityClosedAware.closedAwareResultCapability

/-- One-hop projection: closed-aware row-tail stability from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_closedAwareRowTailStable
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  h_suite.closedAware.closedAwareRowTailStable

/-- One-hop projection: legacy handled-removal guarantee from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_legacyHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  h_suite.closedAware.legacyHandledRemoved

/-- One-hop projection: non-invalid tail classification from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_tailNotInvalid
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  h_suite.capabilityClosedAware.notInvalid

/-- One-hop projection: generic catch capstone branch from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_genericCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy :=
  CatchInteroperabilitySuite.catchCapstoneInteropSuite_generic
    clause innerEffects okTy errTy loweredTy h_suite.catchInteropCapstone

/-- One-hop projection: higher-order catch capstone branch from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_higherCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  CatchInteroperabilitySuite.catchCapstoneInteropSuite_higher
    clause innerEffects okTy errTy loweredTy h_suite.catchInteropCapstone

/-- One-hop projection: catch bridge laws from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_catchLaws
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  CatchInteroperabilitySuite.catchCapstoneInteropSuite_laws
    clause innerEffects okTy errTy loweredTy h_suite.catchInteropCapstone

/-- One-hop projection: classifier aggregate witness from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_classifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  h_pair.classifier

/-- One-hop projection: capstone aggregate witness from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  h_pair.capstone

/-- One-hop projection: coherence equation from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_classifierFromCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    h_pair.classifier =
      effectHandlerSuite_of_capstoneSuite
        clause capability innerEffects okTy errTy loweredTy h_pair.capstone :=
  h_pair.classifierFromCapstone

/-- One-hop projection: generic classifier branch from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_genericCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  effectHandlerSuite_genericCatchClassifier
    clause capability innerEffects okTy errTy loweredTy h_pair.classifier

/-- One-hop projection: higher-order classifier branch from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_higherCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  effectHandlerSuite_higherCatchClassifier
    clause capability innerEffects okTy errTy loweredTy h_pair.classifier

/-- One-hop projection: generic capstone branch from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_genericCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy :=
  effectHandlerCapstoneSuite_genericCatchCapstone
    clause capability innerEffects okTy errTy loweredTy h_pair.capstone

/-- One-hop projection: higher-order capstone branch from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_higherCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_higherCatchCapstone
    clause capability innerEffects okTy errTy loweredTy h_pair.capstone

/-- One-hop projection: catch bridge laws from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_catchLaws
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy h_pair.capstone

/-- One-hop projection: coherent catch pair from master composition suite. -/
theorem effectHandlerCompositionSuite_catchPair
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy :=
  h_suite.catchPair

/-- One-hop projection: nested closed-aware witness from master composition suite. -/
theorem effectHandlerCompositionSuite_nestedClosedAware
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  h_suite.nestedClosedAware

/-- One-hop projection: nested handled-removal guarantee from master composition suite. -/
theorem effectHandlerCompositionSuite_nestedHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false :=
  h_suite.nestedClosedAware.handledRemoved

/-- One-hop projection: nested row-tail stability from master composition suite. -/
theorem effectHandlerCompositionSuite_nestedRowTailStable
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectRow.rest
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) =
      EffectRow.rest clause.exprEffects :=
  h_suite.nestedClosedAware.rowTailStable

/-- One-hop projection: generic classifier branch from master composition suite. -/
theorem effectHandlerCompositionSuite_genericCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  effectHandlerCatchPairSuite_genericCatchClassifier
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/-- One-hop projection: higher-order classifier branch from master composition suite. -/
theorem effectHandlerCompositionSuite_higherCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  effectHandlerCatchPairSuite_higherCatchClassifier
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/-- One-hop projection: generic capstone branch from master composition suite. -/
theorem effectHandlerCompositionSuite_genericCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy :=
  effectHandlerCatchPairSuite_genericCatchCapstone
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/-- One-hop projection: higher-order capstone branch from master composition suite. -/
theorem effectHandlerCompositionSuite_higherCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_higherCatchCapstone
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/-- One-hop projection: catch bridge laws from master composition suite. -/
theorem effectHandlerCompositionSuite_catchLaws
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/-- One-hop projection: clause closed-aware handled-removal from master composition suite. -/
theorem effectHandlerCompositionSuite_closedAwareHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  effectHandlerCapstoneSuite_closedAwareHandledRemoved
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair.capstone

/-- One-hop projection: clause closed-aware capability preservation from master composition suite. -/
theorem effectHandlerCompositionSuite_closedAwareCapability
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  effectHandlerCapstoneSuite_closedAwareCapability
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair.capstone

/-- One-hop projection: clause closed-aware row-tail stability from master composition suite. -/
theorem effectHandlerCompositionSuite_closedAwareRowTailStable
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  effectHandlerCapstoneSuite_closedAwareRowTailStable
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair.capstone

/-- One-hop projection: clause legacy handled-removal from master composition suite. -/
theorem effectHandlerCompositionSuite_legacyHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  effectHandlerCapstoneSuite_legacyHandledRemoved
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair.capstone

/-- One-hop projection: clause non-invalid tail classification from master composition suite. -/
theorem effectHandlerCompositionSuite_tailNotInvalid
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerCapstoneSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair.capstone

/-- One-hop projection: catch-pair coherence equation from master composition suite. -/
theorem effectHandlerCompositionSuite_classifierFromCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    h_suite.catchPair.classifier =
      effectHandlerSuite_of_capstoneSuite
        clause capability innerEffects okTy errTy loweredTy h_suite.catchPair.capstone :=
  h_suite.catchPair.classifierFromCapstone

end EffectHandlerContractSuite
end Kea
