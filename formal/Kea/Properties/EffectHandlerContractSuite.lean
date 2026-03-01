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

/-- Explicit component alias for `EffectHandlerSuite`. -/
abbrev EffectHandlerSuiteComponents
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop :=
  HandlerClosedAwareContracts.ClosedAwareResultBundle clause
    ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
    ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
        clause innerEffects okTy errTy loweredTy

/-- Explicit component alias for `EffectHandlerCapstoneSuite`. -/
abbrev EffectHandlerCapstoneSuiteComponents
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop :=
  HandlerClosedAwareContracts.ClosedAwareResultBundle clause
    ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
    ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
        clause innerEffects okTy errTy loweredTy

/-- Aggregate suite is equivalent to explicit component bundles. -/
theorem effectHandlerSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy
      ↔ EffectHandlerSuiteComponents clause capability innerEffects okTy errTy loweredTy := by
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
      EffectHandlerSuiteComponents clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerSuite_iff_components clause capability innerEffects okTy errTy loweredTy).2 h_comp

theorem effectHandlerSuite_as_components_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      EffectHandlerSuiteComponents clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerSuite_iff_components clause capability innerEffects okTy errTy loweredTy).1
    (effectHandlerSuite_of_components clause capability innerEffects okTy errTy loweredTy h_comp)

/-- One-hop decomposition of aggregate suite into explicit component bundles. -/
theorem effectHandlerSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerSuite_iff_components clause capability innerEffects okTy errTy loweredTy).1 h_suite

/-- Capstone aggregate suite is equivalent to explicit component bundles. -/
theorem effectHandlerCapstoneSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
      ↔ EffectHandlerCapstoneSuiteComponents clause capability innerEffects okTy errTy loweredTy := by
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
      EffectHandlerCapstoneSuiteComponents clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerCapstoneSuite_iff_components clause capability innerEffects okTy errTy loweredTy).2 h_comp

theorem effectHandlerCapstoneSuite_as_components_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      EffectHandlerCapstoneSuiteComponents clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCapstoneSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerCapstoneSuite_iff_components clause capability innerEffects okTy errTy loweredTy).1
    (effectHandlerCapstoneSuite_of_components
      clause capability innerEffects okTy errTy loweredTy h_comp)

/-- One-hop decomposition of capstone aggregate suite into explicit component bundles. -/
theorem effectHandlerCapstoneSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCapstoneSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
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

theorem effectHandlerSuite_as_components_of_capstoneSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_capstoneSuite
      clause capability innerEffects okTy errTy loweredTy h_cap)

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

/-- Explicit component alias for `EffectHandlerCatchPairSuite`. -/
abbrev EffectHandlerCatchPairSuiteComponents
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) : Prop :=
  ∃ (h_cap :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
    (h_cls :
      EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
    h_cls =
      effectHandlerSuite_of_capstoneSuite
        clause capability innerEffects okTy errTy loweredTy h_cap

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

theorem effectHandlerCatchPairSuite_as_components_of_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_cap :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCatchPairSuiteComponents clause capability innerEffects okTy errTy loweredTy := by
  refine ⟨h_cap, ?_, rfl⟩
  exact effectHandlerSuite_of_capstoneSuite
    clause capability innerEffects okTy errTy loweredTy h_cap

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

/-- Structural decomposition for coherent catch-pair suite. -/
theorem effectHandlerCatchPairSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ↔ EffectHandlerCatchPairSuiteComponents clause capability innerEffects okTy errTy loweredTy := by
  constructor
  · intro h_pair
    exact ⟨h_pair.capstone, h_pair.classifier, h_pair.classifierFromCapstone⟩
  · intro h_comp
    rcases h_comp with ⟨h_cap, h_cls, h_eq⟩
    exact {
      capstone := h_cap
      classifier := h_cls
      classifierFromCapstone := h_eq
    }

/-- Constructor helper for coherent catch-pair decomposition. -/
theorem effectHandlerCatchPairSuite_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      EffectHandlerCatchPairSuiteComponents clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerCatchPairSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy).2 h_comp

theorem effectHandlerCatchPairSuite_as_components_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_comp :
      EffectHandlerCatchPairSuiteComponents clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCatchPairSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerCatchPairSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy).1
    (effectHandlerCatchPairSuite_of_components
      clause capability innerEffects okTy errTy loweredTy h_comp)

/-- One-hop decomposition of coherent catch-pair suite into explicit components. -/
theorem effectHandlerCatchPairSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCatchPairSuiteComponents clause capability innerEffects okTy errTy loweredTy :=
  (effectHandlerCatchPairSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy).1 h_pair

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

/-- Explicit component alias for `EffectHandlerCompositionSuite`. -/
abbrev EffectHandlerCompositionSuiteComponents
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) : Prop :=
  EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
    ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
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
      ↔ EffectHandlerCompositionSuiteComponents
          clause capability innerEffects okTy errTy loweredTy outerHandler := by
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
      EffectHandlerCompositionSuiteComponents
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).2 h_comp

theorem effectHandlerCompositionSuite_as_components_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuiteComponents
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionSuiteComponents
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1
    (effectHandlerCompositionSuite_of_components
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp)

/-- One-hop decomposition of master composition suite into explicit components. -/
theorem effectHandlerCompositionSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionSuiteComponents
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1 h_suite

/-- Master composition suite is also equivalent to capstone+nested components directly. -/
theorem effectHandlerCompositionSuite_iff_capstone_and_nested
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler
      ↔ (EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
          ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
              clause.exprEffects
              clause.handlerEffects
              outerHandler
              clause.handled) := by
  constructor
  · intro h_suite
    exact ⟨h_suite.catchPair.capstone, h_suite.nestedClosedAware⟩
  · intro h_comp
    exact {
      catchPair :=
        effectHandlerCatchPairSuite_of_capstone
          clause capability innerEffects okTy errTy loweredTy h_comp.1
      nestedClosedAware := h_comp.2
    }

/-- Build master composition suite from direct capstone+nested components. -/
theorem effectHandlerCompositionSuite_of_capstone_and_nested
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
        ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled) :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionSuite_iff_capstone_and_nested
    clause capability innerEffects okTy errTy loweredTy outerHandler).2 h_comp

theorem effectHandlerCompositionSuite_as_components_of_capstone_and_nested
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
        ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_capstone_and_nested
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp)

/-- One-hop decomposition of master suite into direct capstone+nested components. -/
theorem effectHandlerCompositionSuite_as_capstone_and_nested
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  (effectHandlerCompositionSuite_iff_capstone_and_nested
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

/--
Direct packaged resume-linearity consequence from a clause-level well-typed
premise, independent of catch/capability side conditions.
-/
def effectHandlerResumeLinearityBundle_of_wellTyped
    (clause : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  HandleClauseContract.clauseResumeLinearityBundle_of_wellTypedSlice clause h_wellTyped

/-- One-hop decomposition of the packaged resume-linearity consequence. -/
theorem effectHandlerResumeLinearityBundle_as_components_of_wellTyped
    (clause : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  HandleClauseContract.clauseResumeLinearityBundle_as_components
    clause
    (effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped)

/-- Singleton handler packaging for a single clause. -/
def singletonHandleContract
    (clause : HandleClauseContract) :
    HandleClauseContract.HandleContract where
  clauses := [clause]

theorem singletonHandleContract_wellTypedSlice_of_wellTyped
    (clause : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause) :
    HandleClauseContract.handlerWellTypedSlice (singletonHandleContract clause) := by
  intro c h_mem
  have h_eq : c = clause := by
    simpa [singletonHandleContract] using h_mem
  subst h_eq
  exact h_wellTyped

/--
Handler-level packaged resume-linearity consequence from a clause-level
well-typed premise via singleton handler membership.
-/
def effectHandlerHandlerResumeLinearityBundle_of_wellTyped
    (clause : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause) :
    HandleClauseContract.HandlerResumeLinearityBundle (singletonHandleContract clause) :=
  HandleClauseContract.handlerResumeLinearityBundle_of_handlerWellTypedSlice
    (singletonHandleContract clause)
    (singletonHandleContract_wellTypedSlice_of_wellTyped clause h_wellTyped)

/-- One-hop decomposition of singleton handler-level resume-linearity bundle. -/
theorem effectHandlerHandlerResumeLinearityBundle_as_components_of_wellTyped
    (clause : HandleClauseContract)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause) :
    HandleClauseContract.HandlerResumeLinearityBundleComponents
      (singletonHandleContract clause) :=
  HandleClauseContract.handlerResumeLinearityBundle_as_components
    (singletonHandleContract clause)
    (effectHandlerHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped)

/--
Premise-route wrapper: extract the packaged resume-linearity consequence along
the same route used to build `EffectHandlerSuite`.
-/
def effectHandlerSuite_resumeLinearityBundle_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/--
Premise-route decomposition wrapper for the packaged resume-linearity
consequence.
-/
theorem effectHandlerSuite_resumeLinearityBundle_as_components_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/--
Premise-route wrapper: extract singleton handler-level packaged linearity along
the same route used to build `EffectHandlerSuite`.
-/
def effectHandlerSuite_handlerResumeLinearityBundle_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.HandlerResumeLinearityBundle (singletonHandleContract clause) :=
  effectHandlerHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

theorem effectHandlerSuite_handlerResumeLinearityBundle_as_components_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.HandlerResumeLinearityBundleComponents
      (singletonHandleContract clause) :=
  effectHandlerHandlerResumeLinearityBundle_as_components_of_wellTyped
    clause h_wellTyped

/--
Fail-present-route wrapper: extract the packaged resume-linearity consequence
along the same route used to build `EffectHandlerSuite`.
-/
def effectHandlerSuite_resumeLinearityBundle_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/--
Fail-present-route decomposition wrapper for the packaged resume-linearity
consequence.
-/
theorem effectHandlerSuite_resumeLinearityBundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/--
Fail-present route wrapper for singleton handler-level packaged linearity.
-/
def effectHandlerSuite_handlerResumeLinearityBundle_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.HandlerResumeLinearityBundle (singletonHandleContract clause) :=
  effectHandlerHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

theorem effectHandlerSuite_handlerResumeLinearityBundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.HandlerResumeLinearityBundleComponents
      (singletonHandleContract clause) :=
  effectHandlerHandlerResumeLinearityBundle_as_components_of_wellTyped
    clause h_wellTyped

theorem effectHandlerSuite_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

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

/--
Premise-route wrapper: extract the packaged resume-linearity consequence along
the same route used to build `EffectHandlerCapstoneSuite`.
-/
def effectHandlerCapstoneSuite_resumeLinearityBundle_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/--
Premise-route decomposition wrapper for the packaged resume-linearity
consequence on the capstone suite route.
-/
theorem effectHandlerCapstoneSuite_resumeLinearityBundle_as_components_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/--
Fail-present-route wrapper: extract the packaged resume-linearity consequence
along the same route used to build `EffectHandlerCapstoneSuite`.
-/
def effectHandlerCapstoneSuite_resumeLinearityBundle_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/--
Fail-present-route decomposition wrapper for the packaged resume-linearity
consequence on the capstone suite route.
-/
theorem effectHandlerCapstoneSuite_resumeLinearityBundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/-- One-hop aggregate-suite premise-route `resume_at_most_once` wrapper. -/
theorem effectHandlerSuite_resumeAtMostOnce_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

/-- One-hop aggregate-suite fail-present-route `resume_at_most_once` wrapper. -/
theorem effectHandlerSuite_resumeAtMostOnce_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

/-- One-hop capstone-suite premise-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCapstoneSuite_resumeAtMostOnce_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

/-- One-hop capstone-suite fail-present-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCapstoneSuite_resumeAtMostOnce_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

theorem effectHandlerCapstoneSuite_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

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

/--
Premise-route wrapper: extract packaged resume-linearity consequences along the
same route used to build `EffectHandlerCatchPairSuite`.
-/
def effectHandlerCatchPairSuite_resumeLinearityBundle_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/-- Premise-route decomposition wrapper for catch-pair resume-linearity package. -/
theorem effectHandlerCatchPairSuite_resumeLinearityBundle_as_components_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/--
Fail-present-route wrapper: extract packaged resume-linearity consequences
along the same route used to build `EffectHandlerCatchPairSuite`.
-/
def effectHandlerCatchPairSuite_resumeLinearityBundle_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/-- Fail-present-route decomposition wrapper for catch-pair resume-linearity package. -/
theorem effectHandlerCatchPairSuite_resumeLinearityBundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/-- One-hop catch-pair premise-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCatchPairSuite_resumeAtMostOnce_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

/-- One-hop catch-pair fail-present-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCatchPairSuite_resumeAtMostOnce_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

theorem effectHandlerCatchPairSuite_as_components_of_premises
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
    ∃ (h_cap :
        EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
      (h_cls :
        EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
      h_cls =
        effectHandlerSuite_of_capstoneSuite
          clause capability innerEffects okTy errTy loweredTy h_cap :=
  effectHandlerCatchPairSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_as_components_of_fail_present
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
    ∃ (h_cap :
        EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
      (h_cls :
        EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
      h_cls =
        effectHandlerSuite_of_capstoneSuite
          clause capability innerEffects okTy errTy loweredTy h_cap :=
  effectHandlerCatchPairSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_fail_present
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

theorem effectHandlerCompositionSuite_as_components_of_pair_outer_absent
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy)
    (h_outer_abs :
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_pair_outer_absent
      clause capability innerEffects okTy errTy loweredTy outerHandler h_pair h_outer_abs)

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

/--
Premise-route wrapper: extract packaged resume-linearity consequences along the
same route used to build `EffectHandlerCompositionSuite`.
-/
def effectHandlerCompositionSuite_resumeLinearityBundle_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/-- Premise-route decomposition wrapper for composition resume-linearity package. -/
theorem effectHandlerCompositionSuite_resumeLinearityBundle_as_components_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/--
Fail-present-route wrapper: extract packaged resume-linearity consequences
along the same route used to build `EffectHandlerCompositionSuite`.
-/
def effectHandlerCompositionSuite_resumeLinearityBundle_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/-- Fail-present-route decomposition wrapper for composition resume-linearity package. -/
theorem effectHandlerCompositionSuite_resumeLinearityBundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/-- One-hop composition premise-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCompositionSuite_resumeAtMostOnce_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

/-- One-hop composition fail-present-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCompositionSuite_resumeAtMostOnce_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

theorem effectHandlerCompositionSuite_as_components_of_premises
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_as_components_of_fail_present
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

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

/--
One-hop projection: closed-aware result bundle decomposed into explicit
handled-removal/row-tail/legacy facts from aggregate suite.
-/
theorem effectHandlerSuite_closedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects)
    ∧
    (RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects clause))
        clause.handled = false) :=
  HandlerClosedAwareContracts.closedAwareResultBundle_as_components
    clause h_suite.closedAware

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

/-- One-hop projection: clause resume linearity from aggregate suite. -/
theorem effectHandlerSuite_resumeAtMostOnce
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    ResumeUse.atMostOnce clause.resumeUse :=
  TailResumptiveClassification.tail_resumptive_notInvalid_implies_atMostOnce
    clause
    (effectHandlerSuite_tailNotInvalid clause capability innerEffects okTy errTy loweredTy h_suite)

/--
One-hop projection: closed-aware tail-capability bundle decomposed into
capability-presence + not-invalid classification facts from aggregate suite.
-/
theorem effectHandlerSuite_capabilityClosedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        capability = true)
    ∧
    (TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid) :=
  TailCapabilityComposition.tailCapabilityClosedAwareBundle_as_components
    clause capability h_suite.capabilityClosedAware

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

theorem effectHandlerSuite_closedAwareHandledRemoved_of_premises
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  effectHandlerSuite_closedAwareHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_closedAwareHandledRemoved_of_fail_present
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  effectHandlerSuite_closedAwareHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_closedAwareCapability_of_premises
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  effectHandlerSuite_closedAwareCapability
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_closedAwareCapability_of_fail_present
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  effectHandlerSuite_closedAwareCapability
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_closedAwareRowTailStable_of_premises
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
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  effectHandlerSuite_closedAwareRowTailStable
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_closedAwareRowTailStable_of_fail_present
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
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  effectHandlerSuite_closedAwareRowTailStable
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_legacyHandledRemoved_of_premises
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
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  effectHandlerSuite_legacyHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_legacyHandledRemoved_of_fail_present
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
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  effectHandlerSuite_legacyHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_tailNotInvalid_of_premises
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
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_tailNotInvalid_of_fail_present
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
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_genericCatchClassifier_of_premises
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  effectHandlerSuite_genericCatchClassifier
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_genericCatchClassifier_of_fail_present
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  effectHandlerSuite_genericCatchClassifier
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_higherCatchClassifier_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  effectHandlerSuite_higherCatchClassifier
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_higherCatchClassifier_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  effectHandlerSuite_higherCatchClassifier
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerSuite_catchLaws_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_clauseEffects h_lowered)

theorem effectHandlerSuite_catchLaws_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

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

/--
One-hop projection: closed-aware result bundle decomposed into explicit
handled-removal/row-tail/legacy facts from capstone aggregate suite.
-/
theorem effectHandlerCapstoneSuite_closedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects)
    ∧
    (RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects clause))
        clause.handled = false) :=
  HandlerClosedAwareContracts.closedAwareResultBundle_as_components
    clause h_suite.closedAware

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

/-- One-hop projection: clause resume linearity from capstone aggregate suite. -/
theorem effectHandlerCapstoneSuite_resumeAtMostOnce
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    ResumeUse.atMostOnce clause.resumeUse :=
  TailResumptiveClassification.tail_resumptive_notInvalid_implies_atMostOnce
    clause
    (effectHandlerCapstoneSuite_tailNotInvalid
      clause capability innerEffects okTy errTy loweredTy h_suite)

/--
One-hop projection: closed-aware tail-capability bundle decomposed into
capability-presence + not-invalid classification facts from capstone suite.
-/
theorem effectHandlerCapstoneSuite_capabilityClosedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_suite : EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        capability = true)
    ∧
    (TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid) :=
  TailCapabilityComposition.tailCapabilityClosedAwareBundle_as_components
    clause capability h_suite.capabilityClosedAware

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

theorem effectHandlerCapstoneSuite_closedAwareHandledRemoved_of_premises
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  effectHandlerCapstoneSuite_closedAwareHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_closedAwareHandledRemoved_of_fail_present
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  effectHandlerCapstoneSuite_closedAwareHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_closedAwareCapability_of_premises
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  effectHandlerCapstoneSuite_closedAwareCapability
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_closedAwareCapability_of_fail_present
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
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  effectHandlerCapstoneSuite_closedAwareCapability
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_closedAwareRowTailStable_of_premises
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
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  effectHandlerCapstoneSuite_closedAwareRowTailStable
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_closedAwareRowTailStable_of_fail_present
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
    EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects :=
  effectHandlerCapstoneSuite_closedAwareRowTailStable
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_legacyHandledRemoved_of_premises
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
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  effectHandlerCapstoneSuite_legacyHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_legacyHandledRemoved_of_fail_present
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
    RowFields.has
      (EffectRow.fields (HandleClauseContract.resultEffects clause))
      clause.handled = false :=
  effectHandlerCapstoneSuite_legacyHandledRemoved
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_tailNotInvalid_of_premises
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
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerCapstoneSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_tailNotInvalid_of_fail_present
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
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerCapstoneSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_genericCatchCapstone_of_premises
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy :=
  effectHandlerCapstoneSuite_genericCatchCapstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_genericCatchCapstone_of_fail_present
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
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy :=
  effectHandlerCapstoneSuite_genericCatchCapstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_higherCatchCapstone_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_higherCatchCapstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_higherCatchCapstone_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_higherCatchCapstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_catchLaws_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCapstoneSuite_catchLaws_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCapstoneSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

/-- One-hop projection: classifier aggregate witness from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_classifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  h_pair.classifier

/--
One-hop projection: classifier aggregate witness decomposed into explicit
closed-aware/capability/catch-classifier components from coherent pair suite.
-/
theorem effectHandlerCatchPairSuite_classifier_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy h_pair.classifier

/-- One-hop projection: capstone aggregate witness from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  h_pair.capstone

/--
One-hop projection: capstone aggregate witness decomposed into explicit
closed-aware/capability/catch-capstone components from coherent pair suite.
-/
theorem effectHandlerCatchPairSuite_capstone_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy h_pair.capstone

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

/-- One-hop projection: non-invalid tail classification from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_tailNotInvalid
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerCapstoneSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy h_pair.capstone

/-- One-hop projection: clause resume linearity from coherent pair suite. -/
theorem effectHandlerCatchPairSuite_resumeAtMostOnce
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (h_pair : EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy) :
    ResumeUse.atMostOnce clause.resumeUse :=
  TailResumptiveClassification.tail_resumptive_notInvalid_implies_atMostOnce
    clause
    (effectHandlerCatchPairSuite_tailNotInvalid
      clause capability innerEffects okTy errTy loweredTy h_pair)

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

theorem effectHandlerCatchPairSuite_classifier_of_premises
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
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_classifier
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_classifier_of_fail_present
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
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_classifier
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_classifier_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_classifier_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_classifier_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_classifier_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_capstone_of_premises
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_capstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_capstone_of_fail_present
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_capstone
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_capstone_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_capstone_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_capstone_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_capstone_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_catchLaws_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered)

theorem effectHandlerCatchPairSuite_catchLaws_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCatchPairSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered)

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

/-- One-hop projection: classifier aggregate witness from master composition suite. -/
theorem effectHandlerCompositionSuite_classifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_classifier
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/--
One-hop projection: classifier aggregate witness decomposed into explicit
closed-aware/capability/catch-classifier components from master composition
suite.
-/
theorem effectHandlerCompositionSuite_classifier_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionSuite_classifier
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/-- One-hop projection: capstone aggregate witness from master composition suite. -/
theorem effectHandlerCompositionSuite_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_capstone
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

/--
One-hop projection: capstone aggregate witness decomposed into explicit
closed-aware/capability/catch-capstone components from master composition
suite.
-/
theorem effectHandlerCompositionSuite_capstone_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionSuite_capstone
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/--
One-hop projection: coherent catch-pair decomposed into explicit capstone,
classifier, and coherence equation from master composition suite.
-/
theorem effectHandlerCompositionSuite_catchPair_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    ∃ (h_cap :
        EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
      (h_cls :
        EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
      h_cls =
        effectHandlerSuite_of_capstoneSuite
          clause capability innerEffects okTy errTy loweredTy h_cap :=
  effectHandlerCatchPairSuite_as_components
    clause capability innerEffects okTy errTy loweredTy h_suite.catchPair

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

/--
One-hop projection: nested closed-aware witness decomposed into explicit
handled-removal and row-tail-stability facts from master composition suite.
-/
theorem effectHandlerCompositionSuite_nestedClosedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)
    ∧
    (EffectRow.rest
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) =
      EffectRow.rest clause.exprEffects) :=
  NestedHandlerCompositionContracts.nestedHandlerClosedAwareBundle_as_components
    clause.exprEffects
    clause.handlerEffects
    outerHandler
    clause.handled
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

theorem effectHandlerCompositionSuite_classifier_of_premises
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
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_classifier
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_classifier_of_fail_present
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
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_classifier
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_classifier_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionSuite_classifier_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_classifier_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionSuite_classifier_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_capstone_of_premises
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_capstone
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_capstone_of_fail_present
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_capstone
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_capstone_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionSuite_capstone_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_capstone_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionSuite_capstone_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_catchLaws_of_premises
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionSuite_catchLaws_of_fail_present
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
    HigherOrderCatchContracts.HigherOrderCatchBridgeLaws clause innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_catchLaws
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

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

/--
One-hop projection: closed-aware result bundle decomposed into explicit
handled-removal/row-tail/legacy facts from master composition suite.
-/
theorem effectHandlerCompositionSuite_closedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects)
    ∧
    (RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects clause))
        clause.handled = false) :=
  effectHandlerCapstoneSuite_closedAware_as_components
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

/-- One-hop projection: clause resume linearity from master composition suite. -/
theorem effectHandlerCompositionSuite_resumeAtMostOnce
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    ResumeUse.atMostOnce clause.resumeUse :=
  TailResumptiveClassification.tail_resumptive_notInvalid_implies_atMostOnce
    clause
    (effectHandlerCompositionSuite_tailNotInvalid
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/--
One-hop projection: closed-aware tail-capability bundle decomposed into
capability-presence + not-invalid classification facts from master composition
suite.
-/
theorem effectHandlerCompositionSuite_capabilityClosedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        capability = true)
    ∧
    (TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid) :=
  effectHandlerCapstoneSuite_capabilityClosedAware_as_components
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

/-- Coherence: nested and closed-aware clause rows share the same row tail. -/
theorem effectHandlerCompositionSuite_nestedRowTail_eq_closedAwareRowTail
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
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) := by
  calc
    EffectRow.rest
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
      = EffectRow.rest clause.exprEffects :=
        effectHandlerCompositionSuite_nestedRowTailStable
          clause capability innerEffects okTy errTy loweredTy outerHandler h_suite
    _ = EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) := by
        symm
        exact effectHandlerCompositionSuite_closedAwareRowTailStable
          clause capability innerEffects okTy errTy loweredTy outerHandler h_suite

/--
Bridge wrapper: nested closed-aware composition agrees with normalized nested
composition under explicit present/open branch assumptions for both stages.
-/
theorem effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_present_or_open
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (_h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_inner_case :
      RowFields.has (EffectRow.fields clause.exprEffects) clause.handled = true ∨
        EffectRow.rest clause.exprEffects ≠ none)
    (h_outer_case :
      RowFields.has
          (EffectRow.fields
            (HandlerAbsentEffectNoop.handleComposeClosedAware
              clause.exprEffects
              clause.handlerEffects
              clause.handled))
          clause.handled = true ∨
        EffectRow.rest
          (HandlerAbsentEffectNoop.handleComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            clause.handled) ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  NestedHandlerCompositionContracts.nestedComposeClosedAware_eq_nestedCompose_of_present_or_open
    clause.exprEffects
    clause.handlerEffects
    outerHandler
    clause.handled
    h_inner_case
    h_outer_case

/-- Coherence: nested same-target composition keeps handled label absent. -/
theorem effectHandlerCompositionSuite_nestedHandledRemoved_coherent
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
  effectHandlerCompositionSuite_nestedHandledRemoved
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite

/-- Coherence: clause closed-aware output also keeps handled label absent. -/
theorem effectHandlerCompositionSuite_clauseHandledRemoved_coherent
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
  effectHandlerCompositionSuite_closedAwareHandledRemoved
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite

/--
Named coherence bundle for the master composition layer that packages:
- nested same-target handled-absence
- clause-level closed-aware handled-absence
- shared row-tail equality between nested and clause closed-aware outputs
-/
structure EffectHandlerNestedClauseCoherenceBundle
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) : Prop where
  nestedHandledRemoved :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false
  clauseHandledRemoved :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false
  nestedRowTailEqClosedAwareRowTail :
    EffectRow.rest
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause)

/-- Structural decomposition for the nested/clause coherence bundle. -/
theorem effectHandlerNestedClauseCoherenceBundle_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) :
    EffectHandlerNestedClauseCoherenceBundle
      clause capability innerEffects okTy errTy loweredTy outerHandler
      ↔
      (RowFields.has
          (EffectRow.fields
            (NestedHandlerCompositionContracts.nestedComposeClosedAware
              clause.exprEffects
              clause.handlerEffects
              outerHandler
              clause.handled))
          clause.handled = false)
      ∧
      (RowFields.has
          (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
          clause.handled = false)
      ∧
      (EffectRow.rest
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled) =
        EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause)) := by
  constructor
  · intro h_bundle
    exact ⟨
      h_bundle.nestedHandledRemoved,
      h_bundle.clauseHandledRemoved,
      h_bundle.nestedRowTailEqClosedAwareRowTail
    ⟩
  · intro h_comp
    exact {
      nestedHandledRemoved := h_comp.1
      clauseHandledRemoved := h_comp.2.1
      nestedRowTailEqClosedAwareRowTail := h_comp.2.2
    }

/-- Constructor helper for nested/clause coherence decomposition. -/
theorem effectHandlerNestedClauseCoherenceBundle_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      (RowFields.has
          (EffectRow.fields
            (NestedHandlerCompositionContracts.nestedComposeClosedAware
              clause.exprEffects
              clause.handlerEffects
              outerHandler
              clause.handled))
          clause.handled = false)
      ∧
      (RowFields.has
          (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
          clause.handled = false)
      ∧
      (EffectRow.rest
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled) =
        EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause))) :
    EffectHandlerNestedClauseCoherenceBundle
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerNestedClauseCoherenceBundle_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).2 h_comp

theorem effectHandlerNestedClauseCoherenceBundle_as_components_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      (RowFields.has
          (EffectRow.fields
            (NestedHandlerCompositionContracts.nestedComposeClosedAware
              clause.exprEffects
              clause.handlerEffects
              outerHandler
              clause.handled))
          clause.handled = false)
      ∧
      (RowFields.has
          (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
          clause.handled = false)
      ∧
      (EffectRow.rest
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled) =
        EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause))) :
    (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)
    ∧
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause)) :=
  (effectHandlerNestedClauseCoherenceBundle_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1
    (effectHandlerNestedClauseCoherenceBundle_of_components
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp)

/-- Projection helper for nested/clause coherence decomposition. -/
theorem effectHandlerNestedClauseCoherenceBundle_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_bundle :
      EffectHandlerNestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)
    ∧
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause)) :=
  (effectHandlerNestedClauseCoherenceBundle_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1 h_bundle

/-- Build the named nested/clause coherence bundle from the master composition suite. -/
theorem effectHandlerNestedClauseCoherenceBundle_of_compositionSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerNestedClauseCoherenceBundle
      clause capability innerEffects okTy errTy loweredTy outerHandler := by
  refine {
    nestedHandledRemoved :=
      effectHandlerCompositionSuite_nestedHandledRemoved_coherent
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite
    clauseHandledRemoved :=
      effectHandlerCompositionSuite_clauseHandledRemoved_coherent
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite
    nestedRowTailEqClosedAwareRowTail :=
      effectHandlerCompositionSuite_nestedRowTail_eq_closedAwareRowTail
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite
  }

theorem effectHandlerNestedClauseCoherenceBundle_as_components_of_compositionSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)
    ∧
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause)) :=
  effectHandlerNestedClauseCoherenceBundle_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerNestedClauseCoherenceBundle_of_compositionSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/-- One-hop projection: nested/clause coherence bundle from the master composition suite. -/
theorem effectHandlerCompositionSuite_nestedClauseCoherenceBundle
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerNestedClauseCoherenceBundle
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  effectHandlerNestedClauseCoherenceBundle_of_compositionSuite
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite

/-- One-hop projection: nested handled-absence from the named coherence bundle. -/
theorem effectHandlerNestedClauseCoherenceBundle_nestedHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_bundle :
      EffectHandlerNestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false :=
  h_bundle.nestedHandledRemoved

/-- One-hop projection: clause closed-aware handled-absence from the named coherence bundle. -/
theorem effectHandlerNestedClauseCoherenceBundle_clauseHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_bundle :
      EffectHandlerNestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  h_bundle.clauseHandledRemoved

/-- One-hop projection: nested/clause row-tail equality from the named coherence bundle. -/
theorem effectHandlerNestedClauseCoherenceBundle_nestedRowTailEqClosedAwareRowTail
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_bundle :
      EffectHandlerNestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectRow.rest
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) :=
  h_bundle.nestedRowTailEqClosedAwareRowTail

/--
Master package that pairs the full composition suite with its derived
nested/clause coherence bundle and records the derivation equation explicitly.
-/
structure EffectHandlerCompositionCoherenceSuite
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) : Prop where
  composition :
    EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler
  nestedClauseCoherence :
    EffectHandlerNestedClauseCoherenceBundle
      clause capability innerEffects okTy errTy loweredTy outerHandler
  coherenceFromComposition :
    nestedClauseCoherence =
      effectHandlerCompositionSuite_nestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler composition

/-- Explicit component alias for `EffectHandlerCompositionCoherenceSuite`. -/
abbrev EffectHandlerCompositionCoherenceSuiteComponents
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) : Prop :=
  ∃ (h_comp :
      EffectHandlerCompositionSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_coh :
      EffectHandlerNestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler),
    h_coh =
      effectHandlerCompositionSuite_nestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler h_comp

/-- Build the master composition+coherence package from any composition witness. -/
theorem effectHandlerCompositionCoherenceSuite_of_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionCoherenceSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler := by
  refine {
    composition := h_comp
    nestedClauseCoherence :=
      effectHandlerCompositionSuite_nestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler h_comp
    coherenceFromComposition := rfl
  }

theorem effectHandlerCompositionCoherenceSuite_as_components_of_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionCoherenceSuiteComponents
      clause capability innerEffects okTy errTy loweredTy outerHandler := by
  refine ⟨h_comp, ?_, rfl⟩
  exact effectHandlerCompositionSuite_nestedClauseCoherenceBundle
    clause capability innerEffects okTy errTy loweredTy outerHandler h_comp

/--
Composition+coherence package is equivalent to just the composition witness,
since the coherence bundle is canonically derived.
-/
theorem effectHandlerCompositionCoherenceSuite_iff_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) :
    EffectHandlerCompositionCoherenceSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler
      ↔ EffectHandlerCompositionSuite
          clause capability innerEffects okTy errTy loweredTy outerHandler := by
  constructor
  · intro h_suite
    exact h_suite.composition
  · intro h_comp
    exact effectHandlerCompositionCoherenceSuite_of_composition
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp

/--
Explicit component decomposition for the composition+coherence package:
composition witness, derived coherence witness, and coherence derivation
equation.
-/
theorem effectHandlerCompositionCoherenceSuite_iff_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow) :
    EffectHandlerCompositionCoherenceSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler
      ↔ EffectHandlerCompositionCoherenceSuiteComponents
          clause capability innerEffects okTy errTy loweredTy outerHandler := by
  constructor
  · intro h_suite
    exact ⟨h_suite.composition, h_suite.nestedClauseCoherence, h_suite.coherenceFromComposition⟩
  · intro h_parts
    rcases h_parts with ⟨h_comp, h_coh, h_eq⟩
    exact {
      composition := h_comp
      nestedClauseCoherence := h_coh
      coherenceFromComposition := h_eq
    }

/-- Build the package from explicit components and their derivation equation. -/
theorem effectHandlerCompositionCoherenceSuite_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_parts :
      EffectHandlerCompositionCoherenceSuiteComponents
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionCoherenceSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionCoherenceSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).2 h_parts

theorem effectHandlerCompositionCoherenceSuite_as_components_of_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_parts :
      EffectHandlerCompositionCoherenceSuiteComponents
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionCoherenceSuiteComponents
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionCoherenceSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1
    (effectHandlerCompositionCoherenceSuite_of_components
      clause capability innerEffects okTy errTy loweredTy outerHandler h_parts)

/-- One-hop decomposition of the package into explicit components. -/
theorem effectHandlerCompositionCoherenceSuite_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionCoherenceSuiteComponents
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  (effectHandlerCompositionCoherenceSuite_iff_components
    clause capability innerEffects okTy errTy loweredTy outerHandler).1 h_suite

/-- Build the master package from premise-level capstone inputs and outer-absence. -/
theorem effectHandlerCompositionCoherenceSuite_of_premises
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
    EffectHandlerCompositionCoherenceSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler := by
  exact effectHandlerCompositionCoherenceSuite_of_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

/-- Build the master package from Fail-presence evidence and outer-absence. -/
theorem effectHandlerCompositionCoherenceSuite_of_fail_present
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
    EffectHandlerCompositionCoherenceSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler := by
  exact effectHandlerCompositionCoherenceSuite_of_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

/--
Premise-route wrapper: extract packaged resume-linearity consequences along the
same route used to build `EffectHandlerCompositionCoherenceSuite`.
-/
def effectHandlerCompositionCoherenceSuite_resumeLinearityBundle_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/-- Premise-route decomposition wrapper for coherence resume-linearity package. -/
theorem effectHandlerCompositionCoherenceSuite_resumeLinearityBundle_as_components_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/--
Fail-present-route wrapper: extract packaged resume-linearity consequences
along the same route used to build `EffectHandlerCompositionCoherenceSuite`.
-/
def effectHandlerCompositionCoherenceSuite_resumeLinearityBundle_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundle clause :=
  effectHandlerResumeLinearityBundle_of_wellTyped clause h_wellTyped

/-- Fail-present-route decomposition wrapper for coherence resume-linearity package. -/
theorem effectHandlerCompositionCoherenceSuite_resumeLinearityBundle_as_components_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    HandleClauseContract.ClauseResumeLinearityBundleComponents clause :=
  effectHandlerResumeLinearityBundle_as_components_of_wellTyped clause h_wellTyped

/-- One-hop coherence premise-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCompositionCoherenceSuite_resumeAtMostOnce_of_premises
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_admissible : FailResultContracts.catchAdmissible clause.exprEffects)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

/-- One-hop coherence fail-present-route `resume_at_most_once` wrapper. -/
theorem effectHandlerCompositionCoherenceSuite_resumeAtMostOnce_of_fail_present
    (clause : HandleClauseContract)
    (_baseEffects : EffectRow)
    (_capability : Label)
    (_innerEffects : EffectRow)
    (_okTy _errTy _loweredTy : Ty)
    (_outerHandler : EffectRow)
    (h_wellTyped : HandleClauseContract.wellTypedSlice clause)
    (_h_expr :
      clause.exprEffects =
        EffectOperationTyping.performOperationEffects _baseEffects _capability)
    (_h_cap_ne : _capability ≠ clause.handled)
    (_h_failZero : FailResultContracts.failAsZeroResume clause)
    (_h_fail_present :
      RowFields.has (EffectRow.fields clause.exprEffects) FailResultContracts.failLabel = true)
    (_h_clauseEffects : clause.exprEffects = _innerEffects)
    (_h_lowered :
      _loweredTy =
        FailResultContracts.lowerFailFunctionType
          (CatchInteroperabilitySuite.higherOrderParams _innerEffects _okTy)
          clause.exprEffects
          _okTy
          _errTy)
    (_h_outer_abs :
      RowFields.has (EffectRow.fields _outerHandler) clause.handled = false) :
    resume_at_most_once clause.resumeUse :=
  HandleClauseContract.clauseResumeLinearityBundle_atMostOnce_of_wellTypedSlice
    clause h_wellTyped

theorem effectHandlerCompositionCoherenceSuite_as_components_of_premises
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
    ∃ (h_comp :
        EffectHandlerCompositionSuite
          clause capability innerEffects okTy errTy loweredTy outerHandler)
      (h_coh :
        EffectHandlerNestedClauseCoherenceBundle
          clause capability innerEffects okTy errTy loweredTy outerHandler),
      h_coh =
        effectHandlerCompositionSuite_nestedClauseCoherenceBundle
          clause capability innerEffects okTy errTy loweredTy outerHandler h_comp :=
  effectHandlerCompositionCoherenceSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_as_components_of_fail_present
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
    ∃ (h_comp :
        EffectHandlerCompositionSuite
          clause capability innerEffects okTy errTy loweredTy outerHandler)
      (h_coh :
        EffectHandlerNestedClauseCoherenceBundle
          clause capability innerEffects okTy errTy loweredTy outerHandler),
      h_coh =
        effectHandlerCompositionSuite_nestedClauseCoherenceBundle
          clause capability innerEffects okTy errTy loweredTy outerHandler h_comp :=
  effectHandlerCompositionCoherenceSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

/-- One-hop projection: composition witness from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCompositionSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  h_suite.composition

/--
One-hop projection: composition witness decomposed into explicit catch-pair and
nested closed-aware components from the master composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_composition_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/--
One-hop projection: composition witness decomposed into explicit capstone and
nested closed-aware components from the master composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_composition_as_capstone_and_nested
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_capstone_and_nested
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/-- One-hop projection: coherent catch pair from the master composition+coherence package. -/
theorem effectHandlerCompositionCoherenceSuite_catchPair
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy :=
  h_suite.composition.catchPair

/--
One-hop projection: coherent catch pair decomposed into explicit capstone,
classifier, and coherence equation from the master package.
-/
theorem effectHandlerCompositionCoherenceSuite_catchPair_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    ∃ (h_cap :
        EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
      (h_cls :
        EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
      h_cls =
        effectHandlerSuite_of_capstoneSuite
          clause capability innerEffects okTy errTy loweredTy h_cap :=
  effectHandlerCatchPairSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    h_suite.composition.catchPair

/-- One-hop projection: classifier aggregate witness from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_classifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_classifier
    clause capability innerEffects okTy errTy loweredTy
    h_suite.composition.catchPair

/--
One-hop projection: classifier aggregate witness decomposed into explicit
closed-aware/capability/catch-classifier components from master
composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_classifier_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_classifier
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/-- One-hop projection: capstone aggregate witness from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_capstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCatchPairSuite_capstone
    clause capability innerEffects okTy errTy loweredTy
    h_suite.composition.catchPair

theorem effectHandlerCompositionCoherenceSuite_composition_of_premises
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
    EffectHandlerCompositionSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  effectHandlerCompositionCoherenceSuite_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_composition_of_fail_present
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
    EffectHandlerCompositionSuite
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  effectHandlerCompositionCoherenceSuite_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_composition_as_components_of_premises
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_composition_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_composition_as_components_of_fail_present
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy
      ∧ NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled :=
  effectHandlerCompositionSuite_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_composition_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_catchPair_of_premises
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionCoherenceSuite_catchPair
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_catchPair_of_fail_present
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
    EffectHandlerCatchPairSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionCoherenceSuite_catchPair
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_catchPair_as_components_of_premises
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
    ∃ (h_cap :
        EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
      (h_cls :
        EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
      h_cls =
        effectHandlerSuite_of_capstoneSuite
          clause capability innerEffects okTy errTy loweredTy h_cap :=
  effectHandlerCatchPairSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_catchPair_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_catchPair_as_components_of_fail_present
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
    ∃ (h_cap :
        EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy)
      (h_cls :
        EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy),
      h_cls =
        effectHandlerSuite_of_capstoneSuite
          clause capability innerEffects okTy errTy loweredTy h_cap :=
  effectHandlerCatchPairSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_catchPair_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_classifier_of_premises
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
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionCoherenceSuite_classifier
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_classifier_of_fail_present
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
    EffectHandlerSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionCoherenceSuite_classifier
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_classifier_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_classifier_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_classifier_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchClassifierInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_classifier_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_capstone_of_premises
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionCoherenceSuite_capstone
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_capstone_of_fail_present
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
    EffectHandlerCapstoneSuite clause capability innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionCoherenceSuite_capstone
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_capstone_as_components_of_premises
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_capstone_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)

theorem effectHandlerCompositionCoherenceSuite_capstone_as_components_of_fail_present
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
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_capstone_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)

/--
One-hop projection: capstone aggregate witness decomposed into explicit
closed-aware/capability/catch-capstone components from master
composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_capstone_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HandlerClosedAwareContracts.ClosedAwareResultBundle clause
      ∧ TailCapabilityComposition.TailCapabilityClosedAwareBundle clause capability
      ∧ CatchInteroperabilitySuite.CatchCapstoneInteropSuite
          clause innerEffects okTy errTy loweredTy :=
  effectHandlerCapstoneSuite_as_components
    clause capability innerEffects okTy errTy loweredTy
    (effectHandlerCompositionCoherenceSuite_capstone
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/--
One-hop projection: classifier-from-capstone coherence equation from the master
composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_classifierFromCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    h_suite.composition.catchPair.classifier =
      effectHandlerSuite_of_capstoneSuite
        clause capability innerEffects okTy errTy loweredTy
        h_suite.composition.catchPair.capstone :=
  effectHandlerCatchPairSuite_classifierFromCapstone
    clause capability innerEffects okTy errTy loweredTy
    h_suite.composition.catchPair

/--
One-hop projection: nested closed-aware witness from the master
composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    NestedHandlerCompositionContracts.NestedHandlerClosedAwareBundle
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerCompositionSuite_nestedClosedAware
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/--
One-hop projection: nested closed-aware witness decomposed into explicit
handled-removal and row-tail-stability facts from master
composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)
    ∧
    (EffectRow.rest
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) =
      EffectRow.rest clause.exprEffects) :=
  effectHandlerCompositionSuite_nestedClosedAware_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/--
One-hop projection: nested row-tail stability with respect to expression
effects from the master composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedRowTailStable
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectRow.rest
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) =
      EffectRow.rest clause.exprEffects :=
  effectHandlerCompositionSuite_nestedRowTailStable
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/-- One-hop projection: nested/clause coherence bundle from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_nestedClauseCoherence
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectHandlerNestedClauseCoherenceBundle
      clause capability innerEffects okTy errTy loweredTy outerHandler :=
  h_suite.nestedClauseCoherence

/--
One-hop projection: nested/clause coherence bundle decomposed into explicit
component facts from the master package.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClauseCoherence_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)
    ∧
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause)) :=
  effectHandlerNestedClauseCoherenceBundle_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.nestedClauseCoherence

/--
One-hop projection: closed-aware result bundle decomposed into explicit
handled-removal/row-tail/legacy facts from master composition+coherence
package.
-/
theorem effectHandlerCompositionCoherenceSuite_closedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        clause.handled = false)
    ∧
    (EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) =
      EffectRow.rest clause.exprEffects)
    ∧
    (RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects clause))
        clause.handled = false) :=
  effectHandlerCompositionSuite_closedAware_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/-- One-hop projection: coherence derivation equation from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_coherenceFromComposition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    h_suite.nestedClauseCoherence =
      effectHandlerCompositionSuite_nestedClauseCoherenceBundle
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition :=
  h_suite.coherenceFromComposition

/-- One-hop projection: nested/clause row-tail equality from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_nestedRowTailEqClosedAwareRowTail
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    EffectRow.rest
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) =
      EffectRow.rest (HandlerClosedAwareContracts.resultEffectsClosedAware clause) :=
  h_suite.nestedClauseCoherence.nestedRowTailEqClosedAwareRowTail

/-- One-hop projection: nested handled-absence from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_nestedHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false :=
  h_suite.nestedClauseCoherence.nestedHandledRemoved

/-- One-hop projection: clause closed-aware handled-absence from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_clauseHandledRemoved
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      clause.handled = false :=
  h_suite.nestedClauseCoherence.clauseHandledRemoved

/-- One-hop projection: generic catch classifier branch from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_genericCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy
      ∨ FailResultContracts.catchUnnecessary clause.exprEffects :=
  effectHandlerCompositionSuite_genericCatchClassifier
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition

/-- One-hop projection: higher-order catch classifier branch from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_higherCatchClassifier
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy
      ∨ FailResultContracts.catchUnnecessary innerEffects :=
  effectHandlerCompositionSuite_higherCatchClassifier
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition

/-- One-hop projection: generic catch capstone branch from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_genericCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    CatchTypingBridge.CatchTypingCapstoneOutcome
      clause
      (CatchInteroperabilitySuite.higherOrderParams innerEffects okTy)
      okTy
      errTy
      loweredTy :=
  effectHandlerCompositionSuite_genericCatchCapstone
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition

/-- One-hop projection: higher-order catch capstone branch from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_higherCatchCapstone
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    HigherOrderCatchContracts.HigherOrderCatchCapstoneOutcome clause innerEffects okTy errTy loweredTy :=
  effectHandlerCompositionSuite_higherCatchCapstone
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition

/-- One-hop projection: closed-aware capability preservation from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_closedAwareCapability
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    RowFields.has
      (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
      capability = true :=
  effectHandlerCompositionSuite_closedAwareCapability
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition

/-- One-hop projection: clause non-invalid tail classification from the master package. -/
theorem effectHandlerCompositionCoherenceSuite_tailNotInvalid
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid :=
  effectHandlerCompositionSuite_tailNotInvalid
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite.composition

/-- One-hop projection: clause resume linearity from composition+coherence suite. -/
theorem effectHandlerCompositionCoherenceSuite_resumeAtMostOnce
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    ResumeUse.atMostOnce clause.resumeUse :=
  TailResumptiveClassification.tail_resumptive_notInvalid_implies_atMostOnce
    clause
    (effectHandlerCompositionCoherenceSuite_tailNotInvalid
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite)

/--
One-hop projection: closed-aware tail-capability bundle decomposed into
capability-presence + not-invalid classification facts from master
composition+coherence package.
-/
theorem effectHandlerCompositionCoherenceSuite_capabilityClosedAware_as_components
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler) :
    (RowFields.has
        (EffectRow.fields (HandlerClosedAwareContracts.resultEffectsClosedAware clause))
        capability = true)
    ∧
    (TailResumptiveClassification.classifyClause clause ≠
      TailResumptiveClassification.TailResumptiveClass.invalid) :=
  effectHandlerCompositionSuite_capabilityClosedAware_as_components
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition

/--
Bridge wrapper on the composition+coherence package: nested closed-aware
composition agrees with normalized nested composition under explicit
present/open branch assumptions for both stages.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_present_or_open
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_inner_case :
      RowFields.has (EffectRow.fields clause.exprEffects) clause.handled = true ∨
        EffectRow.rest clause.exprEffects ≠ none)
    (h_outer_case :
      RowFields.has
          (EffectRow.fields
            (HandlerAbsentEffectNoop.handleComposeClosedAware
              clause.exprEffects
              clause.handlerEffects
              clause.handled))
          clause.handled = true ∨
        EffectRow.rest
          (HandlerAbsentEffectNoop.handleComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            clause.handled) ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_present_or_open
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition
    h_inner_case
    h_outer_case

/--
Open-row corollary on composition suite: if the clause expression effect row is
open, nested closed-aware composition agrees with normalized nested composition.
-/
theorem effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (_h_suite :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  NestedHandlerCompositionContracts.nestedComposeClosedAware_eq_nestedCompose_of_open_row
    clause.exprEffects
    clause.handlerEffects
    outerHandler
    clause.handled
    h_open

/--
Direct premise-level bridge on the composition suite from open base row.
-/
theorem effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_base_row_of_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled := by
  have h_open : EffectRow.rest clause.exprEffects ≠ none := by
    rw [h_expr]
    rw [EffectOperationTyping.performOperation_preserves_row_tail baseEffects capability]
    exact h_base_open
  exact effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)
    h_open

/--
Fail-presence variant of the open-base-row bridge on the composition suite.
-/
theorem effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_base_row_of_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled := by
  have h_open : EffectRow.rest clause.exprEffects ≠ none := by
    rw [h_expr]
    rw [EffectOperationTyping.performOperation_preserves_row_tail baseEffects capability]
    exact h_base_open
  exact effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)
    h_open

/--
Open-row consequence on the composition suite: normalized nested composition
also keeps the handled label absent.
-/
theorem effectHandlerCompositionSuite_nestedComposeHandledRemoved_of_open_expr_row
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false := by
  have h_closed :
      RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedComposeClosedAware
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false :=
    effectHandlerCompositionSuite_nestedHandledRemoved_coherent
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp
  have h_eq :
      NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled :=
    effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open
  simpa [h_eq] using h_closed

/--
Open-row consequence on the composition+coherence suite: normalized nested
composition keeps the handled label absent.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedComposeHandledRemoved_of_open_expr_row
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false :=
  effectHandlerCompositionSuite_nestedComposeHandledRemoved_of_open_expr_row
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition
    h_open

/--
Open-row corollary on composition+coherence suite: if the clause expression
effect row is open, nested closed-aware composition agrees with normalized
nested composition.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    clause capability innerEffects okTy errTy loweredTy outerHandler
    h_suite.composition
    h_open

/--
Direct premise-level open-row bridge: nested closed-aware composition agrees
with normalized nested composition without explicit suite construction.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled := by
  exact effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)
    h_open

/--
Direct fail-presence entrypoint for the open-row nested bridge.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled := by
  exact effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
    clause capability innerEffects okTy errTy loweredTy outerHandler
    (effectHandlerCompositionCoherenceSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)
    h_open

/--
Direct premise-level bridge from open base row:
if `baseEffects` is open and `clause.exprEffects` is produced by one operation
step from `baseEffects`, nested closed-aware composition agrees with normalized
nested composition.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_base_row_of_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled := by
  have h_open : EffectRow.rest clause.exprEffects ≠ none := by
    rw [h_expr]
    rw [EffectOperationTyping.performOperation_preserves_row_tail baseEffects capability]
    exact h_base_open
  exact effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_premises
    clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
    h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_open

/--
Fail-presence variant of the open-base-row bridge entrypoint.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_base_row_of_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled := by
  have h_open : EffectRow.rest clause.exprEffects ≠ none := by
    rw [h_expr]
    rw [EffectOperationTyping.performOperation_preserves_row_tail baseEffects capability]
    exact h_base_open
  exact effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_fail_present
    clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
    h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_open

/--
Named bundle for the open-row nested bridge surface.
-/
structure EffectHandlerNestedOpenRowBridgeBundle
    (clause : HandleClauseContract)
    (outerHandler : EffectRow) : Prop where
  closedAwareEqNormalized :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled

/-- Structural decomposition for the open-row bridge bundle. -/
theorem effectHandlerNestedOpenRowBridgeBundle_iff_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler
      ↔
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled =
        NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled) := by
  constructor
  · intro h_bundle
    exact h_bundle.closedAwareEqNormalized
  · intro h_comp
    exact {
      closedAwareEqNormalized := h_comp
    }

/-- Constructor helper for the open-row bridge bundle decomposition. -/
theorem effectHandlerNestedOpenRowBridgeBundle_of_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_comp :
      NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler :=
  (effectHandlerNestedOpenRowBridgeBundle_iff_components clause outerHandler).2 h_comp

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_comp :
      NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  (effectHandlerNestedOpenRowBridgeBundle_iff_components clause outerHandler).1
    (effectHandlerNestedOpenRowBridgeBundle_of_components clause outerHandler h_comp)

/-- Projection helper for the open-row bridge bundle decomposition. -/
theorem effectHandlerNestedOpenRowBridgeBundle_as_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowBridgeBundle clause outerHandler) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  (effectHandlerNestedOpenRowBridgeBundle_iff_components clause outerHandler).1 h_bundle

/-- Build the open-row bridge bundle from a composition-suite witness. -/
theorem effectHandlerNestedOpenRowBridgeBundle_of_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open
  }

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_composition
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open)

/-- Build the open-row bridge bundle from a composition+coherence witness. -/
theorem effectHandlerNestedOpenRowBridgeBundle_of_coherence
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open
  }

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_coherence
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_coherence
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open)

/--
One-hop projection: open-row bridge bundle from a composition-suite witness.
-/
theorem effectHandlerCompositionSuite_nestedOpenRowBridgeBundle
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler :=
  effectHandlerNestedOpenRowBridgeBundle_of_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open

/--
One-hop projection: open-row bridge bundle from a composition+coherence
suite witness.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedOpenRowBridgeBundle
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler :=
  effectHandlerNestedOpenRowBridgeBundle_of_coherence
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open

/-- Premise-level constructor for the open-row bridge bundle. -/
theorem effectHandlerNestedOpenRowBridgeBundle_of_open_base_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_base_row_of_premises
        clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
        h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_base_open
  }

/-- Fail-presence variant of the premise-level open-row bridge bundle constructor. -/
theorem effectHandlerNestedOpenRowBridgeBundle_of_open_base_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_base_row_of_fail_present
        clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
        h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_base_open
  }

/--
Direct open-expr-row premise constructor for the open-row bridge bundle.
-/
theorem effectHandlerNestedOpenRowBridgeBundle_of_open_expr_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_premises
        clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
        h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_open
  }

/--
Fail-presence variant of the direct open-expr-row premise constructor.
-/
theorem effectHandlerNestedOpenRowBridgeBundle_of_open_expr_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_fail_present
        clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
        h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_open
  }

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_open_base_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_open_base_row_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_base_open)

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_open_base_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_open_base_row_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_base_open)

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_open_expr_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_open_expr_row_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_open)

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_open_expr_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_open_expr_row_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_open)

/-- One-hop projection from the open-row bridge bundle. -/
theorem effectHandlerNestedOpenRowBridgeBundle_closedAwareEqNormalized
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowBridgeBundle clause outerHandler) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  h_bundle.closedAwareEqNormalized

/--
Strengthened open-row consequence bundle:
- closed-aware/normalized equality
- handled-label absence on normalized nested composition
-/
structure EffectHandlerNestedOpenRowConsequenceBundle
    (clause : HandleClauseContract)
    (outerHandler : EffectRow) : Prop where
  closedAwareEqNormalized :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled
  normalizedHandledRemoved :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false

/-- Structural decomposition for strengthened open-row consequence bundle. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_iff_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler
      ↔
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled =
        NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled)
      ∧
      (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedCompose
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false) := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.closedAwareEqNormalized, h_bundle.normalizedHandledRemoved⟩
  · intro h_comp
    exact {
      closedAwareEqNormalized := h_comp.1
      normalizedHandledRemoved := h_comp.2
    }

/-- Build strengthened open-row consequence bundle from explicit components. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_comp :
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled =
        NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled)
      ∧
      (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedCompose
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler :=
  (effectHandlerNestedOpenRowConsequenceBundle_iff_components clause outerHandler).2 h_comp

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_comp :
      (NestedHandlerCompositionContracts.nestedComposeClosedAware
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled =
        NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled)
      ∧
      (RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedCompose
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false)) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  (effectHandlerNestedOpenRowConsequenceBundle_iff_components clause outerHandler).1
    (effectHandlerNestedOpenRowConsequenceBundle_of_components clause outerHandler h_comp)

/-- One-hop decomposition of strengthened open-row consequence bundle. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_as_components
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  (effectHandlerNestedOpenRowConsequenceBundle_iff_components clause outerHandler).1 h_bundle

/-- Build strengthened open-row consequence bundle from a composition witness. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open
    normalizedHandledRemoved :=
      effectHandlerCompositionSuite_nestedComposeHandledRemoved_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open
  }

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_composition
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_composition
      clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open)

/-- Build strengthened open-row consequence bundle from a coherence witness. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_coherence
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open
    normalizedHandledRemoved :=
      effectHandlerCompositionCoherenceSuite_nestedComposeHandledRemoved_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open
  }

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_coherence
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_coherence
      clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open)

/--
One-hop projection: strengthened open-row consequence bundle from a
composition-suite witness.
-/
theorem effectHandlerCompositionSuite_nestedOpenRowConsequenceBundle
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler :=
  effectHandlerNestedOpenRowConsequenceBundle_of_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open

/--
One-hop projection: strengthened open-row consequence bundle from a
composition+coherence suite witness.
-/
theorem effectHandlerCompositionCoherenceSuite_nestedOpenRowConsequenceBundle
    (clause : HandleClauseContract)
    (capability : Label)
    (innerEffects : EffectRow)
    (okTy errTy loweredTy : Ty)
    (outerHandler : EffectRow)
    (h_suite :
      EffectHandlerCompositionCoherenceSuite
        clause capability innerEffects okTy errTy loweredTy outerHandler)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler :=
  effectHandlerNestedOpenRowConsequenceBundle_of_coherence
    clause capability innerEffects okTy errTy loweredTy outerHandler h_suite h_open

/-- Premise-level constructor for strengthened open-row consequence bundle. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_open_base_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  have h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler :=
    effectHandlerCompositionSuite_of_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs
  have h_open : EffectRow.rest clause.exprEffects ≠ none := by
    rw [h_expr]
    rw [EffectOperationTyping.performOperation_preserves_row_tail baseEffects capability]
    exact h_base_open
  exact effectHandlerNestedOpenRowConsequenceBundle_of_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open

/-- Fail-presence variant of premise-level strengthened open-row consequence bundle. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_open_base_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  have h_comp :
      EffectHandlerCompositionSuite clause capability innerEffects okTy errTy loweredTy outerHandler :=
    effectHandlerCompositionSuite_of_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs
  have h_open : EffectRow.rest clause.exprEffects ≠ none := by
    rw [h_expr]
    rw [EffectOperationTyping.performOperation_preserves_row_tail baseEffects capability]
    exact h_base_open
  exact effectHandlerNestedOpenRowConsequenceBundle_of_composition
    clause capability innerEffects okTy errTy loweredTy outerHandler h_comp h_open

/--
Direct open-expr-row premise constructor for strengthened open-row
consequence bundle.
-/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_open_expr_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_premises
        clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
        h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_open
    normalizedHandledRemoved :=
      effectHandlerCompositionSuite_nestedComposeHandledRemoved_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler
        (effectHandlerCompositionSuite_of_premises
          clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
          h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs)
        h_open
  }

/--
Fail-presence variant of direct open-expr-row premise constructor for the
strengthened open-row consequence bundle.
-/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_open_expr_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized :=
      effectHandlerCompositionCoherenceSuite_nestedClosedAware_eq_nestedCompose_of_open_expr_row_of_fail_present
        clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
        h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_open
    normalizedHandledRemoved :=
      effectHandlerCompositionSuite_nestedComposeHandledRemoved_of_open_expr_row
        clause capability innerEffects okTy errTy loweredTy outerHandler
        (effectHandlerCompositionSuite_of_fail_present
          clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
          h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs)
        h_open
  }

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_open_base_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_open_base_row_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_base_open)

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_open_base_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_base_open : EffectRow.rest baseEffects ≠ none) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_open_base_row_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_base_open)

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_open_expr_row_premises
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_open_expr_row_premises
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_admissible h_clauseEffects h_lowered h_outer_abs h_open)

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_open_expr_row_fail_present
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
      RowFields.has (EffectRow.fields outerHandler) clause.handled = false)
    (h_open : EffectRow.rest clause.exprEffects ≠ none) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_open_expr_row_fail_present
      clause baseEffects capability innerEffects okTy errTy loweredTy outerHandler
      h_wellTyped h_expr h_cap_ne h_failZero h_fail_present h_clauseEffects h_lowered h_outer_abs h_open)

/-- One-hop projection: equality facet of strengthened open-row consequence bundle. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_closedAwareEqNormalized
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  h_bundle.closedAwareEqNormalized

/-- One-hop projection: normalized handled-removal facet of strengthened bundle. -/
theorem effectHandlerNestedOpenRowConsequenceBundle_normalizedHandledRemoved
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler) :
    RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false :=
  h_bundle.normalizedHandledRemoved

/--
Build strengthened consequence bundle from a bridge bundle plus normalized
handled-removal fact.
-/
theorem effectHandlerNestedOpenRowConsequenceBundle_of_bridge_and_normalizedHandledRemoved
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bridge : EffectHandlerNestedOpenRowBridgeBundle clause outerHandler)
    (h_removed :
      RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedCompose
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized := h_bridge.closedAwareEqNormalized
    normalizedHandledRemoved := h_removed
  }

theorem effectHandlerNestedOpenRowConsequenceBundle_as_components_of_bridge_and_normalizedHandledRemoved
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bridge : EffectHandlerNestedOpenRowBridgeBundle clause outerHandler)
    (h_removed :
      RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedCompose
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false) :
    (NestedHandlerCompositionContracts.nestedComposeClosedAware
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled =
      NestedHandlerCompositionContracts.nestedCompose
        clause.exprEffects
        clause.handlerEffects
        outerHandler
        clause.handled)
    ∧
    (RowFields.has
      (EffectRow.fields
        (NestedHandlerCompositionContracts.nestedCompose
          clause.exprEffects
          clause.handlerEffects
          outerHandler
          clause.handled))
      clause.handled = false) :=
  effectHandlerNestedOpenRowConsequenceBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowConsequenceBundle_of_bridge_and_normalizedHandledRemoved
      clause outerHandler h_bridge h_removed)

/-- One-hop projection: recover bridge bundle from strengthened consequence bundle. -/
theorem effectHandlerNestedOpenRowBridgeBundle_of_consequenceBundle
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler) :
    EffectHandlerNestedOpenRowBridgeBundle clause outerHandler := by
  exact {
    closedAwareEqNormalized := h_bundle.closedAwareEqNormalized
  }

theorem effectHandlerNestedOpenRowBridgeBundle_as_components_of_consequenceBundle
    (clause : HandleClauseContract)
    (outerHandler : EffectRow)
    (h_bundle : EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler) :
    NestedHandlerCompositionContracts.nestedComposeClosedAware
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled =
    NestedHandlerCompositionContracts.nestedCompose
      clause.exprEffects
      clause.handlerEffects
      outerHandler
      clause.handled :=
  effectHandlerNestedOpenRowBridgeBundle_as_components clause outerHandler
    (effectHandlerNestedOpenRowBridgeBundle_of_consequenceBundle clause outerHandler h_bundle)

/--
Strengthened consequence bundle is equivalent to:
- bridge bundle witness
- normalized handled-removal fact
-/
theorem effectHandlerNestedOpenRowConsequenceBundle_iff_bridge_and_normalizedHandledRemoved
    (clause : HandleClauseContract)
    (outerHandler : EffectRow) :
    EffectHandlerNestedOpenRowConsequenceBundle clause outerHandler
      ↔
      EffectHandlerNestedOpenRowBridgeBundle clause outerHandler
      ∧
      RowFields.has
        (EffectRow.fields
          (NestedHandlerCompositionContracts.nestedCompose
            clause.exprEffects
            clause.handlerEffects
            outerHandler
            clause.handled))
        clause.handled = false := by
  constructor
  · intro h_bundle
    exact ⟨
      effectHandlerNestedOpenRowBridgeBundle_of_consequenceBundle clause outerHandler h_bundle,
      h_bundle.normalizedHandledRemoved
    ⟩
  · intro h_comp
    exact effectHandlerNestedOpenRowConsequenceBundle_of_bridge_and_normalizedHandledRemoved
      clause
      outerHandler
      h_comp.1
      h_comp.2

end EffectHandlerContractSuite
end Kea
