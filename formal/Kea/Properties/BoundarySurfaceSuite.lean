import Kea.Properties.TemporalLeafParity
import Kea.Properties.PrecisionLeafParity
import Kea.Properties.DecimalParity
import Kea.Properties.NominalAdtParity
import Kea.Properties.NominalAdtTypingBridge
import Kea.Properties.RecordStructuralProjection
import Kea.Properties.HigherOrderConstructorParity
import Kea.Properties.ForallParity
import Kea.Properties.ExistentialParity
import Kea.Properties.RuntimeWrapperParity
import Kea.Properties.DynamicBoundaryTypingBridge
import Kea.Properties.WrapperBoundaryTypingBridge
import Kea.Properties.GroupedTaggedParity
import Kea.Properties.GroupedTaggedTypingBridge
import Kea.Properties.BoundaryAscriptionSyntax
import Kea.Properties.ColumnBoundary
import Kea.Traits

/-!
  Kea.Properties.BoundarySurfaceSuite

  Cross-family boundary surface package: compose the existing per-family
  boundary slices into one theorem-level contract for downstream citation.
-/

/-- Packaged language-level typing-bridge slice at explicit boundary sites. -/
def BoundarySurfaceTypingBridgeSliceAtSites
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) : Prop :=
  (dynamicBoundaryAllowsAtSite dynamicSite .int .dynamic = false)
  ∧
  (¬ HasTypeAtAscriptionBoundaryAtSite dynamicSite [("x", .dynamic)] (.var "x") .int)
  ∧
  (HasTypeAtAscriptionBoundaryAtSite dynamicSite [("x", .dynamic)] (.var "x") .dynamic)
  ∧
  (¬ HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperTaskVarBoolEnv (.var "t") (.task .int))
  ∧
  (¬ HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperIntVarEnv (.var "x") (.task .int))
  ∧
  (HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperTaskVarIntEnv (.var "t") (.task .int))
  ∧
  (¬ HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperActorVarBoolEnv (.var "a") (.actor .int))
  ∧
  (¬ HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperIntVarEnv (.var "x") (.actor .int))
  ∧
  (HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperActorVarIntEnv (.var "a") (.actor .int))
  ∧
  (¬ HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperArcVarBoolEnv (.var "r") (.arc .int))
  ∧
  (¬ HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperIntVarEnv (.var "x") (.arc .int))
  ∧
  (HasTypeAtWrapperBoundaryAtSite wrapperSite wrapperArcVarIntEnv (.var "r") (.arc .int))
  ∧
  (¬ HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"]))
  ∧
  (¬ HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite intVarEnv (.var "x") (.groupedFrame .int ["a"]))
  ∧
  (HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"]))
  ∧
  (¬ HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite taggedVarBoolEnv (.var "t") (.tagged .int [("unit", 1)]))
  ∧
  (¬ HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite intVarEnv (.var "x") (.tagged .int [("unit", 1)]))
  ∧
  (HasTypeAtGroupedTaggedBoundaryAtSite groupedTaggedSite taggedVarIntEnv (.var "t") (.tagged .int [("unit", 1)]))

/-- Ascription-specialized alias for `BoundarySurfaceTypingBridgeSliceAtSites`. -/
abbrev BoundarySurfaceTypingBridgeSlice : Prop :=
  BoundarySurfaceTypingBridgeSliceAtSites .ascription .ascription .ascription

/-- Proof witness for `BoundarySurfaceTypingBridgeSliceAtSites`. -/
theorem boundarySurfaceTypingBridgeSliceAtSites_proved
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite) :
    BoundarySurfaceTypingBridgeSliceAtSites dynamicSite wrapperSite groupedTaggedSite := by
  rcases dynamic_boundary_typing_bridge_ascription_all_sites dynamicSite with
    ⟨h_dyn_reject, h_dyn_narrow, h_dyn_accept⟩
  rcases wrapper_typing_bridge_all_sites wrapperSite with
    ⟨h_task_inner, h_task_non_wrapper, h_task_id,
      h_actor_inner, h_actor_non_wrapper, h_actor_id,
      h_arc_inner, h_arc_non_wrapper, h_arc_id⟩
  rcases grouped_tagged_typing_bridge_all_sites groupedTaggedSite with
    ⟨h_grouped_inner, h_grouped_non_wrapper, h_grouped_id,
      h_tagged_inner, h_tagged_non_wrapper, h_tagged_id⟩
  exact ⟨h_dyn_reject, h_dyn_narrow, h_dyn_accept,
    h_task_inner, h_task_non_wrapper, h_task_id,
    h_actor_inner, h_actor_non_wrapper, h_actor_id,
    h_arc_inner, h_arc_non_wrapper, h_arc_id,
    h_grouped_inner, h_grouped_non_wrapper, h_grouped_id,
    h_tagged_inner, h_tagged_non_wrapper, h_tagged_id⟩

/-- Proof witness for ascription-specialized `BoundarySurfaceTypingBridgeSlice`. -/
theorem boundarySurfaceTypingBridgeSlice_proved : BoundarySurfaceTypingBridgeSlice := by
  simpa [BoundarySurfaceTypingBridgeSlice]
    using boundarySurfaceTypingBridgeSliceAtSites_proved
      .ascription .ascription .ascription

/-- Cross-family boundary surface contract.
    This theorem does not introduce new boundary behavior; it packages the
    already-proved slices for convenient reuse as one citation point. -/
theorem boundary_surface_suite
    (st : UnifyState)
    (leafSite : LeafBoundarySite)
    (precisionSite : PrecisionBoundarySite)
    (decimalSite : DecimalBoundarySite)
    (nominalAdtSite : NominalAdtBoundarySite)
    (recordSite : RecordBoundarySite) (recordName : String) (recordRow : Row)
    (constructorSite : ConstructorGuardBoundarySite)
    (forallSite : ForallBoundarySite)
    (existentialSite : ExistentialBoundarySite)
    (dynamicSite : DynamicBoundarySite)
    (wrapperSite : WrapperBoundarySite)
    (groupedTaggedSite : GroupedTaggedBoundarySite)
    (columnSite : ColumnBoundarySite)
    (traitSite : TraitCallBoundarySite)
    (actorSite : ActorDispatchBoundarySite) :
    leafBoundaryAllowsAtSite leafSite .html .markdown = false
    ∧ precisionBoundaryAllowsAtSite precisionSite (.intN .i32 .signed) (.intN .i64 .signed) = false
    ∧ decimalBoundaryAllowsAtSite decimalSite
        (.decimal (.const 10) (.const 2))
        (.decimal (.const 10) (.const 3)) = false
    ∧ nominalAdtBoundaryAllowsAtSite nominalAdtSite (.sum "A" .nil) (.sum "B" .nil) = false
    ∧ recordBoundaryAllowsAtSite recordSite (.anonRecord recordRow) (.record recordName recordRow) = true
    ∧ recordBoundaryAllowsAtSite recordSite (.record recordName recordRow) (.anonRecord recordRow) = false
    ∧ constructorGuardBoundaryAllowsAtSite constructorSite
        (.constructor "List" (.cons .int .nil) 1)
        (.constructor "Map" (.cons .int .nil) 1) = false
    ∧ forallBoundaryAllowsAtSite forallSite
        (.forall ["a"] (.function (.cons .int .nil) .int))
        (.forall ["b"] (.function (.cons .int .nil) .int)) = true
    ∧ forallBoundaryAllowsAtSite forallSite
        (.forall ["a"] .int)
        (.forall ["b"] .bool) = false
    ∧ existentialBoundaryAllowsAtSite existentialSite
        (.existential ["Show"] (.cons .int .nil))
        (.existential ["Eq"] (.cons .int .nil)) = false
    ∧ dynamicBoundaryAllowsAtSite dynamicSite .int .dynamic = false
    ∧ dynamicBoundaryAllowsAtSite dynamicSite .dynamic .int = true
    ∧ wrapperBoundaryAllowsAtSite wrapperSite (.task .int) (.task .bool) = false
    ∧ groupedTaggedBoundaryAllowsAtSite groupedTaggedSite
        (.groupedFrame .int ["a"])
        (.groupedFrame .int ["b"]) = false
    ∧ columnBoundaryAllowsAtSite columnSite .int (.column .int) = false
    ∧ columnBoundaryAllowsAtSite columnSite (.column .int) .int = false
    ∧ callSiteAcceptsDirectAtSite traitSite boundsVar0MyOrd substVar0Int 1 regOrdOnly = true
    ∧ callSiteAcceptsWithGraphAtSite
        traitSite boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 = false
    ∧ actorDispatchAcceptsMessageAtSite actorSite actorDispatchHandleOnly = true
    ∧ actorDispatchAcceptsLegacyAtSite actorSite actorDispatchHandleOnly "inc" 0 = false
    ∧ NominalAdtTypingBridgeSliceAtSites nominalAdtSite
    ∧ NominalAdtAscriptionAlgorithmicSliceAtSite nominalAdtSite
    ∧ BoundarySurfaceTypingBridgeSliceAtSites dynamicSite wrapperSite groupedTaggedSite
    ∧ AscriptionInferExprBridgeSliceAtSites
        dynamicSite wrapperSite groupedTaggedSite
    ∧ AscriptionInferExprCompletenessSliceAtSites
        dynamicSite wrapperSite groupedTaggedSite
    ∧ AscriptionAlgorithmicDeclarativeAlignmentSliceAtSites
        dynamicSite wrapperSite groupedTaggedSite
    ∧ AscriptionInferExprIffSliceAtSites
        dynamicSite wrapperSite groupedTaggedSite
    ∧ AscriptionCoreInferRoutingSliceAtSites
        dynamicSite wrapperSite groupedTaggedSite
    ∧ AscriptionBaseEmbeddingSliceAtSites
        dynamicSite wrapperSite groupedTaggedSite
    ∧ BoundaryAscriptionBridgeSuiteAtSites
        dynamicSite wrapperSite groupedTaggedSite := by
  have h_leaf := leaf_boundary_surface_slice st leafSite
  have h_precision := precision_boundary_surface_slice st precisionSite
  have h_decimal := decimal_boundary_surface_slice st decimalSite
  have h_nominal := nominal_adt_boundary_surface_slice st nominalAdtSite
  have h_record := record_boundary_directional_policy_all_sites
      recordSite recordName recordRow
  have h_constructor := constructor_guard_boundary_surface_slice st constructorSite
  have h_forall := forall_boundary_surface_slice st forallSite
  have h_existential := existential_boundary_surface_slice st existentialSite
  have h_dynamic := dynamic_boundary_surface_slice st dynamicSite
  have h_wrapper := wrapper_boundary_surface_slice st wrapperSite
  have h_grouped := grouped_tagged_boundary_surface_slice st groupedTaggedSite
  have h_column := column_boundary_surface_slice st columnSite
  have h_trait := trait_call_boundary_surface_slice traitSite
  have h_actor := actor_dispatch_boundary_surface_slice actorSite
  have h_nominal_typing := nominalAdtTypingBridgeSliceAtSites_proved nominalAdtSite
  have h_nominal_ascription := nominalAdtAscriptionAlgorithmicSliceAtSite_proved nominalAdtSite
  refine ⟨
    h_leaf.1,
    h_precision.1,
    h_decimal.1,
    h_nominal.1,
    h_record.1,
    h_record.2,
    h_constructor.1,
    h_forall.1,
    h_forall.2.2.1,
    h_existential.1,
    h_dynamic.1,
    h_dynamic.2.2.2.1,
    h_wrapper.1,
    h_grouped.1,
    h_column.1,
    h_column.2.1,
    h_trait.1,
    h_trait.2.1,
    h_actor.1,
    h_actor.2.1,
    h_nominal_typing,
    h_nominal_ascription,
    boundarySurfaceTypingBridgeSliceAtSites_proved dynamicSite wrapperSite groupedTaggedSite,
    ascriptionInferExprBridgeSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionInferExprCompletenessSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionAlgorithmicDeclarativeAlignmentSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionInferExprIffSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionCoreInferRoutingSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    ascriptionBaseEmbeddingSliceAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite,
    boundaryAscriptionBridgeSuiteAtSites_proved
      dynamicSite wrapperSite groupedTaggedSite
  ⟩
