/-
  Kea.Traits — Supertrait closure model for trait-bound checking.

  This module extends the simplified `TraitRegistry` model from `DataFrame.lean`
  with an explicit supertrait graph and closure-aware bound checking.

  Goal: provide a formal bridge target for the evidence/supertrait behavior now
  exposed by MCP observability (`resolve_traits`, `elaborate_evidence`).
-/

import Kea.DataFrame

abbrev TraitName := String

/-- Directed supertrait graph: `(t, s)` means `t : s`. -/
structure TraitGraph where
  edges : List (TraitName × TraitName)

namespace TraitGraph

def empty : TraitGraph := ⟨[]⟩

/-- Direct supertraits declared for `traitName`. -/
def directSupers (g : TraitGraph) (traitName : TraitName) : List TraitName :=
  g.edges.filterMap fun (t, s) =>
    if t == traitName then some s else none

/-- One graph-expansion step from a frontier of trait names. -/
def closureStep (g : TraitGraph) (frontier : List TraitName) : List TraitName :=
  (frontier.flatMap g.directSupers).eraseDups

/-- Fuel-bounded transitive supertrait expansion. -/
def closure (g : TraitGraph) : Nat → List TraitName → List TraitName
  | 0, _ => []
  | n + 1, frontier =>
      let next := closureStep g frontier
      next ++ closure g n next

/-- Required trait set for satisfying a bound, including transitive supertraits. -/
def requiredTraits (g : TraitGraph) (fuel : Nat) (traitName : TraitName) : List TraitName :=
  traitName :: (closure g fuel [traitName]).eraseDups

theorem directSupers_empty (traitName : TraitName) :
    directSupers empty traitName = [] := by
  simp [directSupers, empty]

theorem closure_empty (fuel : Nat) (frontier : List TraitName) :
    closure empty fuel frontier = [] := by
  induction fuel generalizing frontier with
  | zero =>
      rfl
  | succ n ih =>
      have hnext : closureStep empty frontier = [] := by
        induction frontier with
        | nil =>
            simp [closureStep]
        | cons t ts ihf =>
            simpa [closureStep, directSupers, empty] using ihf
      simp [closure, hnext, ih]

theorem requiredTraits_empty (fuel : Nat) (traitName : TraitName) :
    requiredTraits empty fuel traitName = [traitName] := by
  simp [requiredTraits, closure_empty]

end TraitGraph

namespace TraitRegistry

/-- Closure-aware trait satisfaction: trait and all required supertraits hold. -/
def satisfiesWithGraph (reg : TraitRegistry)
    (graph : TraitGraph) (graphFuel : Nat)
    (traitName typeName : String) : Bool :=
  (TraitGraph.requiredTraits graph graphFuel traitName).all
    (fun required => reg.satisfies required typeName)

theorem satisfiesWithGraph_implies_satisfies
    (reg : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat)
    (traitName typeName : String)
    (h : reg.satisfiesWithGraph graph graphFuel traitName typeName = true) :
    reg.satisfies traitName typeName = true := by
  have hAll :
      ∀ x ∈ TraitGraph.requiredTraits graph graphFuel traitName,
        reg.satisfies x typeName = true := by
    simpa [satisfiesWithGraph] using h
  exact hAll traitName (by simp [TraitGraph.requiredTraits])

theorem satisfiesWithGraph_empty_eq_satisfies
    (reg : TraitRegistry) (graphFuel : Nat)
    (traitName typeName : String) :
    reg.satisfiesWithGraph TraitGraph.empty graphFuel traitName typeName =
      reg.satisfies traitName typeName := by
  simp [satisfiesWithGraph, TraitGraph.requiredTraits_empty]

end TraitRegistry

/-- Supertrait-aware trait-bound checking.
    Reports unsatisfied `(requiredTrait, concreteType)` pairs. -/
def checkTraitBoundsWithGraph (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat) :
    List (String × String) :=
  traitBounds.flatMap fun (tv, traitName) =>
    let resolved := applySubst subst fuel (.var tv)
    match resolved with
    | .var _ => []
    | _ =>
      match typeNameForTraitCheck resolved with
      | none => []
      | some typeName =>
        (TraitGraph.requiredTraits graph graphFuel traitName).filterMap fun required =>
          if registry.satisfies required typeName then none
          else some (required, typeName)

/-- One-bound closure-aware checker contribution (list form, to compose via append). -/
def checkTraitBoundOneWithGraph
    (tv : TypeVarId) (traitName : String) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat) :
    List (String × String) :=
  let resolved := applySubst subst fuel (.var tv)
  match resolved with
  | .var _ => []
  | _ =>
    match typeNameForTraitCheck resolved with
    | none => []
    | some typeName =>
      (TraitGraph.requiredTraits graph graphFuel traitName).filterMap fun required =>
        if registry.satisfies required typeName then none
        else some (required, typeName)

/-- One-bound direct checker contribution (list form, to compose via append). -/
def checkTraitBoundOneDirect
    (tv : TypeVarId) (traitName : String) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) :
    List (String × String) :=
  let resolved := applySubst subst fuel (.var tv)
  match resolved with
  | .var _ => []
  | _ =>
    match typeNameForTraitCheck resolved with
    | none => []
    | some typeName =>
      if registry.satisfies traitName typeName then []
      else [(traitName, typeName)]

-- =========================================================================
-- Concrete boundary witness (matches MCP-observed supertrait gap shape)
-- =========================================================================

/-- Registry with only a direct `MyOrd for Int` impl (no `MyEq for Int`). -/
def regOrdOnly : TraitRegistry :=
  ⟨[{ traitName := "MyOrd", typeName := "Int" }]⟩

/-- Graph encoding `MyOrd : MyEq`. -/
def graphOrdRequiresEq : TraitGraph :=
  ⟨[("MyOrd", "MyEq")]⟩

theorem satisfies_direct_ord_only :
    TraitRegistry.satisfies regOrdOnly "MyOrd" "Int" = true := by
  simp [TraitRegistry.satisfies, TraitRegistry.hasImpl, regOrdOnly]

theorem requiredTraits_ord_requires_eq :
    TraitGraph.requiredTraits graphOrdRequiresEq 1 "MyOrd" = ["MyOrd", "MyEq"] := by
  native_decide

theorem satisfiesWithGraph_ord_only_false :
    TraitRegistry.satisfiesWithGraph regOrdOnly graphOrdRequiresEq 1 "MyOrd" "Int" = false := by
  native_decide

/-- Direct trait satisfaction can succeed while closure-aware satisfaction fails. -/
theorem supertrait_gap_witness :
    TraitRegistry.satisfies regOrdOnly "MyOrd" "Int" = true ∧
    TraitRegistry.satisfiesWithGraph regOrdOnly graphOrdRequiresEq 1 "MyOrd" "Int" = false := by
  exact ⟨satisfies_direct_ord_only, satisfiesWithGraph_ord_only_false⟩

/-- Witness substitution that resolves type variable `0` to `Int`. -/
def substVar0Int : Subst :=
  Subst.bindType Subst.empty 0 .int

/-- Witness bound set requiring `MyOrd` for type variable `0`. -/
def boundsVar0MyOrd : TraitBounds :=
  [(0, "MyOrd")]

/-- Witness bound set requiring `MyEq` for type variable `0`. -/
def boundsVar0MyEq : TraitBounds :=
  [(0, "MyEq")]

/-- Registry with both required impls (`MyOrd` and `MyEq`) for `Int`. -/
def regOrdAndEq : TraitRegistry :=
  ⟨[
    { traitName := "MyEq", typeName := "Int" },
    { traitName := "MyOrd", typeName := "Int" }
  ]⟩

/-- Closure-aware bound checking reports missing `MyEq` when only direct `MyOrd` exists. -/
theorem checkTraitBoundsWithGraph_ord_only_reports_missing_super :
    checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 =
      [("MyEq", "Int")] := by
  native_decide

/-- Direct (non-closure) bound checking accepts the same witness state. -/
theorem checkTraitBounds_direct_ord_only_accepts :
    checkTraitBounds boundsVar0MyOrd substVar0Int 1 regOrdOnly = [] := by
  native_decide

/-- Adding the supertrait impl closes the closure-aware bound-checking gap. -/
theorem checkTraitBoundsWithGraph_ord_and_eq_accepts :
    checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = [] := by
  native_decide

/-- Direct checker also accepts once both required impls are present. -/
theorem checkTraitBounds_direct_ord_and_eq_accepts :
    checkTraitBounds boundsVar0MyOrd substVar0Int 1 regOrdAndEq = [] := by
  native_decide

/-- Direct bound checking reports missing `MyOrd` when no impl is registered. -/
theorem checkTraitBounds_direct_no_impl_reports_ord :
    checkTraitBounds boundsVar0MyOrd substVar0Int 1 TraitRegistry.empty = [("MyOrd", "Int")] := by
  native_decide

/-- Closure-aware bound checking reports both `MyOrd` and `MyEq` with no impls. -/
theorem checkTraitBoundsWithGraph_no_impl_reports_ord_and_eq :
    checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 TraitRegistry.empty graphOrdRequiresEq 1 =
      [("MyOrd", "Int"), ("MyEq", "Int")] := by
  native_decide

/-- Direct bound checking reports missing `MyEq` when no impl is registered. -/
theorem checkTraitBounds_direct_no_impl_reports_eq :
    checkTraitBounds boundsVar0MyEq substVar0Int 1 TraitRegistry.empty = [("MyEq", "Int")] := by
  native_decide

/-- Modeled direct call-site acceptance: all direct trait bounds must be discharged. -/
def callSiteAcceptsDirect (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) : Bool :=
  (checkTraitBounds traitBounds subst fuel registry).isEmpty

/-- Modeled closure-aware call-site acceptance: direct + supertrait obligations must be discharged. -/
def callSiteAcceptsWithGraph (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat) : Bool :=
  (checkTraitBoundsWithGraph traitBounds subst fuel registry graph graphFuel).isEmpty

/-- Boundary-sensitive sites where trait call-site gates are enforced. -/
inductive TraitCallBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level wrapper for direct call-site acceptance gate. -/
def callSiteAcceptsDirectAtSite
    (_site : TraitCallBoundarySite)
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) : Bool :=
  callSiteAcceptsDirect traitBounds subst fuel registry

/-- Site-level wrapper for closure-aware call-site acceptance gate. -/
def callSiteAcceptsWithGraphAtSite
    (_site : TraitCallBoundarySite)
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat) : Bool :=
  callSiteAcceptsWithGraph traitBounds subst fuel registry graph graphFuel

/-- Direct trait call-site gate is currently site-invariant. -/
theorem trait_call_boundary_policy_site_invariant_direct
    (site1 site2 : TraitCallBoundarySite)
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) :
    callSiteAcceptsDirectAtSite site1 traitBounds subst fuel registry =
      callSiteAcceptsDirectAtSite site2 traitBounds subst fuel registry := by
  cases site1 <;> cases site2 <;> rfl

/-- Closure-aware trait call-site gate is currently site-invariant. -/
theorem trait_call_boundary_policy_site_invariant_with_graph
    (site1 site2 : TraitCallBoundarySite)
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat) :
    callSiteAcceptsWithGraphAtSite site1 traitBounds subst fuel registry graph graphFuel =
      callSiteAcceptsWithGraphAtSite site2 traitBounds subst fuel registry graph graphFuel := by
  cases site1 <;> cases site2 <;> rfl

theorem callSiteAcceptsDirect_eq_true_iff
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat) (registry : TraitRegistry) :
    callSiteAcceptsDirect traitBounds subst fuel registry = true ↔
      checkTraitBounds traitBounds subst fuel registry = [] := by
  simp [callSiteAcceptsDirect]

theorem callSiteAcceptsWithGraph_eq_true_iff
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat) :
    callSiteAcceptsWithGraph traitBounds subst fuel registry graph graphFuel = true ↔
      checkTraitBoundsWithGraph traitBounds subst fuel registry graph graphFuel = [] := by
  simp [callSiteAcceptsWithGraph]

/-- Reusable bridge premise: closure-aware checker acceptance refines to direct checker acceptance. -/
def TraitBoundRefinementPremise : Prop :=
  ∀ (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat),
    checkTraitBoundsWithGraph traitBounds subst fuel registry graph graphFuel = [] →
      checkTraitBounds traitBounds subst fuel registry = []

theorem callSiteAcceptsWithGraph_implies_direct_of_premise
    (hPrem : TraitBoundRefinementPremise)
    (traitBounds : TraitBounds) (subst : Subst) (fuel : Nat)
    (registry : TraitRegistry) (graph : TraitGraph) (graphFuel : Nat)
    (h :
      callSiteAcceptsWithGraph traitBounds subst fuel registry graph graphFuel = true) :
    callSiteAcceptsDirect traitBounds subst fuel registry = true := by
  have hGraph :
      checkTraitBoundsWithGraph traitBounds subst fuel registry graph graphFuel = [] :=
    (callSiteAcceptsWithGraph_eq_true_iff traitBounds subst fuel registry graph graphFuel).1 h
  have hDirect :
      checkTraitBounds traitBounds subst fuel registry = [] :=
    hPrem traitBounds subst fuel registry graph graphFuel hGraph
  exact (callSiteAcceptsDirect_eq_true_iff traitBounds subst fuel registry).2 hDirect

theorem callSiteAcceptsDirect_ord_only_true :
    callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 regOrdOnly = true := by
  native_decide

theorem callSiteAcceptsWithGraph_ord_only_false :
    callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 = false := by
  native_decide

theorem callSiteAcceptsWithGraph_ord_and_eq_true :
    callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = true := by
  native_decide

theorem callSiteAcceptsWithGraph_ord_and_eq_implies_direct
    :
    callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = true →
    callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 regOrdAndEq = true := by
  intro _
  native_decide

/-- Witness-specific refinement premise for the fully-implemented `MyOrd`/`MyEq` state. -/
def TraitBoundRefinementPremise_ord_and_eq_witness : Prop :=
  checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = [] →
    checkTraitBounds boundsVar0MyOrd substVar0Int 1 regOrdAndEq = []

theorem traitBoundRefinementPremise_ord_and_eq_witness_proved :
    TraitBoundRefinementPremise_ord_and_eq_witness := by
  intro _
  exact checkTraitBounds_direct_ord_and_eq_accepts

theorem callSiteAcceptsWithGraph_ord_and_eq_implies_direct_via_premise :
    callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = true →
      callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 regOrdAndEq = true := by
  intro h
  have hGraph :
      checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = [] :=
    (callSiteAcceptsWithGraph_eq_true_iff
      boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1).1 h
  have hDirect :
      checkTraitBounds boundsVar0MyOrd substVar0Int 1 regOrdAndEq = [] :=
    traitBoundRefinementPremise_ord_and_eq_witness_proved hGraph
  exact (callSiteAcceptsDirect_eq_true_iff boundsVar0MyOrd substVar0Int 1 regOrdAndEq).2 hDirect

theorem callSiteAcceptsDirect_no_impl_ord_false :
    callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 TraitRegistry.empty = false := by
  native_decide

theorem callSiteAcceptsDirect_no_impl_eq_false :
    callSiteAcceptsDirect boundsVar0MyEq substVar0Int 1 TraitRegistry.empty = false := by
  native_decide

/-- Packaged supertrait-closure boundary witness contract for downstream citation. -/
def TraitClosureGapSlice : Prop :=
  TraitRegistry.satisfies regOrdOnly "MyOrd" "Int" = true ∧
  TraitRegistry.satisfiesWithGraph regOrdOnly graphOrdRequiresEq 1 "MyOrd" "Int" = false ∧
  checkTraitBounds boundsVar0MyOrd substVar0Int 1 regOrdOnly = [] ∧
  checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 =
    [("MyEq", "Int")] ∧
  checkTraitBoundsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = []

theorem traitClosureGapSlice_proved : TraitClosureGapSlice := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact satisfies_direct_ord_only
  · exact satisfiesWithGraph_ord_only_false
  · exact checkTraitBounds_direct_ord_only_accepts
  · exact checkTraitBoundsWithGraph_ord_only_reports_missing_super
  · exact checkTraitBoundsWithGraph_ord_and_eq_accepts

/-- Packaged call-site enforcement contract for direct vs closure-aware checking. -/
def TraitCallSiteEnforcementSlice : Prop :=
  callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 regOrdOnly = true ∧
  callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 = false ∧
  callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = true ∧
  callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 TraitRegistry.empty = false ∧
  callSiteAcceptsDirect boundsVar0MyEq substVar0Int 1 TraitRegistry.empty = false

theorem traitCallSiteEnforcementSlice_proved : TraitCallSiteEnforcementSlice := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact callSiteAcceptsDirect_ord_only_true
  · exact callSiteAcceptsWithGraph_ord_only_false
  · exact callSiteAcceptsWithGraph_ord_and_eq_true
  · exact callSiteAcceptsDirect_no_impl_ord_false
  · exact callSiteAcceptsDirect_no_impl_eq_false

/-- Witness-level refinement slice: closure-aware acceptance implies direct acceptance
    on the fully-implemented witness state, while direct-only acceptance remains strictly weaker. -/
def TraitCallSiteRefinementWitnessSlice : Prop :=
  (callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = true →
    callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 regOrdAndEq = true) ∧
  callSiteAcceptsWithGraph boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 = false ∧
  callSiteAcceptsDirect boundsVar0MyOrd substVar0Int 1 regOrdOnly = true

theorem traitCallSiteRefinementWitnessSlice_proved : TraitCallSiteRefinementWitnessSlice := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact callSiteAcceptsWithGraph_ord_and_eq_implies_direct h
  · exact callSiteAcceptsWithGraph_ord_only_false
  · exact callSiteAcceptsDirect_ord_only_true

/-- Packaged site-level call-site enforcement surface:
    direct-vs-closure outcomes are invariant across boundary-sensitive sites
    and preserve the witness-state acceptance/rejection shape. -/
theorem trait_call_boundary_surface_slice (site : TraitCallBoundarySite) :
    callSiteAcceptsDirectAtSite site boundsVar0MyOrd substVar0Int 1 regOrdOnly = true ∧
      callSiteAcceptsWithGraphAtSite site boundsVar0MyOrd substVar0Int 1 regOrdOnly graphOrdRequiresEq 1 = false ∧
      callSiteAcceptsWithGraphAtSite site boundsVar0MyOrd substVar0Int 1 regOrdAndEq graphOrdRequiresEq 1 = true ∧
      callSiteAcceptsDirectAtSite site boundsVar0MyOrd substVar0Int 1 TraitRegistry.empty = false ∧
      callSiteAcceptsDirectAtSite site boundsVar0MyEq substVar0Int 1 TraitRegistry.empty = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact callSiteAcceptsDirect_ord_only_true
  · cases site <;> exact callSiteAcceptsWithGraph_ord_only_false
  · cases site <;> exact callSiteAcceptsWithGraph_ord_and_eq_true
  · cases site <;> exact callSiteAcceptsDirect_no_impl_ord_false
  · cases site <;> exact callSiteAcceptsDirect_no_impl_eq_false

-- =========================================================================
-- Actor message-style dispatch boundary (post-61bd3a1 surface)
-- =========================================================================

/-- Minimal actor call-site dispatch model:
    method name plus required argument count. -/
structure ActorDispatchModel where
  methods : List (String × Nat)

namespace ActorDispatchModel

/-- Generic dispatch acceptance: method exists with exact arity. -/
def accepts (model : ActorDispatchModel) (method : String) (argCount : Nat) : Bool :=
  model.methods.any (fun (name, arity) => name == method && arity == argCount)

/-- Message-style actor operations desugar to `handle(message)`. -/
def acceptsMessageStyle (model : ActorDispatchModel) : Bool :=
  accepts model "handle" 1

/-- Legacy actor operations use explicit atom method names (`:inc`, `:get`, ...). -/
def acceptsLegacyStyle (model : ActorDispatchModel) (method : String) (argCount : Nat) : Bool :=
  accepts model method argCount

end ActorDispatchModel

/-- Witness protocol after message-style migration:
    only `handle` is dispatchable. -/
def actorDispatchHandleOnly : ActorDispatchModel :=
  ⟨[("handle", 1)]⟩

theorem actorDispatch_message_style_accepts_handle_only :
    ActorDispatchModel.acceptsMessageStyle actorDispatchHandleOnly = true := by
  native_decide

theorem actorDispatch_legacy_inc_rejected_on_handle_only :
    ActorDispatchModel.acceptsLegacyStyle actorDispatchHandleOnly "inc" 0 = false := by
  native_decide

theorem actorDispatch_legacy_handle_single_arg_accepts :
    ActorDispatchModel.acceptsLegacyStyle actorDispatchHandleOnly "handle" 1 = true := by
  native_decide

/-- Boundary-sensitive sites where actor dispatch checks are enforced. -/
inductive ActorDispatchBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level wrapper for message-style actor dispatch acceptance. -/
def actorDispatchAcceptsMessageAtSite
    (_site : ActorDispatchBoundarySite) (model : ActorDispatchModel) : Bool :=
  ActorDispatchModel.acceptsMessageStyle model

/-- Site-level wrapper for legacy-style actor dispatch acceptance. -/
def actorDispatchAcceptsLegacyAtSite
    (_site : ActorDispatchBoundarySite) (model : ActorDispatchModel)
    (method : String) (argCount : Nat) : Bool :=
  ActorDispatchModel.acceptsLegacyStyle model method argCount

/-- Message-style actor dispatch gate is currently site-invariant. -/
theorem actor_dispatch_boundary_policy_site_invariant_message
    (site1 site2 : ActorDispatchBoundarySite) (model : ActorDispatchModel) :
    actorDispatchAcceptsMessageAtSite site1 model =
      actorDispatchAcceptsMessageAtSite site2 model := by
  cases site1 <;> cases site2 <;> rfl

/-- Legacy-style actor dispatch gate is currently site-invariant. -/
theorem actor_dispatch_boundary_policy_site_invariant_legacy
    (site1 site2 : ActorDispatchBoundarySite) (model : ActorDispatchModel)
    (method : String) (argCount : Nat) :
    actorDispatchAcceptsLegacyAtSite site1 model method argCount =
      actorDispatchAcceptsLegacyAtSite site2 model method argCount := by
  cases site1 <;> cases site2 <;> rfl

/-- Packaged site-level actor dispatch boundary:
    message-style dispatch remains accepted while legacy `:inc` rejects
    (and legacy explicit `handle` still accepts) at all boundary sites. -/
theorem actor_dispatch_boundary_surface_slice (site : ActorDispatchBoundarySite) :
    actorDispatchAcceptsMessageAtSite site actorDispatchHandleOnly = true ∧
      actorDispatchAcceptsLegacyAtSite site actorDispatchHandleOnly "inc" 0 = false ∧
      actorDispatchAcceptsLegacyAtSite site actorDispatchHandleOnly "handle" 1 = true := by
  refine ⟨?_, ?_, ?_⟩
  · cases site <;> exact actorDispatch_message_style_accepts_handle_only
  · cases site <;> exact actorDispatch_legacy_inc_rejected_on_handle_only
  · cases site <;> exact actorDispatch_legacy_handle_single_arg_accepts

/-- Packaged actor dispatch boundary:
    message-style calls are accepted while legacy `:inc`-style calls reject
    once the protocol exposes only `handle`. -/
def ActorMessageDispatchBoundarySlice : Prop :=
  ActorDispatchModel.acceptsMessageStyle actorDispatchHandleOnly = true ∧
  ActorDispatchModel.acceptsLegacyStyle actorDispatchHandleOnly "inc" 0 = false ∧
  ActorDispatchModel.acceptsLegacyStyle actorDispatchHandleOnly "handle" 1 = true

theorem actorMessageDispatchBoundarySlice_proved : ActorMessageDispatchBoundarySlice := by
  refine ⟨?_, ?_, ?_⟩
  · exact actorDispatch_message_style_accepts_handle_only
  · exact actorDispatch_legacy_inc_rejected_on_handle_only
  · exact actorDispatch_legacy_handle_single_arg_accepts
