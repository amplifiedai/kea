import Kea.Typing
import Kea.Properties.GroupedTaggedParity
import Kea.Properties.BoundaryAssignability

/-!
  Kea.Properties.GroupedTaggedTypingBridge

  Language-level bridge for grouped/tagged wrapper behavior at a modeled
  ascription boundary gate.
-/

/-- Modeled grouped/tagged boundary gate at a chosen boundary site:
    expression `e` inhabits `expected` iff it has some actual type that both
    passes grouped/tagged boundary policy and unifies with `expected`. -/
def HasTypeAtGroupedTaggedBoundaryAtSite
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtBoundary
    (allowsByBoolAndUnify
      (groupedTaggedBoundaryAllowsAtSite site)
      UnifyState.empty
      2)
    env e expected

/-- Modeled grouped/tagged ascription gate (site-specialized alias). -/
abbrev HasTypeAtGroupedTaggedBoundary
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtGroupedTaggedBoundaryAtSite .ascription env e expected

/-- Grouped/tagged typing gate is site-invariant because grouped/tagged
    boundary policy is currently site-invariant. -/
theorem hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription
    (site : GroupedTaggedBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeAtGroupedTaggedBoundaryAtSite site env e expected
      ↔ HasTypeAtGroupedTaggedBoundary env e expected := by
  refine hasTypeAtBoundary_congr
    (allowsByBoolAndUnify (groupedTaggedBoundaryAllowsAtSite site) UnifyState.empty 2)
    (allowsByBoolAndUnify (groupedTaggedBoundaryAllowsAtSite .ascription) UnifyState.empty 2)
    env e expected ?_
  intro exp act
  have h_site :
      groupedTaggedBoundaryAllowsAtSite site exp act
        = groupedTaggedBoundaryAllowsAtSite .ascription exp act :=
    grouped_tagged_boundary_policy_site_invariant site .ascription exp act
  unfold allowsByBoolAndUnify
  simp [h_site]

abbrev groupedVarIntEnv : TermEnv := [("g", .groupedFrame .int ["a"])]
abbrev groupedVarBoolEnv : TermEnv := [("g", .groupedFrame .bool ["a"])]
abbrev taggedVarIntEnv : TermEnv := [("t", .tagged .int [("unit", 1)])]
abbrev taggedVarBoolEnv : TermEnv := [("t", .tagged .bool [("unit", 1)])]
abbrev intVarEnv : TermEnv := [("x", .int)]

/-- `g` has the unique grouped-Int type in `groupedVarIntEnv`. -/
theorem hasType_var_grouped_int_unique
    (ty : Ty)
    (h_ty : HasType groupedVarIntEnv (.var "g") ty) :
    ty = .groupedFrame .int ["a"] := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [groupedVarIntEnv, TermEnv.lookup] using h_lookup.symm

/-- `g` has the unique grouped-Bool type in `groupedVarBoolEnv`. -/
theorem hasType_var_grouped_bool_unique
    (ty : Ty)
    (h_ty : HasType groupedVarBoolEnv (.var "g") ty) :
    ty = .groupedFrame .bool ["a"] := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [groupedVarBoolEnv, TermEnv.lookup] using h_lookup.symm

/-- `t` has the unique tagged-Int type in `taggedVarIntEnv`. -/
theorem hasType_var_tagged_int_unique
    (ty : Ty)
    (h_ty : HasType taggedVarIntEnv (.var "t") ty) :
    ty = .tagged .int [("unit", 1)] := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [taggedVarIntEnv, TermEnv.lookup] using h_lookup.symm

/-- `t` has the unique tagged-Bool type in `taggedVarBoolEnv`. -/
theorem hasType_var_tagged_bool_unique
    (ty : Ty)
    (h_ty : HasType taggedVarBoolEnv (.var "t") ty) :
    ty = .tagged .bool [("unit", 1)] := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [taggedVarBoolEnv, TermEnv.lookup] using h_lookup.symm

/-- `x` has the unique bare `Int` type in `intVarEnv`. -/
theorem hasType_var_int_unique
    (ty : Ty)
    (h_ty : HasType intVarEnv (.var "x") ty) :
    ty = .int := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [intVarEnv, TermEnv.lookup] using h_lookup.symm

/-- Grouped inner mismatch is rejected by modeled ascription gate.
    Boundary policy allows this shape (keys match), but unifier rejects it. -/
theorem hasType_ascription_grouped_inner_mismatch_rejected :
    ¬ HasTypeAtGroupedTaggedBoundary groupedVarBoolEnv (.var "g")
      (.groupedFrame .int ["a"]) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨_h_allow, h_unify⟩
  rcases h_unify with ⟨_, h_unify⟩
  have h_actual : actual = .groupedFrame .bool ["a"] :=
    hasType_var_grouped_bool_unique actual h_ty
  subst h_actual
  have h_err :
      unify UnifyState.empty 2
        (.groupedFrame .int ["a"])
        (.groupedFrame .bool ["a"])
      = .err "type mismatch" :=
    groupedFrame_inner_mismatch UnifyState.empty
  rw [h_err] at h_unify
  cases h_unify

/-- Grouped from bare Int is rejected by modeled ascription gate. -/
theorem hasType_ascription_grouped_from_int_rejected :
    ¬ HasTypeAtGroupedTaggedBoundary intVarEnv (.var "x")
      (.groupedFrame .int ["a"]) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .int := hasType_var_int_unique actual h_ty
  subst h_actual
  have h_reject :
      groupedTaggedBoundaryAllowsAtSite .ascription
        (.groupedFrame .int ["a"])
        .int
      = false := by
    simpa [groupedTaggedBoundaryAllowsAtSite] using grouped_tagged_boundary_rejects_non_wrapper_actual
  simp [h_reject] at h_allow

/-- Grouped identity ascription remains accepted. -/
theorem hasType_ascription_grouped_accepts :
    HasTypeAtGroupedTaggedBoundary groupedVarIntEnv (.var "g")
      (.groupedFrame .int ["a"]) := by
  refine ⟨.groupedFrame .int ["a"], ?_, ?_⟩
  · exact HasType.var groupedVarIntEnv "g" (.groupedFrame .int ["a"]) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (groupedFrame_unifies_with_self UnifyState.empty 1 .int ["a"])

/-- Tagged inner mismatch is rejected by modeled ascription gate.
    Boundary policy allows this shape (metadata matches), but unifier rejects it. -/
theorem hasType_ascription_tagged_inner_mismatch_rejected :
    ¬ HasTypeAtGroupedTaggedBoundary taggedVarBoolEnv (.var "t")
      (.tagged .int [("unit", 1)]) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨_h_allow, h_unify⟩
  rcases h_unify with ⟨_, h_unify⟩
  have h_actual : actual = .tagged .bool [("unit", 1)] :=
    hasType_var_tagged_bool_unique actual h_ty
  subst h_actual
  have h_err :
      unify UnifyState.empty 2
        (.tagged .int [("unit", 1)])
        (.tagged .bool [("unit", 1)])
      = .err "type mismatch" :=
    tagged_inner_mismatch UnifyState.empty
  rw [h_err] at h_unify
  cases h_unify

/-- Tagged from bare Int is rejected by modeled ascription gate. -/
theorem hasType_ascription_tagged_from_int_rejected :
    ¬ HasTypeAtGroupedTaggedBoundary intVarEnv (.var "x")
      (.tagged .int [("unit", 1)]) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .int := hasType_var_int_unique actual h_ty
  subst h_actual
  have h_reject :
      groupedTaggedBoundaryAllowsAtSite .ascription
        (.tagged .int [("unit", 1)])
        .int
      = false := by
    native_decide
  simp [h_reject] at h_allow

/-- Tagged identity ascription remains accepted. -/
theorem hasType_ascription_tagged_accepts :
    HasTypeAtGroupedTaggedBoundary taggedVarIntEnv (.var "t")
      (.tagged .int [("unit", 1)]) := by
  refine ⟨.tagged .int [("unit", 1)], ?_, ?_⟩
  · exact HasType.var taggedVarIntEnv "t" (.tagged .int [("unit", 1)]) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (tagged_unifies_with_self UnifyState.empty 1 .int [("unit", 1)])

/-- Packaged grouped/tagged typing bridge at modeled ascription boundary:
    inner mismatch and non-wrapper rejection hold, while grouped/tagged
    identity controls remain accepted. -/
theorem grouped_tagged_typing_bridge_ascription :
    ¬ HasTypeAtGroupedTaggedBoundary groupedVarBoolEnv (.var "g")
      (.groupedFrame .int ["a"])
    ∧
    ¬ HasTypeAtGroupedTaggedBoundary intVarEnv (.var "x")
      (.groupedFrame .int ["a"])
    ∧
    HasTypeAtGroupedTaggedBoundary groupedVarIntEnv (.var "g")
      (.groupedFrame .int ["a"])
    ∧
    ¬ HasTypeAtGroupedTaggedBoundary taggedVarBoolEnv (.var "t")
      (.tagged .int [("unit", 1)])
    ∧
    ¬ HasTypeAtGroupedTaggedBoundary intVarEnv (.var "x")
      (.tagged .int [("unit", 1)])
    ∧
    HasTypeAtGroupedTaggedBoundary taggedVarIntEnv (.var "t")
      (.tagged .int [("unit", 1)]) := by
  refine ⟨
    hasType_ascription_grouped_inner_mismatch_rejected,
    hasType_ascription_grouped_from_int_rejected,
    hasType_ascription_grouped_accepts,
    hasType_ascription_tagged_inner_mismatch_rejected,
    hasType_ascription_tagged_from_int_rejected,
    hasType_ascription_tagged_accepts
  ⟩

/-- Site-generalized grouped/tagged typing bridge:
    grouped/tagged bridge outcomes are preserved at all boundary-sensitive
    sites. -/
theorem grouped_tagged_typing_bridge_all_sites
    (site : GroupedTaggedBoundarySite) :
    ¬ HasTypeAtGroupedTaggedBoundaryAtSite site groupedVarBoolEnv (.var "g")
      (.groupedFrame .int ["a"])
    ∧
    ¬ HasTypeAtGroupedTaggedBoundaryAtSite site intVarEnv (.var "x")
      (.groupedFrame .int ["a"])
    ∧
    HasTypeAtGroupedTaggedBoundaryAtSite site groupedVarIntEnv (.var "g")
      (.groupedFrame .int ["a"])
    ∧
    ¬ HasTypeAtGroupedTaggedBoundaryAtSite site taggedVarBoolEnv (.var "t")
      (.tagged .int [("unit", 1)])
    ∧
    ¬ HasTypeAtGroupedTaggedBoundaryAtSite site intVarEnv (.var "x")
      (.tagged .int [("unit", 1)])
    ∧
    HasTypeAtGroupedTaggedBoundaryAtSite site taggedVarIntEnv (.var "t")
      (.tagged .int [("unit", 1)]) := by
  rcases grouped_tagged_typing_bridge_ascription with
    ⟨h_grouped_inner, h_grouped_non_wrapper, h_grouped_id,
      h_tagged_inner, h_tagged_non_wrapper, h_tagged_id⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_ascr :
        HasTypeAtGroupedTaggedBoundary groupedVarBoolEnv (.var "g")
          (.groupedFrame .int ["a"]) :=
      (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site
        groupedVarBoolEnv (.var "g") (.groupedFrame .int ["a"])).1 h
    exact h_grouped_inner h_ascr
  · intro h
    have h_ascr :
        HasTypeAtGroupedTaggedBoundary intVarEnv (.var "x")
          (.groupedFrame .int ["a"]) :=
      (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site
        intVarEnv (.var "x") (.groupedFrame .int ["a"])).1 h
    exact h_grouped_non_wrapper h_ascr
  · exact (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site
      groupedVarIntEnv (.var "g") (.groupedFrame .int ["a"])).2 h_grouped_id
  · intro h
    have h_ascr :
        HasTypeAtGroupedTaggedBoundary taggedVarBoolEnv (.var "t")
          (.tagged .int [("unit", 1)]) :=
      (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site
        taggedVarBoolEnv (.var "t") (.tagged .int [("unit", 1)])).1 h
    exact h_tagged_inner h_ascr
  · intro h
    have h_ascr :
        HasTypeAtGroupedTaggedBoundary intVarEnv (.var "x")
          (.tagged .int [("unit", 1)]) :=
      (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site
        intVarEnv (.var "x") (.tagged .int [("unit", 1)])).1 h
    exact h_tagged_non_wrapper h_ascr
  · exact (hasTypeAtGroupedTaggedBoundaryAtSite_iff_ascription site
      taggedVarIntEnv (.var "t") (.tagged .int [("unit", 1)])).2 h_tagged_id
