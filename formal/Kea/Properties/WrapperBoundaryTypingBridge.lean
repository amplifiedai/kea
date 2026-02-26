import Kea.Typing
import Kea.Properties.RuntimeWrapperParity
import Kea.Properties.BoundaryAssignability

/-!
  Kea.Properties.WrapperBoundaryTypingBridge

  Language-level bridge for Task/Actor/Arc wrapper behavior at a modeled
  ascription boundary gate.
-/

/-- Modeled wrapper boundary gate at a chosen boundary site:
    expression `e` inhabits `expected` iff it has some actual type that both
    passes wrapper boundary policy and unifies with `expected`. -/
def HasTypeAtWrapperBoundaryAtSite
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtBoundary
    (allowsByBoolAndUnify
      (wrapperBoundaryAllowsAtSite site)
      UnifyState.empty
      2)
    env e expected

/-- Modeled wrapper ascription gate (site-specialized alias). -/
abbrev HasTypeAtWrapperBoundary
    (env : TermEnv) (e : CoreExpr) (expected : Ty) : Prop :=
  HasTypeAtWrapperBoundaryAtSite .ascription env e expected

/-- Wrapper typing gate is site-invariant because wrapper boundary policy is
    currently site-invariant. -/
theorem hasTypeAtWrapperBoundaryAtSite_iff_ascription
    (site : WrapperBoundarySite)
    (env : TermEnv) (e : CoreExpr) (expected : Ty) :
    HasTypeAtWrapperBoundaryAtSite site env e expected
      ↔ HasTypeAtWrapperBoundary env e expected := by
  refine hasTypeAtBoundary_congr
    (allowsByBoolAndUnify (wrapperBoundaryAllowsAtSite site) UnifyState.empty 2)
    (allowsByBoolAndUnify (wrapperBoundaryAllowsAtSite .ascription) UnifyState.empty 2)
    env e expected ?_
  intro exp act
  have h_site :
      wrapperBoundaryAllowsAtSite site exp act
        = wrapperBoundaryAllowsAtSite .ascription exp act :=
    wrapper_boundary_policy_site_invariant site .ascription exp act
  unfold allowsByBoolAndUnify
  simp [h_site]

abbrev wrapperTaskVarIntEnv : TermEnv := [("t", .task .int)]
abbrev wrapperTaskVarBoolEnv : TermEnv := [("t", .task .bool)]
abbrev wrapperActorVarIntEnv : TermEnv := [("a", .actor .int)]
abbrev wrapperActorVarBoolEnv : TermEnv := [("a", .actor .bool)]
abbrev wrapperArcVarIntEnv : TermEnv := [("r", .arc .int)]
abbrev wrapperArcVarBoolEnv : TermEnv := [("r", .arc .bool)]
abbrev wrapperIntVarEnv : TermEnv := [("x", .int)]

/-- `t` has the unique task-Int type in `wrapperTaskVarIntEnv`. -/
theorem hasType_var_task_int_unique
    (ty : Ty)
    (h_ty : HasType wrapperTaskVarIntEnv (.var "t") ty) :
    ty = .task .int := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperTaskVarIntEnv, TermEnv.lookup] using h_lookup.symm

/-- `t` has the unique task-Bool type in `wrapperTaskVarBoolEnv`. -/
theorem hasType_var_task_bool_unique
    (ty : Ty)
    (h_ty : HasType wrapperTaskVarBoolEnv (.var "t") ty) :
    ty = .task .bool := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperTaskVarBoolEnv, TermEnv.lookup] using h_lookup.symm

/-- `a` has the unique actor-Int type in `wrapperActorVarIntEnv`. -/
theorem hasType_var_actor_int_unique
    (ty : Ty)
    (h_ty : HasType wrapperActorVarIntEnv (.var "a") ty) :
    ty = .actor .int := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperActorVarIntEnv, TermEnv.lookup] using h_lookup.symm

/-- `a` has the unique actor-Bool type in `wrapperActorVarBoolEnv`. -/
theorem hasType_var_actor_bool_unique
    (ty : Ty)
    (h_ty : HasType wrapperActorVarBoolEnv (.var "a") ty) :
    ty = .actor .bool := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperActorVarBoolEnv, TermEnv.lookup] using h_lookup.symm

/-- `r` has the unique arc-Int type in `wrapperArcVarIntEnv`. -/
theorem hasType_var_arc_int_unique
    (ty : Ty)
    (h_ty : HasType wrapperArcVarIntEnv (.var "r") ty) :
    ty = .arc .int := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperArcVarIntEnv, TermEnv.lookup] using h_lookup.symm

/-- `r` has the unique arc-Bool type in `wrapperArcVarBoolEnv`. -/
theorem hasType_var_arc_bool_unique
    (ty : Ty)
    (h_ty : HasType wrapperArcVarBoolEnv (.var "r") ty) :
    ty = .arc .bool := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperArcVarBoolEnv, TermEnv.lookup] using h_lookup.symm

/-- `x` has the unique bare `Int` type in `wrapperIntVarEnv`. -/
theorem hasType_var_wrapper_int_unique
    (ty : Ty)
    (h_ty : HasType wrapperIntVarEnv (.var "x") ty) :
    ty = .int := by
  cases h_ty with
  | var env name ty' h_lookup =>
      simpa [wrapperIntVarEnv, TermEnv.lookup] using h_lookup.symm

/-- Task inner mismatch is rejected by modeled ascription gate. -/
theorem hasType_ascription_task_inner_mismatch_rejected :
    ¬ HasTypeAtWrapperBoundary wrapperTaskVarBoolEnv (.var "t") (.task .int) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨_h_allow, h_unify⟩
  rcases h_unify with ⟨_, h_unify⟩
  have h_actual : actual = .task .bool :=
    hasType_var_task_bool_unique actual h_ty
  subst h_actual
  have h_err :
      unify UnifyState.empty 2 (.task .int) (.task .bool) = .err "type mismatch" :=
    task_inner_mismatch UnifyState.empty
  rw [h_err] at h_unify
  cases h_unify

/-- Task from bare Int is rejected by modeled ascription gate. -/
theorem hasType_ascription_task_from_int_rejected :
    ¬ HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.task .int) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .int := hasType_var_wrapper_int_unique actual h_ty
  subst h_actual
  have h_reject :
      wrapperBoundaryAllowsAtSite .ascription (.task .int) .int = false := by
    simpa [wrapperBoundaryAllowsAtSite] using wrapper_boundary_rejects_non_wrapper_actual
  simp [h_reject] at h_allow

/-- Task identity ascription remains accepted. -/
theorem hasType_ascription_task_accepts :
    HasTypeAtWrapperBoundary wrapperTaskVarIntEnv (.var "t") (.task .int) := by
  refine ⟨.task .int, ?_, ?_⟩
  · exact HasType.var wrapperTaskVarIntEnv "t" (.task .int) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (task_unifies_with_self UnifyState.empty 1 .int)

/-- Actor inner mismatch is rejected by modeled ascription gate. -/
theorem hasType_ascription_actor_inner_mismatch_rejected :
    ¬ HasTypeAtWrapperBoundary wrapperActorVarBoolEnv (.var "a") (.actor .int) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨_h_allow, h_unify⟩
  rcases h_unify with ⟨_, h_unify⟩
  have h_actual : actual = .actor .bool :=
    hasType_var_actor_bool_unique actual h_ty
  subst h_actual
  have h_err :
      unify UnifyState.empty 2 (.actor .int) (.actor .bool) = .err "type mismatch" :=
    actor_inner_mismatch UnifyState.empty
  rw [h_err] at h_unify
  cases h_unify

/-- Actor from bare Int is rejected by modeled ascription gate. -/
theorem hasType_ascription_actor_from_int_rejected :
    ¬ HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.actor .int) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .int := hasType_var_wrapper_int_unique actual h_ty
  subst h_actual
  have h_reject :
      wrapperBoundaryAllowsAtSite .ascription (.actor .int) .int = false := by
    native_decide
  simp [h_reject] at h_allow

/-- Actor identity ascription remains accepted. -/
theorem hasType_ascription_actor_accepts :
    HasTypeAtWrapperBoundary wrapperActorVarIntEnv (.var "a") (.actor .int) := by
  refine ⟨.actor .int, ?_, ?_⟩
  · exact HasType.var wrapperActorVarIntEnv "a" (.actor .int) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (actor_unifies_with_self UnifyState.empty 1 .int)

/-- Arc inner mismatch is rejected by modeled ascription gate. -/
theorem hasType_ascription_arc_inner_mismatch_rejected :
    ¬ HasTypeAtWrapperBoundary wrapperArcVarBoolEnv (.var "r") (.arc .int) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨_h_allow, h_unify⟩
  rcases h_unify with ⟨_, h_unify⟩
  have h_actual : actual = .arc .bool :=
    hasType_var_arc_bool_unique actual h_ty
  subst h_actual
  have h_err :
      unify UnifyState.empty 2 (.arc .int) (.arc .bool) = .err "type mismatch" :=
    arc_inner_mismatch UnifyState.empty
  rw [h_err] at h_unify
  cases h_unify

/-- Arc from bare Int is rejected by modeled ascription gate. -/
theorem hasType_ascription_arc_from_int_rejected :
    ¬ HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.arc .int) := by
  intro h
  rcases h with ⟨actual, h_ty, h_rel⟩
  rcases h_rel with ⟨h_allow, _h_unify⟩
  have h_actual : actual = .int := hasType_var_wrapper_int_unique actual h_ty
  subst h_actual
  have h_reject :
      wrapperBoundaryAllowsAtSite .ascription (.arc .int) .int = false := by
    native_decide
  simp [h_reject] at h_allow

/-- Arc identity ascription remains accepted. -/
theorem hasType_ascription_arc_accepts :
    HasTypeAtWrapperBoundary wrapperArcVarIntEnv (.var "r") (.arc .int) := by
  refine ⟨.arc .int, ?_, ?_⟩
  · exact HasType.var wrapperArcVarIntEnv "r" (.arc .int) (by
      simp [TermEnv.lookup])
  · refine ⟨?_, ?_⟩
    · native_decide
    · refine ⟨UnifyState.empty, ?_⟩
      simpa using (arc_unifies_with_self UnifyState.empty 1 .int)

/-- Packaged wrapper typing bridge at modeled ascription boundary:
    wrapper inner mismatch and non-wrapper rejection hold, while Task/Actor/Arc
    identity controls remain accepted. -/
theorem wrapper_typing_bridge_ascription :
    ¬ HasTypeAtWrapperBoundary wrapperTaskVarBoolEnv (.var "t") (.task .int)
    ∧
    ¬ HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.task .int)
    ∧
    HasTypeAtWrapperBoundary wrapperTaskVarIntEnv (.var "t") (.task .int)
    ∧
    ¬ HasTypeAtWrapperBoundary wrapperActorVarBoolEnv (.var "a") (.actor .int)
    ∧
    ¬ HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.actor .int)
    ∧
    HasTypeAtWrapperBoundary wrapperActorVarIntEnv (.var "a") (.actor .int)
    ∧
    ¬ HasTypeAtWrapperBoundary wrapperArcVarBoolEnv (.var "r") (.arc .int)
    ∧
    ¬ HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.arc .int)
    ∧
    HasTypeAtWrapperBoundary wrapperArcVarIntEnv (.var "r") (.arc .int) := by
  refine ⟨
    hasType_ascription_task_inner_mismatch_rejected,
    hasType_ascription_task_from_int_rejected,
    hasType_ascription_task_accepts,
    hasType_ascription_actor_inner_mismatch_rejected,
    hasType_ascription_actor_from_int_rejected,
    hasType_ascription_actor_accepts,
    hasType_ascription_arc_inner_mismatch_rejected,
    hasType_ascription_arc_from_int_rejected,
    hasType_ascription_arc_accepts
  ⟩

/-- Site-generalized wrapper typing bridge:
    wrapper bridge outcomes are preserved at all boundary-sensitive sites. -/
theorem wrapper_typing_bridge_all_sites
    (site : WrapperBoundarySite) :
    ¬ HasTypeAtWrapperBoundaryAtSite site wrapperTaskVarBoolEnv (.var "t") (.task .int)
    ∧
    ¬ HasTypeAtWrapperBoundaryAtSite site wrapperIntVarEnv (.var "x") (.task .int)
    ∧
    HasTypeAtWrapperBoundaryAtSite site wrapperTaskVarIntEnv (.var "t") (.task .int)
    ∧
    ¬ HasTypeAtWrapperBoundaryAtSite site wrapperActorVarBoolEnv (.var "a") (.actor .int)
    ∧
    ¬ HasTypeAtWrapperBoundaryAtSite site wrapperIntVarEnv (.var "x") (.actor .int)
    ∧
    HasTypeAtWrapperBoundaryAtSite site wrapperActorVarIntEnv (.var "a") (.actor .int)
    ∧
    ¬ HasTypeAtWrapperBoundaryAtSite site wrapperArcVarBoolEnv (.var "r") (.arc .int)
    ∧
    ¬ HasTypeAtWrapperBoundaryAtSite site wrapperIntVarEnv (.var "x") (.arc .int)
    ∧
    HasTypeAtWrapperBoundaryAtSite site wrapperArcVarIntEnv (.var "r") (.arc .int) := by
  rcases wrapper_typing_bridge_ascription with
    ⟨h_task_inner, h_task_non_wrapper, h_task_id,
      h_actor_inner, h_actor_non_wrapper, h_actor_id,
      h_arc_inner, h_arc_non_wrapper, h_arc_id⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_ascr :
        HasTypeAtWrapperBoundary wrapperTaskVarBoolEnv (.var "t") (.task .int) :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
        wrapperTaskVarBoolEnv (.var "t") (.task .int)).1 h
    exact h_task_inner h_ascr
  · intro h
    have h_ascr :
        HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.task .int) :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
        wrapperIntVarEnv (.var "x") (.task .int)).1 h
    exact h_task_non_wrapper h_ascr
  · exact (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
      wrapperTaskVarIntEnv (.var "t") (.task .int)).2 h_task_id
  · intro h
    have h_ascr :
        HasTypeAtWrapperBoundary wrapperActorVarBoolEnv (.var "a") (.actor .int) :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
        wrapperActorVarBoolEnv (.var "a") (.actor .int)).1 h
    exact h_actor_inner h_ascr
  · intro h
    have h_ascr :
        HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.actor .int) :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
        wrapperIntVarEnv (.var "x") (.actor .int)).1 h
    exact h_actor_non_wrapper h_ascr
  · exact (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
      wrapperActorVarIntEnv (.var "a") (.actor .int)).2 h_actor_id
  · intro h
    have h_ascr :
        HasTypeAtWrapperBoundary wrapperArcVarBoolEnv (.var "r") (.arc .int) :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
        wrapperArcVarBoolEnv (.var "r") (.arc .int)).1 h
    exact h_arc_inner h_ascr
  · intro h
    have h_ascr :
        HasTypeAtWrapperBoundary wrapperIntVarEnv (.var "x") (.arc .int) :=
      (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
        wrapperIntVarEnv (.var "x") (.arc .int)).1 h
    exact h_arc_non_wrapper h_ascr
  · exact (hasTypeAtWrapperBoundaryAtSite_iff_ascription site
      wrapperArcVarIntEnv (.var "r") (.arc .int)).2 h_arc_id
