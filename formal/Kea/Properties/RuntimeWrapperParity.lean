/- 
  Kea.Properties.RuntimeWrapperParity - Runtime wrapper constructor parity.

  Current scope: `Dynamic`, `Task`, `Actor`, and `Arc` are modeled in `Ty`,
  propagated through core substitution/unification machinery, and covered by
  constructor-local parity lemmas.
-/

import Kea.Properties.UnifyReflexive

private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => rfl

/-- One substitution step over `Task` rewrites the inner type only. -/
theorem task_subst_step (s : Subst) (fuel : Nat) (inner : Ty) :
    applySubst s (fuel + 1) (.task inner) = .task (applySubst s fuel inner) := by
  simp [applySubst]

/-- One substitution step over `Actor` rewrites the inner type only. -/
theorem actor_subst_step (s : Subst) (fuel : Nat) (inner : Ty) :
    applySubst s (fuel + 1) (.actor inner) = .actor (applySubst s fuel inner) := by
  simp [applySubst]

/-- One substitution step over `Arc` rewrites the inner type only. -/
theorem arc_subst_step (s : Subst) (fuel : Nat) (inner : Ty) :
    applySubst s (fuel + 1) (.arc inner) = .arc (applySubst s fuel inner) := by
  simp [applySubst]

/-- On normalized task forms, failed constructor BEq short-circuit reduces
    unification to inner-type unification. -/
theorem task_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 inner1' inner2' : Ty)
    (hleft : applySubst st.subst fuel (.task inner1) = .task inner1')
    (hright : applySubst st.subst fuel (.task inner2) = .task inner2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.task inner1) ==
        applySubst st.subst fuel (.task inner2)) = false) :
    unify st (fuel + 1) (.task inner1) (.task inner2) = unify st fuel inner1' inner2' := by
  have h_ctor_neq' : (Ty.task inner1' == Ty.task inner2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq']

/-- On normalized actor forms, failed constructor BEq short-circuit reduces
    unification to inner-type unification. -/
theorem actor_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 inner1' inner2' : Ty)
    (hleft : applySubst st.subst fuel (.actor inner1) = .actor inner1')
    (hright : applySubst st.subst fuel (.actor inner2) = .actor inner2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.actor inner1) ==
        applySubst st.subst fuel (.actor inner2)) = false) :
    unify st (fuel + 1) (.actor inner1) (.actor inner2) = unify st fuel inner1' inner2' := by
  have h_ctor_neq' : (Ty.actor inner1' == Ty.actor inner2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq']

/-- On normalized arc forms, failed constructor BEq short-circuit reduces
    unification to inner-type unification. -/
theorem arc_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (inner1 inner2 inner1' inner2' : Ty)
    (hleft : applySubst st.subst fuel (.arc inner1) = .arc inner1')
    (hright : applySubst st.subst fuel (.arc inner2) = .arc inner2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.arc inner1) ==
        applySubst st.subst fuel (.arc inner2)) = false) :
    unify st (fuel + 1) (.arc inner1) (.arc inner2) = unify st fuel inner1' inner2' := by
  have h_ctor_neq' : (Ty.arc inner1' == Ty.arc inner2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq']

/-- At any outer successor+1 fuel, normalized task-inner errors propagate
    through task unification unchanged. -/
theorem task_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat) (inner1 inner2 : Ty) (e : String)
    (hbeq :
      (Ty.task (applySubst st.subst fuel inner1) ==
        Ty.task (applySubst st.subst fuel inner2)) = false)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .err e) :
    unify st (fuel + 2) (.task inner1) (.task inner2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.task inner1) =
        .task (applySubst st.subst fuel inner1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.task inner2) =
        .task (applySubst st.subst fuel inner2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.task inner1) ==
        applySubst st.subst (fuel + 1) (.task inner2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.task inner1) (.task inner2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel inner1)
          (applySubst st.subst fuel inner2) := by
    exact task_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      hleft hright h_ctor_neq
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized task-inner success propagates
    through task unification with the same resulting state. -/
theorem task_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat) (inner1 inner2 : Ty)
    (hbeq :
      (Ty.task (applySubst st.subst fuel inner1) ==
        Ty.task (applySubst st.subst fuel inner2)) = false)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .ok st') :
    unify st (fuel + 2) (.task inner1) (.task inner2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.task inner1) =
        .task (applySubst st.subst fuel inner1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.task inner2) =
        .task (applySubst st.subst fuel inner2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.task inner1) ==
        applySubst st.subst (fuel + 1) (.task inner2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.task inner1) (.task inner2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel inner1)
          (applySubst st.subst fuel inner2) := by
    exact task_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      hleft hright h_ctor_neq
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized actor-inner errors propagate
    through actor unification unchanged. -/
theorem actor_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat) (inner1 inner2 : Ty) (e : String)
    (hbeq :
      (Ty.actor (applySubst st.subst fuel inner1) ==
        Ty.actor (applySubst st.subst fuel inner2)) = false)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .err e) :
    unify st (fuel + 2) (.actor inner1) (.actor inner2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.actor inner1) =
        .actor (applySubst st.subst fuel inner1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.actor inner2) =
        .actor (applySubst st.subst fuel inner2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.actor inner1) ==
        applySubst st.subst (fuel + 1) (.actor inner2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.actor inner1) (.actor inner2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel inner1)
          (applySubst st.subst fuel inner2) := by
    exact actor_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      hleft hright h_ctor_neq
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized actor-inner success propagates
    through actor unification with the same resulting state. -/
theorem actor_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat) (inner1 inner2 : Ty)
    (hbeq :
      (Ty.actor (applySubst st.subst fuel inner1) ==
        Ty.actor (applySubst st.subst fuel inner2)) = false)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .ok st') :
    unify st (fuel + 2) (.actor inner1) (.actor inner2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.actor inner1) =
        .actor (applySubst st.subst fuel inner1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.actor inner2) =
        .actor (applySubst st.subst fuel inner2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.actor inner1) ==
        applySubst st.subst (fuel + 1) (.actor inner2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.actor inner1) (.actor inner2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel inner1)
          (applySubst st.subst fuel inner2) := by
    exact actor_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      hleft hright h_ctor_neq
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized arc-inner errors propagate
    through arc unification unchanged. -/
theorem arc_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat) (inner1 inner2 : Ty) (e : String)
    (hbeq :
      (Ty.arc (applySubst st.subst fuel inner1) ==
        Ty.arc (applySubst st.subst fuel inner2)) = false)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .err e) :
    unify st (fuel + 2) (.arc inner1) (.arc inner2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.arc inner1) =
        .arc (applySubst st.subst fuel inner1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.arc inner2) =
        .arc (applySubst st.subst fuel inner2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.arc inner1) ==
        applySubst st.subst (fuel + 1) (.arc inner2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.arc inner1) (.arc inner2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel inner1)
          (applySubst st.subst fuel inner2) := by
    exact arc_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      hleft hright h_ctor_neq
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized arc-inner success propagates
    through arc unification with the same resulting state. -/
theorem arc_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat) (inner1 inner2 : Ty)
    (hbeq :
      (Ty.arc (applySubst st.subst fuel inner1) ==
        Ty.arc (applySubst st.subst fuel inner2)) = false)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel inner1)
        (applySubst st.subst fuel inner2) = .ok st') :
    unify st (fuel + 2) (.arc inner1) (.arc inner2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.arc inner1) =
        .arc (applySubst st.subst fuel inner1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.arc inner2) =
        .arc (applySubst st.subst fuel inner2) := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.arc inner1) ==
        applySubst st.subst (fuel + 1) (.arc inner2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.arc inner1) (.arc inner2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel inner1)
          (applySubst st.subst fuel inner2) := by
    exact arc_unify_reduces_to_inner_of_normalized st (fuel + 1)
      inner1 inner2
      (applySubst st.subst fuel inner1)
      (applySubst st.subst fuel inner2)
      hleft hright h_ctor_neq
  rw [h_reduce]
  exact h_inner

/-- `Task` unifies with itself. -/
theorem task_unifies_with_self (st : UnifyState) (fuel : Nat) (inner : Ty) :
    unify st (fuel + 1) (.task inner) (.task inner) = .ok st := by
  simpa using (unifyReflexive' st fuel (.task inner))

/-- `Actor` unifies with itself. -/
theorem actor_unifies_with_self (st : UnifyState) (fuel : Nat) (inner : Ty) :
    unify st (fuel + 1) (.actor inner) (.actor inner) = .ok st := by
  simpa using (unifyReflexive' st fuel (.actor inner))

/-- `Arc` unifies with itself. -/
theorem arc_unifies_with_self (st : UnifyState) (fuel : Nat) (inner : Ty) :
    unify st (fuel + 1) (.arc inner) (.arc inner) = .ok st := by
  simpa using (unifyReflexive' st fuel (.arc inner))

/-- `Dynamic` unifies with concrete value types. -/
theorem dynamic_unifies_with_int (st : UnifyState) :
    unify st 1 .dynamic .int = .ok st := by
  simp [unify, applySubstCompat, applySubst]

/-- `Dynamic` also unifies in the opposite direction. -/
theorem int_unifies_with_dynamic (st : UnifyState) :
    unify st 1 .int .dynamic = .ok st := by
  simp [unify, applySubstCompat, applySubst]

/-- `Dynamic` unifies with `Int` at any successor fuel. -/
theorem dynamic_unifies_with_int_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .dynamic .int = .ok st := by
  cases fuel with
  | zero =>
      simp [unify, applySubstCompat, applySubst]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst]

/-- `Int` unifies with `Dynamic` at any successor fuel. -/
theorem int_unifies_with_dynamic_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .int .dynamic = .ok st := by
  cases fuel with
  | zero =>
      simp [unify, applySubstCompat, applySubst]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst]

/-- `Dynamic` unifies with `Task(Int)` at any successor fuel. -/
theorem dynamic_unifies_with_task_int_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .dynamic (.task .int) = .ok st := by
  cases fuel with
  | zero =>
      simp [unify, applySubstCompat, applySubst]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      have h_task : applySubst st.subst (fuel' + 1) (.task .int) = .task .int := by
        simp [applySubst, h_int]
      unfold unify
      simp [applySubstCompat, applySubst, h_int]

/-- `Task(Int)` unifies with `Dynamic` at any successor fuel. -/
theorem task_int_unifies_with_dynamic_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) (.task .int) .dynamic = .ok st := by
  cases fuel with
  | zero =>
      simp [unify, applySubstCompat, applySubst]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      have h_task : applySubst st.subst (fuel' + 1) (.task .int) = .task .int := by
        simp [applySubst, h_int]
      unfold unify
      simp [applySubstCompat, applySubst, h_int]

/-- Under normalized right-side var shape, `Dynamic` unification takes the
    var-binding path (before the permissive Dynamic branch). -/
theorem dynamic_unify_var_right_of_normalized
    (st : UnifyState) (fuel : Nat) (rhs : Ty) (v : TypeVarId)
    (hvar : applySubst st.subst fuel rhs = .var v) :
    unify st (fuel + 1) .dynamic rhs = bindTypeVar st v .dynamic fuel := by
  have hdyn : applySubst st.subst fuel .dynamic = .dynamic := by
    cases fuel <;> simp [applySubst]
  have h_beq_false : (Ty.dynamic == Ty.var v) = false := by
    simp [BEq.beq, beqTy]
  unfold unify
  simp [applySubstCompat, hdyn, hvar, h_beq_false]

/-- Under normalized left-side var shape, unifying with `Dynamic` takes the
    var-binding path (before the permissive Dynamic branch). -/
theorem dynamic_unify_var_left_of_normalized
    (st : UnifyState) (fuel : Nat) (lhs : Ty) (v : TypeVarId)
    (hvar : applySubst st.subst fuel lhs = .var v) :
    unify st (fuel + 1) lhs .dynamic = bindTypeVar st v .dynamic fuel := by
  have hdyn : applySubst st.subst fuel .dynamic = .dynamic := by
    cases fuel <;> simp [applySubst]
  have h_beq_false : (Ty.var v == Ty.dynamic) = false := by
    simp [BEq.beq, beqTy]
  unfold unify
  simp [applySubstCompat, hvar, hdyn, h_beq_false]

/-- Function return annotations can be absorbed by `Dynamic` under unification. -/
theorem dynamic_return_annotation_absorbs (st : UnifyState) :
    unify st 2
      (.function .nil .int)
      (.function .nil .dynamic)
      = .ok st := by
  unfold unify
  have h_fn_false :
      (Ty.function .nil .int == Ty.function .nil .dynamic) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_unify_nil : unifyTyList st 1 .nil .nil = .ok st := by
    simp [unifyTyList]
  have h_dyn : unify st 1 .int .dynamic = .ok st := by
    simp [unify, applySubstCompat, applySubst]
  simp [applySubstCompat, applySubst, applySubstTyList, h_fn_false, h_unify_nil, h_dyn]

/-- Dynamic return absorption also holds through a Dynamic parameter function path. -/
theorem dynamic_return_annotation_absorbs_with_dynamic_param (st : UnifyState) :
    unify st 3
      (.function (.cons .dynamic .nil) .int)
      (.function (.cons .dynamic .nil) .dynamic)
      = .ok st := by
  unfold unify
  have h_params :
      applySubstTyList st.subst 1 (.cons .dynamic .nil) = (.cons .dynamic .nil) := by
    simp [applySubstTyList, applySubst]
  have h_fn_false :
      (Ty.function (.cons .dynamic .nil) .int ==
        Ty.function (.cons .dynamic .nil) .dynamic) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_unify_params :
      unifyTyList st 2 (.cons .dynamic .nil) (.cons .dynamic .nil) = .ok st := by
    simp [unifyTyList, unify, applySubstCompat, applySubst]
  have h_dyn : unify st 2 .int .dynamic = .ok st := by
    simp [unify, applySubstCompat, applySubst]
  simp [applySubstCompat, applySubst, applySubstTyList, h_fn_false, h_unify_params, h_dyn]

/-- Dynamic return absorption also holds for non-Int concrete returns. -/
theorem dynamic_return_annotation_absorbs_bool (st : UnifyState) :
    unify st 2
      (.function .nil .bool)
      (.function .nil .dynamic)
      = .ok st := by
  unfold unify
  have h_fn_false :
      (Ty.function .nil .bool == Ty.function .nil .dynamic) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_unify_nil : unifyTyList st 1 .nil .nil = .ok st := by
    simp [unifyTyList]
  have h_dyn : unify st 1 .bool .dynamic = .ok st := by
    simp [unify, applySubstCompat, applySubst]
  simp [applySubstCompat, applySubst, applySubstTyList, h_fn_false, h_unify_nil, h_dyn]

/-- Return absorption is symmetric when Dynamic appears on the return side. -/
theorem dynamic_return_annotation_absorbs_reverse (st : UnifyState) :
    unify st 2
      (.function .nil .dynamic)
      (.function .nil .int)
      = .ok st := by
  unfold unify
  have h_fn_false :
      (Ty.function .nil .dynamic == Ty.function .nil .int) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_unify_nil : unifyTyList st 1 .nil .nil = .ok st := by
    simp [unifyTyList]
  have h_dyn : unify st 1 .dynamic .int = .ok st := by
    simp [unify, applySubstCompat, applySubst]
  simp [applySubstCompat, applySubst, applySubstTyList, h_fn_false, h_unify_nil, h_dyn]

/-- Dynamic return absorption also holds when the concrete return is `Task(Int)`. -/
theorem dynamic_return_annotation_absorbs_task (st : UnifyState) :
    unify st 2
      (.function .nil (.task .int))
      (.function .nil .dynamic)
      = .ok st := by
  unfold unify
  have h_fn_false :
      (Ty.function .nil (.task .int) == Ty.function .nil .dynamic) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_unify_nil : unifyTyList st 1 .nil .nil = .ok st := by
    simp [unifyTyList]
  have h_dyn : unify st 1 (.task .int) .dynamic = .ok st := by
    simp [unify, applySubstCompat, applySubst]
  simp [applySubstCompat, applySubst, applySubstTyList, h_fn_false, h_unify_nil, h_dyn]

/-- Return absorption is symmetric for `Dynamic` vs `Task(Int)`. -/
theorem dynamic_return_annotation_absorbs_task_reverse (st : UnifyState) :
    unify st 2
      (.function .nil .dynamic)
      (.function .nil (.task .int))
      = .ok st := by
  unfold unify
  have h_fn_false :
      (Ty.function .nil .dynamic == Ty.function .nil (.task .int)) = false := by
    simp [BEq.beq, beqTy, beqTyList]
  have h_unify_nil : unifyTyList st 1 .nil .nil = .ok st := by
    simp [unifyTyList]
  have h_dyn : unify st 1 .dynamic (.task .int) = .ok st := by
    simp [unify, applySubstCompat, applySubst]
  simp [applySubstCompat, applySubst, applySubstTyList, h_fn_false, h_unify_nil, h_dyn]

/-- Boundary-sensitive type-check sites for Dynamic narrowing/widening checks. -/
inductive DynamicBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Explicit Dynamic-boundary policy model:
    - concrete -> Dynamic widening is allowed
    - Dynamic -> concrete narrowing is rejected
    - all other non-Dynamic pairs are allowed by this boundary layer
      (left to unification/other checks). -/
def dynamicBoundaryAllowsAtSite
    (_site : DynamicBoundarySite) (expected actual : Ty) : Bool :=
  match expected, actual with
  | .dynamic, _ => true
  | _, .dynamic => false
  | _, _ => true

/-- Dynamic boundary policy is currently site-invariant:
    all boundary-sensitive sites use the same allow/reject predicate. -/
theorem dynamic_boundary_policy_site_invariant
    (site1 site2 : DynamicBoundarySite) (expected actual : Ty) :
    dynamicBoundaryAllowsAtSite site1 expected actual =
      dynamicBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Dynamic narrowing to Int is rejected at every boundary-sensitive site. -/
theorem dynamic_boundary_rejects_int_from_dynamic_all_sites
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .int .dynamic = false := by
  cases site <;> rfl

/-- Dynamic narrowing to `Task(Int)` is rejected at every boundary-sensitive site. -/
theorem dynamic_boundary_rejects_task_int_from_dynamic_all_sites
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site (.task .int) .dynamic = false := by
  cases site <;> rfl

/-- Concrete-to-Dynamic widening remains allowed at every boundary-sensitive site. -/
theorem dynamic_boundary_allows_dynamic_from_int_all_sites
    (site : DynamicBoundarySite) :
    dynamicBoundaryAllowsAtSite site .dynamic .int = true := by
  cases site <;> rfl

/-- General Dynamic widening law:
    for any actual type, `actual -> Dynamic` is allowed at every
    boundary-sensitive site. -/
theorem dynamic_boundary_allows_dynamic_from_any_all_sites
    (site : DynamicBoundarySite) (actual : Ty) :
    dynamicBoundaryAllowsAtSite site .dynamic actual = true := by
  cases site <;> rfl

/-- General Dynamic narrowing law:
    for any non-Dynamic expected type, Dynamic->expected is rejected at every
    boundary-sensitive site. -/
theorem dynamic_boundary_rejects_from_dynamic_all_sites
    (site : DynamicBoundarySite) (expected : Ty)
    (h_expected : expected ≠ .dynamic) :
    dynamicBoundaryAllowsAtSite site expected .dynamic = false := by
  cases site <;> cases expected <;> simp [dynamicBoundaryAllowsAtSite] at *

/-- Boundary policy closure witness:
    function-return unification can still absorb Int/Dynamic at the unifier
    level, while the explicit return-boundary policy rejects Dynamic->Int
    narrowing. -/
theorem dynamic_return_boundary_closes_unifier_absorption
    (st : UnifyState) :
    unify st 2
      (.function .nil .int)
      (.function .nil .dynamic)
      = .ok st ∧
    dynamicBoundaryAllowsAtSite .returnAnnotation .int .dynamic = false := by
  exact ⟨dynamic_return_annotation_absorbs st, rfl⟩

/-- Boundary policy closure witness at all sites:
    return-shape unifier absorption (`Int` vs `Dynamic`) can hold while every
    boundary-sensitive site still rejects Dynamic->Int narrowing. -/
theorem dynamic_boundary_closes_unifier_absorption_all_sites
    (st : UnifyState) (site : DynamicBoundarySite) :
    unify st 2
      (.function .nil .int)
      (.function .nil .dynamic)
      = .ok st ∧
    dynamicBoundaryAllowsAtSite site .int .dynamic = false := by
  exact ⟨dynamic_return_annotation_absorbs st,
    dynamic_boundary_rejects_int_from_dynamic_all_sites site⟩

/-- Boundary policy closure witness at all sites for wrapped returns:
    return-shape unifier absorption (`Task(Int)` vs `Dynamic`) can hold while
    every boundary-sensitive site rejects Dynamic->Task(Int) narrowing. -/
theorem dynamic_boundary_closes_unifier_absorption_task_all_sites
    (st : UnifyState) (site : DynamicBoundarySite) :
    unify st 2
      (.function .nil (.task .int))
      (.function .nil .dynamic)
      = .ok st ∧
    dynamicBoundaryAllowsAtSite site (.task .int) .dynamic = false := by
  exact ⟨dynamic_return_annotation_absorbs_task st,
    dynamic_boundary_rejects_task_int_from_dynamic_all_sites site⟩

/-- Boundary policy closure witness at all sites for non-Int concrete returns:
    return-shape unifier absorption (`Bool` vs `Dynamic`) can hold while every
    boundary-sensitive site rejects Dynamic->Bool narrowing. -/
theorem dynamic_boundary_closes_unifier_absorption_bool_all_sites
    (st : UnifyState) (site : DynamicBoundarySite) :
    unify st 2
      (.function .nil .bool)
      (.function .nil .dynamic)
      = .ok st ∧
    dynamicBoundaryAllowsAtSite site .bool .dynamic = false := by
  exact ⟨dynamic_return_annotation_absorbs_bool st,
    dynamic_boundary_rejects_from_dynamic_all_sites site .bool
      (by
        intro h
        cases h)⟩

/-- Boundary widening witness at all sites:
    return-shape unifier absorption (`Dynamic` vs `Int`) aligns with policy
    acceptance of concrete->Dynamic widening. -/
theorem dynamic_boundary_allows_unifier_widening_int_all_sites
    (st : UnifyState) (site : DynamicBoundarySite) :
    unify st 2
      (.function .nil .dynamic)
      (.function .nil .int)
      = .ok st ∧
    dynamicBoundaryAllowsAtSite site .dynamic .int = true := by
  exact ⟨dynamic_return_annotation_absorbs_reverse st,
    dynamic_boundary_allows_dynamic_from_int_all_sites site⟩

/-- Boundary widening witness at all sites for wrapped returns:
    return-shape unifier absorption (`Dynamic` vs `Task(Int)`) aligns with
    policy acceptance of concrete->Dynamic widening. -/
theorem dynamic_boundary_allows_unifier_widening_task_all_sites
    (st : UnifyState) (site : DynamicBoundarySite) :
    unify st 2
      (.function .nil .dynamic)
      (.function .nil (.task .int))
      = .ok st ∧
    dynamicBoundaryAllowsAtSite site .dynamic (.task .int) = true := by
  exact ⟨dynamic_return_annotation_absorbs_task_reverse st,
    dynamic_boundary_allows_dynamic_from_any_all_sites site (.task .int)⟩

/-- Packaged Dynamic boundary surface slice:
    site-level narrowing/widening policy outcomes together with concrete
    unifier absorption/widening witnesses for `Int`, `Bool`, and `Task(Int)`. -/
theorem dynamic_boundary_surface_slice
    (st : UnifyState) (site : DynamicBoundarySite) :
    (dynamicBoundaryAllowsAtSite site .int .dynamic = false)
    ∧
    (dynamicBoundaryAllowsAtSite site (.task .int) .dynamic = false)
    ∧
    (dynamicBoundaryAllowsAtSite site .bool .dynamic = false)
    ∧
    (dynamicBoundaryAllowsAtSite site .dynamic .int = true)
    ∧
    (dynamicBoundaryAllowsAtSite site .dynamic (.task .int) = true)
    ∧
    (unify st 2
      (.function .nil .int)
      (.function .nil .dynamic)
      = .ok st)
    ∧
    (unify st 2
      (.function .nil .bool)
      (.function .nil .dynamic)
      = .ok st)
    ∧
    (unify st 2
      (.function .nil (.task .int))
      (.function .nil .dynamic)
      = .ok st)
    ∧
    (unify st 2
      (.function .nil .dynamic)
      (.function .nil .int)
      = .ok st)
    ∧
    (unify st 2
      (.function .nil .dynamic)
      (.function .nil (.task .int))
      = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dynamic_boundary_rejects_int_from_dynamic_all_sites site
  · exact dynamic_boundary_rejects_task_int_from_dynamic_all_sites site
  · exact dynamic_boundary_rejects_from_dynamic_all_sites site .bool (by
      intro h
      cases h)
  · exact dynamic_boundary_allows_dynamic_from_int_all_sites site
  · exact dynamic_boundary_allows_dynamic_from_any_all_sites site (.task .int)
  · exact dynamic_return_annotation_absorbs st
  · exact dynamic_return_annotation_absorbs_bool st
  · exact dynamic_return_annotation_absorbs_task st
  · exact dynamic_return_annotation_absorbs_reverse st
  · exact dynamic_return_annotation_absorbs_task_reverse st

/-- `Task` inner-type mismatch rejects unification. -/
theorem task_inner_mismatch (st : UnifyState) :
    unify st 2 (.task .int) (.task .bool) = .err "type mismatch" := by
  have h_inner_neq : (Ty.int == Ty.bool) = false := by
    native_decide
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    unfold unify
    simp [applySubstCompat, applySubst, h_inner_neq]
  have h_neq : (Ty.task .int == Ty.task .bool) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- `Actor` inner-type mismatch rejects unification. -/
theorem actor_inner_mismatch (st : UnifyState) :
    unify st 2 (.actor .int) (.actor .bool) = .err "type mismatch" := by
  have h_inner_neq : (Ty.int == Ty.bool) = false := by
    native_decide
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    unfold unify
    simp [applySubstCompat, applySubst, h_inner_neq]
  have h_neq : (Ty.actor .int == Ty.actor .bool) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- `Arc` inner-type mismatch rejects unification. -/
theorem arc_inner_mismatch (st : UnifyState) :
    unify st 2 (.arc .int) (.arc .bool) = .err "type mismatch" := by
  have h_inner_neq : (Ty.int == Ty.bool) = false := by
    native_decide
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    unfold unify
    simp [applySubstCompat, applySubst, h_inner_neq]
  have h_neq : (Ty.arc .int == Ty.arc .bool) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- Wrapper and non-wrapper types do not unify in wrapper-expected positions. -/
theorem task_non_task_mismatch (st : UnifyState) :
    unify st 1 (.task .int) .int = .err "type mismatch" := by
  have h_neq : (Ty.task .int == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq]

/-- Boundary-sensitive sites where wrapper shape checks are enforced. -/
inductive WrapperBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level wrapper boundary policy for Task/Actor/Arc constructors.
    Current scope:
    - inner types must match when wrapper constructors match
    - non-wrapper actuals are rejected when wrapper constructors are expected
    - otherwise allowed (outside this boundary surface) -/
def wrapperBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .task e, .task a => e == a
  | .task _, _ => false
  | .actor e, .actor a => e == a
  | .actor _, _ => false
  | .arc e, .arc a => e == a
  | .arc _, _ => false
  | _, _ => true

/-- Site-level wrapper for Task/Actor/Arc boundary checks. -/
def wrapperBoundaryAllowsAtSite
    (_site : WrapperBoundarySite) (expected actual : Ty) : Bool :=
  wrapperBoundaryAllows expected actual

/-- Wrapper boundary policy is currently site-invariant. -/
theorem wrapper_boundary_policy_site_invariant
    (site1 site2 : WrapperBoundarySite) (expected actual : Ty) :
    wrapperBoundaryAllowsAtSite site1 expected actual =
      wrapperBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Task inner mismatch is rejected by wrapper boundary policy. -/
theorem wrapper_boundary_rejects_task_inner_mismatch :
    wrapperBoundaryAllows (.task .int) (.task .bool) = false := by
  native_decide

/-- Actor inner mismatch is rejected by wrapper boundary policy. -/
theorem wrapper_boundary_rejects_actor_inner_mismatch :
    wrapperBoundaryAllows (.actor .int) (.actor .bool) = false := by
  native_decide

/-- Arc inner mismatch is rejected by wrapper boundary policy. -/
theorem wrapper_boundary_rejects_arc_inner_mismatch :
    wrapperBoundaryAllows (.arc .int) (.arc .bool) = false := by
  native_decide

/-- Non-wrapper actuals are rejected when wrapper constructors are expected. -/
theorem wrapper_boundary_rejects_non_wrapper_actual :
    wrapperBoundaryAllows (.task .int) .int = false := by
  native_decide

/-- Packaged wrapper boundary surface slice:
    site invariance + wrapper-inner mismatch/non-wrapper rejection, with closure
    to concrete mismatch/reflexive unifier witnesses. -/
theorem wrapper_boundary_surface_slice
    (st : UnifyState) (site : WrapperBoundarySite) :
    (wrapperBoundaryAllowsAtSite site (.task .int) (.task .bool) = false)
    ∧
    (wrapperBoundaryAllowsAtSite site (.actor .int) (.actor .bool) = false)
    ∧
    (wrapperBoundaryAllowsAtSite site (.arc .int) (.arc .bool) = false)
    ∧
    (wrapperBoundaryAllowsAtSite site (.task .int) .int = false)
    ∧
    (unify st 2 (.task .int) (.task .bool) = .err "type mismatch")
    ∧
    (unify st 2 (.actor .int) (.actor .bool) = .err "type mismatch")
    ∧
    (unify st 2 (.arc .int) (.arc .bool) = .err "type mismatch")
    ∧
    (unify st 1 (.task .int) .int = .err "type mismatch")
    ∧
    (unify st 1 (.task .int) (.task .int) = .ok st)
    ∧
    (unify st 1 (.actor .int) (.actor .int) = .ok st)
    ∧
    (unify st 1 (.arc .int) (.arc .int) = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact wrapper_boundary_rejects_task_inner_mismatch
  · cases site <;> exact wrapper_boundary_rejects_actor_inner_mismatch
  · cases site <;> exact wrapper_boundary_rejects_arc_inner_mismatch
  · cases site <;> exact wrapper_boundary_rejects_non_wrapper_actual
  · exact task_inner_mismatch st
  · exact actor_inner_mismatch st
  · exact arc_inner_mismatch st
  · exact task_non_task_mismatch st
  · exact task_unifies_with_self st 0 .int
  · exact actor_unifies_with_self st 0 .int
  · exact arc_unifies_with_self st 0 .int

/-- Wrapper free vars track the wrapped type. -/
theorem wrapper_free_vars (inner : Ty) :
    freeTypeVars (.task inner) = freeTypeVars inner /\
      freeTypeVars (.actor inner) = freeTypeVars inner /\
      freeTypeVars (.arc inner) = freeTypeVars inner /\
      freeRowVars (.task inner) = freeRowVars inner /\
      freeRowVars (.actor inner) = freeRowVars inner /\
      freeRowVars (.arc inner) = freeRowVars inner := by
  simp [freeTypeVars, freeRowVars]

/-- `Dynamic` has no free type or row variables. -/
theorem dynamic_free_vars :
    freeTypeVars .dynamic = [] /\ freeRowVars .dynamic = [] := by
  simp [freeTypeVars, freeRowVars]
