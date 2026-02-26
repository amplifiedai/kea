/- 
  Kea.Properties.ExistentialParity - Existential constructor parity slice.

  Current scope: simplified existential constructor (`bounds`, associated-type
  list) is modeled in `Ty`, propagated through substitution/unification, and
  covered by constructor-local parity lemmas.
-/

import Kea.Properties.UnifyReflexive

private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => rfl

private theorem applySubst_bool (s : Subst) : ∀ fuel, applySubst s fuel .bool = .bool
  | 0 => rfl
  | _ + 1 => rfl

private theorem applySubstTyList_nil (s : Subst) : ∀ fuel, applySubstTyList s fuel .nil = .nil
  | 0 => rfl
  | _ + 1 => rfl

private theorem applySubstTyList_int_singleton (s : Subst) :
    ∀ fuel, applySubstTyList s fuel (.cons .int .nil) = (.cons .int .nil)
  | 0 => rfl
  | fuel + 1 => by
    simp [applySubstTyList, applySubst_int s fuel, applySubstTyList_nil s fuel]

private theorem applySubstTyList_bool_singleton (s : Subst) :
    ∀ fuel, applySubstTyList s fuel (.cons .bool .nil) = (.cons .bool .nil)
  | 0 => rfl
  | fuel + 1 => by
    simp [applySubstTyList, applySubst_bool s fuel, applySubstTyList_nil s fuel]

private theorem applySubstTyList_int_bool_pair (s : Subst) :
    ∀ fuel, applySubstTyList s fuel (.cons .int (.cons .bool .nil)) =
      (.cons .int (.cons .bool .nil))
  | 0 => rfl
  | fuel + 1 => by
    simp [applySubstTyList, applySubst_int s fuel, applySubstTyList_bool_singleton s fuel]

/-- One substitution step over `Existential` rewrites associated types only. -/
theorem existential_subst_step
    (s : Subst) (fuel : Nat) (bounds : List String) (assoc : TyList) :
    applySubst s (fuel + 1) (.existential bounds assoc) =
      .existential bounds (applySubstTyList s fuel assoc) := by
  simp [applySubst]

/-- `Existential` unifies with itself. -/
theorem existential_unifies_with_self
    (st : UnifyState) (fuel : Nat) (bounds : List String) (assoc : TyList) :
    unify st (fuel + 1) (.existential bounds assoc) (.existential bounds assoc) = .ok st := by
  simpa using (unifyReflexive' st fuel (.existential bounds assoc))

/-- On normalized existential forms, failed constructor BEq short-circuit and
    equal bound sets reduce unification to associated-type-list unification. -/
theorem existential_unify_reduces_to_assoc_of_normalized
    (st : UnifyState) (fuel : Nat)
    (bounds1 bounds2 bounds1' bounds2' : List String)
    (assoc1 assoc2 assoc1' assoc2' : TyList)
    (hleft :
      applySubst st.subst fuel (.existential bounds1 assoc1) =
        .existential bounds1' assoc1')
    (hright :
      applySubst st.subst fuel (.existential bounds2 assoc2) =
        .existential bounds2' assoc2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.existential bounds1 assoc1) ==
        applySubst st.subst fuel (.existential bounds2 assoc2)) = false)
    (h_bounds : bounds1' = bounds2') :
    unify st (fuel + 1) (.existential bounds1 assoc1) (.existential bounds2 assoc2) =
      unifyTyList st fuel assoc1' assoc2' := by
  have h_ctor_neq' :
      (Ty.existential bounds1' assoc1' == Ty.existential bounds2' assoc2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  have h_ctor_neq'' :
      (Ty.existential bounds2' assoc1' == Ty.existential bounds2' assoc2') = false := by
    simpa [h_bounds] using h_ctor_neq'
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq'', h_bounds]

/-- Under normalized existential forms with equal bound sets, associated-type
    list success lifts to existential unification success (arbitrary resulting
    state). -/
theorem existential_unify_accepts_of_normalized_assoc_ok
    (st st' : UnifyState) (fuel : Nat)
    (bounds1 bounds2 bounds1' bounds2' : List String)
    (assoc1 assoc2 assoc1' assoc2' : TyList)
    (hleft :
      applySubst st.subst fuel (.existential bounds1 assoc1) =
        .existential bounds1' assoc1')
    (hright :
      applySubst st.subst fuel (.existential bounds2 assoc2) =
        .existential bounds2' assoc2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.existential bounds1 assoc1) ==
        applySubst st.subst fuel (.existential bounds2 assoc2)) = false)
    (h_bounds : bounds1' = bounds2')
    (h_assoc : unifyTyList st fuel assoc1' assoc2' = .ok st') :
    unify st (fuel + 1) (.existential bounds1 assoc1) (.existential bounds2 assoc2) =
      .ok st' := by
  rw [existential_unify_reduces_to_assoc_of_normalized st fuel
        bounds1 bounds2 bounds1' bounds2' assoc1 assoc2 assoc1' assoc2'
        hleft hright h_ctor_neq h_bounds]
  exact h_assoc

/-- Under normalized existential forms with equal bound sets, associated-type
    list rejection propagates the same error through existential unification. -/
theorem existential_unify_rejects_assoc_err_of_normalized_bounds_eq
    (st : UnifyState) (fuel : Nat)
    (bounds1 bounds2 bounds1' bounds2' : List String)
    (assoc1 assoc2 assoc1' assoc2' : TyList)
    (hleft :
      applySubst st.subst fuel (.existential bounds1 assoc1) =
        .existential bounds1' assoc1')
    (hright :
      applySubst st.subst fuel (.existential bounds2 assoc2) =
        .existential bounds2' assoc2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.existential bounds1 assoc1) ==
        applySubst st.subst fuel (.existential bounds2 assoc2)) = false)
    (h_bounds : bounds1' = bounds2')
    (e : String)
    (h_assoc : unifyTyList st fuel assoc1' assoc2' = .err e) :
    unify st (fuel + 1) (.existential bounds1 assoc1) (.existential bounds2 assoc2) =
      .err e := by
  rw [existential_unify_reduces_to_assoc_of_normalized st fuel
        bounds1 bounds2 bounds1' bounds2' assoc1 assoc2 assoc1' assoc2'
        hleft hright h_ctor_neq h_bounds]
  exact h_assoc

/-- On normalized existential forms, failed constructor BEq short-circuit and
    distinct bound sets force mismatch. -/
theorem existential_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (bounds1 bounds2 bounds1' bounds2' : List String)
    (assoc1 assoc2 assoc1' assoc2' : TyList)
    (hleft :
      applySubst st.subst fuel (.existential bounds1 assoc1) =
        .existential bounds1' assoc1')
    (hright :
      applySubst st.subst fuel (.existential bounds2 assoc2) =
        .existential bounds2' assoc2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.existential bounds1 assoc1) ==
        applySubst st.subst fuel (.existential bounds2 assoc2)) = false)
    (h_bounds : bounds1' ≠ bounds2') :
    unify st (fuel + 1) (.existential bounds1 assoc1) (.existential bounds2 assoc2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.existential bounds1' assoc1' == Ty.existential bounds2' assoc2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_bounds]

/-- Distinct bound sets reject existential unification. -/
theorem existential_bounds_mismatch (st : UnifyState) :
    unify st 1
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Eq"] (.cons .int .nil))
      = .err "type mismatch" := by
  have h_neq :
      (Ty.existential ["Show"] (.cons .int .nil) ==
        Ty.existential ["Eq"] (.cons .int .nil)) = false := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq]

/-- Distinct existential bound sets reject unification at any successor fuel. -/
theorem existential_bounds_mismatch_any_fuel (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1)
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Eq"] (.cons .int .nil))
      = .err "type mismatch" := by
  have hleft :
      applySubst st.subst fuel (.existential ["Show"] (.cons .int .nil)) =
        .existential ["Show"] (.cons .int .nil) := by
    cases fuel with
    | zero => rfl
    | succ n =>
      simp [applySubst, applySubstTyList_int_singleton st.subst n]
  have hright :
      applySubst st.subst fuel (.existential ["Eq"] (.cons .int .nil)) =
        .existential ["Eq"] (.cons .int .nil) := by
    cases fuel with
    | zero => rfl
    | succ n =>
      simp [applySubst, applySubstTyList_int_singleton st.subst n]
  have h_ctor_neq :
      (applySubst st.subst fuel (.existential ["Show"] (.cons .int .nil)) ==
        applySubst st.subst fuel (.existential ["Eq"] (.cons .int .nil))) = false := by
    simpa [hleft, hright] using
      (show (Ty.existential ["Show"] (.cons .int .nil) ==
              Ty.existential ["Eq"] (.cons .int .nil)) = false by native_decide)
  have h_bounds : (["Show"] : List String) ≠ (["Eq"] : List String) := by
    decide
  exact existential_unify_rejects_of_normalized st fuel
    ["Show"] ["Eq"] ["Show"] ["Eq"]
    (.cons .int .nil) (.cons .int .nil) (.cons .int .nil) (.cons .int .nil)
    hleft hright h_ctor_neq h_bounds

/-- Distinct existential bound sets reject unification at any successor fuel,
    for arbitrary associated-type lists. -/
theorem existential_bounds_mismatch_any_assoc_any_fuel
    (st : UnifyState) (fuel : Nat)
    (bounds1 bounds2 : List String) (assoc1 assoc2 : TyList)
    (h_bounds_ne : bounds1 ≠ bounds2) :
    unify st (fuel + 1)
      (.existential bounds1 assoc1)
      (.existential bounds2 assoc2)
      = .err "type mismatch" := by
  have h_bounds_beq : (bounds1 == bounds2) = false := by
    cases hbeq : (bounds1 == bounds2) with
    | false => rfl
    | true =>
      have h_eq : bounds1 = bounds2 := by simpa using hbeq
      exact (h_bounds_ne h_eq).elim
  cases fuel with
  | zero =>
    have hleft :
        applySubst st.subst 0 (.existential bounds1 assoc1) =
          .existential bounds1 assoc1 := rfl
    have hright :
        applySubst st.subst 0 (.existential bounds2 assoc2) =
          .existential bounds2 assoc2 := rfl
    have h_ctor_neq :
        (applySubst st.subst 0 (.existential bounds1 assoc1) ==
          applySubst st.subst 0 (.existential bounds2 assoc2)) = false := by
      have h_and_false :
          ((bounds1 == bounds2) && beqTyList assoc1 assoc2) = false := by
        rw [h_bounds_beq]
        simp
      have h_beq_false :
          ((Ty.existential bounds1 assoc1) == (Ty.existential bounds2 assoc2)) = false := by
        simpa [BEq.beq, beqTy] using h_and_false
      rw [hleft, hright]
      exact h_beq_false
    exact existential_unify_rejects_of_normalized st 0
      bounds1 bounds2 bounds1 bounds2
      assoc1 assoc2 assoc1 assoc2
      hleft hright h_ctor_neq h_bounds_ne
  | succ n =>
    have hleft :
        applySubst st.subst (n + 1) (.existential bounds1 assoc1) =
          .existential bounds1 (applySubstTyList st.subst n assoc1) := by
      simp [applySubst]
    have hright :
        applySubst st.subst (n + 1) (.existential bounds2 assoc2) =
          .existential bounds2 (applySubstTyList st.subst n assoc2) := by
      simp [applySubst]
    have h_ctor_neq :
        (applySubst st.subst (n + 1) (.existential bounds1 assoc1) ==
          applySubst st.subst (n + 1) (.existential bounds2 assoc2)) = false := by
      have h_and_false :
          ((bounds1 == bounds2) &&
            beqTyList (applySubstTyList st.subst n assoc1) (applySubstTyList st.subst n assoc2)) = false := by
        rw [h_bounds_beq]
        simp
      have h_beq_false :
          ((Ty.existential bounds1 (applySubstTyList st.subst n assoc1)) ==
            (Ty.existential bounds2 (applySubstTyList st.subst n assoc2))) = false := by
        simpa [BEq.beq, beqTy] using h_and_false
      rw [hleft, hright]
      exact h_beq_false
    exact existential_unify_rejects_of_normalized st (n + 1)
      bounds1 bounds2 bounds1 bounds2
      assoc1 assoc2 (applySubstTyList st.subst n assoc1) (applySubstTyList st.subst n assoc2)
      hleft hright h_ctor_neq h_bounds_ne

/-- Associated-type list length mismatch rejects existential unification. -/
theorem existential_assoc_length_mismatch (st : UnifyState) :
    unify st 3
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .int (.cons .bool .nil)))
      = .err "type list length mismatch" := by
  have h_neq :
      (Ty.existential ["Show"] (.cons .int .nil) ==
        Ty.existential ["Show"] (.cons .int (.cons .bool .nil))) = false := by
    native_decide
  have h_int_refl : unify st 1 .int .int = .ok st := by
    have h_int_eq : (Ty.int == Ty.int) = true := by native_decide
    simp [unify, applySubstCompat, applySubst, h_int_eq]
  unfold unify
  simp [applySubstCompat, applySubst, applySubstTyList, h_neq, unifyTyList, h_int_refl]

/-- Associated-type list length mismatch rejects existential unification at any
    outer successor+2 fuel. -/
theorem existential_assoc_length_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 3)
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .int (.cons .bool .nil)))
      = .err "type list length mismatch" := by
  have hleft :
      applySubst st.subst (fuel + 2) (.existential ["Show"] (.cons .int .nil)) =
        .existential ["Show"] (.cons .int .nil) := by
    have h_single :
        applySubstTyList st.subst (fuel + 1) (.cons .int .nil) =
          (.cons .int .nil) := applySubstTyList_int_singleton st.subst (fuel + 1)
    simp [applySubst, h_single]
  have hright :
      applySubst st.subst (fuel + 2) (.existential ["Show"] (.cons .int (.cons .bool .nil))) =
        .existential ["Show"] (.cons .int (.cons .bool .nil)) := by
    have h_pair :
        applySubstTyList st.subst (fuel + 1) (.cons .int (.cons .bool .nil)) =
          (.cons .int (.cons .bool .nil)) := applySubstTyList_int_bool_pair st.subst (fuel + 1)
    simp [applySubst, h_pair]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 2) (.existential ["Show"] (.cons .int .nil)) ==
        applySubst st.subst (fuel + 2) (.existential ["Show"] (.cons .int (.cons .bool .nil)))) = false := by
    simpa [hleft, hright] using
      (show (Ty.existential ["Show"] (.cons .int .nil) ==
              Ty.existential ["Show"] (.cons .int (.cons .bool .nil))) = false by native_decide)
  have h_assoc :
      unifyTyList st (fuel + 2) (.cons .int .nil) (.cons .int (.cons .bool .nil)) =
        .err "type list length mismatch" := by
    have h_int_refl : unify st (fuel + 1) .int .int = .ok st := by
      simpa using (unifyReflexive' st fuel .int)
    unfold unifyTyList
    simp [h_int_refl, unifyTyList]
  have h_bounds : (["Show"] : List String) = (["Show"] : List String) := rfl
  rw [existential_unify_reduces_to_assoc_of_normalized st (fuel + 2)
        ["Show"] ["Show"] ["Show"] ["Show"]
        (.cons .int .nil) (.cons .int (.cons .bool .nil))
        (.cons .int .nil) (.cons .int (.cons .bool .nil))
        hleft hright h_ctor_neq h_bounds]
  exact h_assoc

/-- Associated-type list length mismatch rejects existential unification at any
    successor+1 fuel for non-empty vs empty associated-type lists. -/
theorem existential_assoc_length_mismatch_any_nonempty_assoc_any_fuel
    (st : UnifyState) (fuel : Nat) (bound : String) (a : Ty) (asTail : TyList) :
    unify st (fuel + 2)
      (.existential [bound] (.cons a asTail))
      (.existential [bound] .nil)
      = .err "type list length mismatch" := by
  have h_neq_zero :
      ((Ty.existential [bound] (.cons a asTail) == Ty.existential [bound] .nil) = false) := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  cases fuel with
  | zero =>
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_zero, unifyTyList]
  | succ n =>
    have h_neq_succ :
        ((Ty.existential [bound] (.cons (applySubst st.subst n a) (applySubstTyList st.subst n asTail)) ==
          Ty.existential [bound] .nil) = false) := by
      simp [BEq.beq, beqTy, beqTyList]
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_succ, unifyTyList]

/-- Associated-type list length mismatch rejects existential unification at any
    successor+1 fuel for empty vs non-empty associated-type lists. -/
theorem existential_assoc_length_mismatch_empty_vs_nonempty_any_fuel
    (st : UnifyState) (fuel : Nat) (bound : String) (a : Ty) (asTail : TyList) :
    unify st (fuel + 2)
      (.existential [bound] .nil)
      (.existential [bound] (.cons a asTail))
      = .err "type list length mismatch" := by
  have h_neq_zero :
      ((Ty.existential [bound] .nil == Ty.existential [bound] (.cons a asTail)) = false) := by
    simp [BEq.beq, beqTy, beqTyList]
  unfold unify
  cases fuel with
  | zero =>
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_zero, unifyTyList]
  | succ n =>
    have h_neq_succ :
        ((Ty.existential [bound] .nil ==
          Ty.existential [bound] (.cons (applySubst st.subst n a) (applySubstTyList st.subst n asTail))) = false) := by
      simp [BEq.beq, beqTy, beqTyList]
    simp [applySubstCompat, applySubst, applySubstTyList, h_neq_succ, unifyTyList]

/-- At any outer successor+1 fuel, normalized associated-type-list errors
    propagate through existential unification unchanged when bounds match. -/
theorem existential_assoc_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (bounds1 bounds2 : List String) (assoc1 assoc2 : TyList)
    (e : String)
    (hbeq :
      (Ty.existential bounds1 (applySubstTyList st.subst fuel assoc1) ==
        Ty.existential bounds2 (applySubstTyList st.subst fuel assoc2)) = false)
    (h_bounds : bounds1 = bounds2)
    (h_assoc :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel assoc1)
        (applySubstTyList st.subst fuel assoc2) = .err e) :
    unify st (fuel + 2)
      (.existential bounds1 assoc1)
      (.existential bounds2 assoc2)
      = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.existential bounds1 assoc1) =
        .existential bounds1 (applySubstTyList st.subst fuel assoc1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.existential bounds2 assoc2) =
        .existential bounds2 (applySubstTyList st.subst fuel assoc2) := by
    simp [applySubst]
  have hbeq' :
      (applySubst st.subst (fuel + 1) (.existential bounds1 assoc1) ==
        applySubst st.subst (fuel + 1) (.existential bounds2 assoc2)) = false := by
    simpa [hleft, hright] using hbeq
  exact existential_unify_rejects_assoc_err_of_normalized_bounds_eq
    st (fuel + 1)
    bounds1 bounds2 bounds1 bounds2
    assoc1 assoc2
    (applySubstTyList st.subst fuel assoc1)
    (applySubstTyList st.subst fuel assoc2)
    hleft hright hbeq' h_bounds e h_assoc

/-- At any outer successor+1 fuel, normalized associated-type-list success
    propagates through existential unification with the same resulting state
    when bounds match. -/
theorem existential_assoc_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (bounds1 bounds2 : List String) (assoc1 assoc2 : TyList)
    (hbeq :
      (Ty.existential bounds1 (applySubstTyList st.subst fuel assoc1) ==
        Ty.existential bounds2 (applySubstTyList st.subst fuel assoc2)) = false)
    (h_bounds : bounds1 = bounds2)
    (h_assoc :
      unifyTyList st (fuel + 1)
        (applySubstTyList st.subst fuel assoc1)
        (applySubstTyList st.subst fuel assoc2) = .ok st') :
    unify st (fuel + 2)
      (.existential bounds1 assoc1)
      (.existential bounds2 assoc2)
      = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.existential bounds1 assoc1) =
        .existential bounds1 (applySubstTyList st.subst fuel assoc1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.existential bounds2 assoc2) =
        .existential bounds2 (applySubstTyList st.subst fuel assoc2) := by
    simp [applySubst]
  have hbeq' :
      (applySubst st.subst (fuel + 1) (.existential bounds1 assoc1) ==
        applySubst st.subst (fuel + 1) (.existential bounds2 assoc2)) = false := by
    simpa [hleft, hright] using hbeq
  exact existential_unify_accepts_of_normalized_assoc_ok
    st st' (fuel + 1)
    bounds1 bounds2 bounds1 bounds2
    assoc1 assoc2
    (applySubstTyList st.subst fuel assoc1)
    (applySubstTyList st.subst fuel assoc2)
    hleft hright hbeq' h_bounds h_assoc

/-- Existential associated-type mismatch (same bounds, same arity) rejects. -/
theorem existential_assoc_type_mismatch (st : UnifyState) :
    unify st 3
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .bool .nil))
      = .err "type mismatch" := by
  have h_neq :
      (Ty.existential ["Show"] (.cons .int .nil) ==
        Ty.existential ["Show"] (.cons .bool .nil)) = false := by
    native_decide
  have h_inner :
      unify st 1 .int .bool = .err "type mismatch" := by
    have h_inner_neq : (Ty.int == Ty.bool) = false := by
      native_decide
    unfold unify
    simp [applySubstCompat, applySubst, h_inner_neq]
  unfold unify
  simp [applySubstCompat, applySubst, applySubstTyList, h_neq, unifyTyList, h_inner]

/-- Existential and non-existential types do not unify. -/
theorem existential_non_existential_mismatch (st : UnifyState) :
    unify st 1
      (.existential ["Show"] (.cons .int .nil))
      .int
      = .err "type mismatch" := by
  have h_neq :
      (Ty.existential ["Show"] (.cons .int .nil) == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq]

/-- Boundary-sensitive sites where existential shape checks are enforced. -/
inductive ExistentialBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level existential boundary policy.
    Current scope:
    - bound sets and associated-type lists must match when existential wrappers
      are expected/actual
    - non-existential actuals are rejected when existential wrappers are expected
    - otherwise allowed (outside this boundary surface) -/
def existentialBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .existential eb ea, .existential ab aa =>
      (eb == ab) && (beqTyList ea aa)
  | .existential _ _, _ => false
  | _, _ => true

/-- Site-level wrapper for existential boundary checks. -/
def existentialBoundaryAllowsAtSite
    (_site : ExistentialBoundarySite) (expected actual : Ty) : Bool :=
  existentialBoundaryAllows expected actual

/-- Existential boundary policy is currently site-invariant. -/
theorem existential_boundary_policy_site_invariant
    (site1 site2 : ExistentialBoundarySite) (expected actual : Ty) :
    existentialBoundaryAllowsAtSite site1 expected actual =
      existentialBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Distinct existential bound sets are rejected by boundary policy. -/
theorem existential_boundary_rejects_bounds_mismatch :
    existentialBoundaryAllows
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Eq"] (.cons .int .nil))
      = false := by
  native_decide

/-- Distinct associated-type shapes are rejected by boundary policy. -/
theorem existential_boundary_rejects_assoc_mismatch :
    existentialBoundaryAllows
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .bool .nil))
      = false := by
  native_decide

/-- Non-existential actuals are rejected when existential wrappers are expected. -/
theorem existential_boundary_rejects_non_existential_actual :
    existentialBoundaryAllows
      (.existential ["Show"] (.cons .int .nil))
      .int
      = false := by
  native_decide

/-- Packaged existential boundary surface slice:
    site invariance + bound/assoc mismatch and non-existential rejection, with
    closure to concrete mismatch/reflexive unifier witnesses. -/
theorem existential_boundary_surface_slice
    (st : UnifyState) (site : ExistentialBoundarySite) :
    (existentialBoundaryAllowsAtSite site
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Eq"] (.cons .int .nil)) = false)
    ∧
    (existentialBoundaryAllowsAtSite site
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .bool .nil)) = false)
    ∧
    (existentialBoundaryAllowsAtSite site
      (.existential ["Show"] (.cons .int .nil))
      .int = false)
    ∧
    (unify st 1
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Eq"] (.cons .int .nil))
      = .err "type mismatch")
    ∧
    (unify st 3
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .bool .nil))
      = .err "type mismatch")
    ∧
    (unify st 1
      (.existential ["Show"] (.cons .int .nil))
      .int
      = .err "type mismatch")
    ∧
    (unify st 1
      (.existential ["Show"] (.cons .int .nil))
      (.existential ["Show"] (.cons .int .nil))
      = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact existential_boundary_rejects_bounds_mismatch
  · cases site <;> exact existential_boundary_rejects_assoc_mismatch
  · cases site <;> exact existential_boundary_rejects_non_existential_actual
  · exact existential_bounds_mismatch st
  · exact existential_assoc_type_mismatch st
  · exact existential_non_existential_mismatch st
  · exact existential_unifies_with_self st 0 ["Show"] (.cons .int .nil)

/-- Existential free vars are exactly associated-type free vars. -/
theorem existential_free_vars (bounds : List String) (assoc : TyList) :
    freeTypeVars (.existential bounds assoc) = freeTypeVarsTyList assoc /\
      freeRowVars (.existential bounds assoc) = freeRowVarsTyList assoc := by
  simp [freeTypeVars, freeRowVars]
