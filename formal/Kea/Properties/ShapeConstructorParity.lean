/-
  Kea.Properties.ShapeConstructorParity - Shape constructor parity slice.

  Current scope: `FixedSizeList` and `Tensor` are modeled in `Ty`, wired through
  substitution/unification, and validated with constructor-local parity theorems:
  substitution decomposition, reflexive unification, and mismatch witnesses.
-/

import Kea.Properties.UnifyReflexive
import Kea.Dimensions
import Kea.Properties.DecimalParity

private theorem nat_beq_false_of_ne {a b : Nat} (h : a = b -> False) : (a == b) = false := by
  cases h_beq : (a == b) with
  | false => rfl
  | true =>
    have hab : a = b := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h_beq)
    exact (h hab).elim

private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => rfl

/-- One substitution step over `FixedSizeList` rewrites only the element type. -/
theorem fixedSizeList_subst_step (s : Subst) (fuel : Nat) (elem : Ty) (d : Dim) :
    applySubst s (fuel + 1) (.fixedSizeList elem d) = .fixedSizeList (applySubst s fuel elem) d := by
  simp [applySubst]

/-- One substitution step over `Tensor` rewrites only the element type. -/
theorem tensor_subst_step (s : Subst) (fuel : Nat) (elem : Ty) (shape : List Dim) :
    applySubst s (fuel + 1) (.tensor elem shape) = .tensor (applySubst s fuel elem) shape := by
  simp [applySubst]

/-- On normalized fixed-size-list forms, failed constructor BEq short-circuit
    and equal dimensions reduce unification to inner-type unification. -/
theorem fixedSizeList_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (elem1 elem2 elem1' elem2' : Ty) (d1 d2 d1' d2' : Dim)
    (hleft :
      applySubst st.subst fuel (.fixedSizeList elem1 d1) =
        .fixedSizeList elem1' d1')
    (hright :
      applySubst st.subst fuel (.fixedSizeList elem2 d2) =
        .fixedSizeList elem2' d2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.fixedSizeList elem1 d1) ==
        applySubst st.subst fuel (.fixedSizeList elem2 d2)) = false)
    (h_dim : (d1' == d2') = true) :
    unify st (fuel + 1) (.fixedSizeList elem1 d1) (.fixedSizeList elem2 d2) =
      unify st fuel elem1' elem2' := by
  have h_ctor_neq' :
      (Ty.fixedSizeList elem1' d1' == Ty.fixedSizeList elem2' d2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_dim]

/-- On normalized tensor forms, failed constructor BEq short-circuit and equal
    shapes reduce unification to inner-type unification. -/
theorem tensor_unify_reduces_to_inner_of_normalized
    (st : UnifyState) (fuel : Nat)
    (elem1 elem2 elem1' elem2' : Ty) (shape1 shape2 shape1' shape2' : List Dim)
    (hleft :
      applySubst st.subst fuel (.tensor elem1 shape1) =
        .tensor elem1' shape1')
    (hright :
      applySubst st.subst fuel (.tensor elem2 shape2) =
        .tensor elem2' shape2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.tensor elem1 shape1) ==
        applySubst st.subst fuel (.tensor elem2 shape2)) = false)
    (h_shape : (shape1' == shape2') = true) :
    unify st (fuel + 1) (.tensor elem1 shape1) (.tensor elem2 shape2) =
      unify st fuel elem1' elem2' := by
  have h_ctor_neq' :
      (Ty.tensor elem1' shape1' == Ty.tensor elem2' shape2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_shape]

/-- At any outer successor+1 fuel, normalized fixed-size-list inner-type
    errors propagate through fixed-size-list unification unchanged when
    dimensions match. -/
theorem fixedSizeList_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (elem1 elem2 : Ty) (d1 d2 : Dim)
    (e : String)
    (hbeq :
      (Ty.fixedSizeList (applySubst st.subst fuel elem1) d1 ==
        Ty.fixedSizeList (applySubst st.subst fuel elem2) d2) = false)
    (h_dim : (d1 == d2) = true)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel elem1)
        (applySubst st.subst fuel elem2) = .err e) :
    unify st (fuel + 2)
      (.fixedSizeList elem1 d1)
      (.fixedSizeList elem2 d2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.fixedSizeList elem1 d1) =
        .fixedSizeList (applySubst st.subst fuel elem1) d1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.fixedSizeList elem2 d2) =
        .fixedSizeList (applySubst st.subst fuel elem2) d2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.fixedSizeList elem1 d1) ==
        applySubst st.subst (fuel + 1) (.fixedSizeList elem2 d2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.fixedSizeList elem1 d1) (.fixedSizeList elem2 d2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel elem1)
          (applySubst st.subst fuel elem2) := by
    exact fixedSizeList_unify_reduces_to_inner_of_normalized st (fuel + 1)
      elem1 elem2
      (applySubst st.subst fuel elem1)
      (applySubst st.subst fuel elem2)
      d1 d2 d1 d2
      hleft hright h_ctor_neq h_dim
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized fixed-size-list inner-type
    success propagates through fixed-size-list unification with the same
    resulting state when dimensions match. -/
theorem fixedSizeList_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (elem1 elem2 : Ty) (d1 d2 : Dim)
    (hbeq :
      (Ty.fixedSizeList (applySubst st.subst fuel elem1) d1 ==
        Ty.fixedSizeList (applySubst st.subst fuel elem2) d2) = false)
    (h_dim : (d1 == d2) = true)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel elem1)
        (applySubst st.subst fuel elem2) = .ok st') :
    unify st (fuel + 2)
      (.fixedSizeList elem1 d1)
      (.fixedSizeList elem2 d2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.fixedSizeList elem1 d1) =
        .fixedSizeList (applySubst st.subst fuel elem1) d1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.fixedSizeList elem2 d2) =
        .fixedSizeList (applySubst st.subst fuel elem2) d2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.fixedSizeList elem1 d1) ==
        applySubst st.subst (fuel + 1) (.fixedSizeList elem2 d2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.fixedSizeList elem1 d1) (.fixedSizeList elem2 d2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel elem1)
          (applySubst st.subst fuel elem2) := by
    exact fixedSizeList_unify_reduces_to_inner_of_normalized st (fuel + 1)
      elem1 elem2
      (applySubst st.subst fuel elem1)
      (applySubst st.subst fuel elem2)
      d1 d2 d1 d2
      hleft hright h_ctor_neq h_dim
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized tensor inner-type errors
    propagate through tensor unification unchanged when shapes match. -/
theorem tensor_inner_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (elem1 elem2 : Ty) (shape1 shape2 : List Dim)
    (e : String)
    (hbeq :
      (Ty.tensor (applySubst st.subst fuel elem1) shape1 ==
        Ty.tensor (applySubst st.subst fuel elem2) shape2) = false)
    (h_shape : (shape1 == shape2) = true)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel elem1)
        (applySubst st.subst fuel elem2) = .err e) :
    unify st (fuel + 2)
      (.tensor elem1 shape1)
      (.tensor elem2 shape2) = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.tensor elem1 shape1) =
        .tensor (applySubst st.subst fuel elem1) shape1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.tensor elem2 shape2) =
        .tensor (applySubst st.subst fuel elem2) shape2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.tensor elem1 shape1) ==
        applySubst st.subst (fuel + 1) (.tensor elem2 shape2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.tensor elem1 shape1) (.tensor elem2 shape2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel elem1)
          (applySubst st.subst fuel elem2) := by
    exact tensor_unify_reduces_to_inner_of_normalized st (fuel + 1)
      elem1 elem2
      (applySubst st.subst fuel elem1)
      (applySubst st.subst fuel elem2)
      shape1 shape2 shape1 shape2
      hleft hright h_ctor_neq h_shape
  rw [h_reduce]
  exact h_inner

/-- At any outer successor+1 fuel, normalized tensor inner-type success
    propagates through tensor unification with the same resulting state when
    shapes match. -/
theorem tensor_inner_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (elem1 elem2 : Ty) (shape1 shape2 : List Dim)
    (hbeq :
      (Ty.tensor (applySubst st.subst fuel elem1) shape1 ==
        Ty.tensor (applySubst st.subst fuel elem2) shape2) = false)
    (h_shape : (shape1 == shape2) = true)
    (h_inner :
      unify st (fuel + 1)
        (applySubst st.subst fuel elem1)
        (applySubst st.subst fuel elem2) = .ok st') :
    unify st (fuel + 2)
      (.tensor elem1 shape1)
      (.tensor elem2 shape2) = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.tensor elem1 shape1) =
        .tensor (applySubst st.subst fuel elem1) shape1 := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.tensor elem2 shape2) =
        .tensor (applySubst st.subst fuel elem2) shape2 := by
    simp [applySubst]
  have h_ctor_neq :
      (applySubst st.subst (fuel + 1) (.tensor elem1 shape1) ==
        applySubst st.subst (fuel + 1) (.tensor elem2 shape2)) = false := by
    simpa [hleft, hright] using hbeq
  have h_reduce :
      unify st (fuel + 2) (.tensor elem1 shape1) (.tensor elem2 shape2) =
        unify st (fuel + 1)
          (applySubst st.subst fuel elem1)
          (applySubst st.subst fuel elem2) := by
    exact tensor_unify_reduces_to_inner_of_normalized st (fuel + 1)
      elem1 elem2
      (applySubst st.subst fuel elem1)
      (applySubst st.subst fuel elem2)
      shape1 shape2 shape1 shape2
      hleft hright h_ctor_neq h_shape
  rw [h_reduce]
  exact h_inner

/-- On normalized fixed-size-list forms, failed constructor BEq short-circuit
    and unequal dimensions force mismatch. -/
theorem fixedSizeList_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (elem1 elem2 elem1' elem2' : Ty) (d1 d2 d1' d2' : Dim)
    (hleft :
      applySubst st.subst fuel (.fixedSizeList elem1 d1) =
        .fixedSizeList elem1' d1')
    (hright :
      applySubst st.subst fuel (.fixedSizeList elem2 d2) =
        .fixedSizeList elem2' d2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.fixedSizeList elem1 d1) ==
        applySubst st.subst fuel (.fixedSizeList elem2 d2)) = false)
    (h_dim : (d1' == d2') = false) :
    unify st (fuel + 1) (.fixedSizeList elem1 d1) (.fixedSizeList elem2 d2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.fixedSizeList elem1' d1' == Ty.fixedSizeList elem2' d2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_dim]

/-- On normalized tensor forms, failed constructor BEq short-circuit and unequal
    shapes force mismatch. -/
theorem tensor_unify_rejects_of_normalized
    (st : UnifyState) (fuel : Nat)
    (elem1 elem2 elem1' elem2' : Ty) (shape1 shape2 shape1' shape2' : List Dim)
    (hleft :
      applySubst st.subst fuel (.tensor elem1 shape1) =
        .tensor elem1' shape1')
    (hright :
      applySubst st.subst fuel (.tensor elem2 shape2) =
        .tensor elem2' shape2')
    (h_ctor_neq :
      (applySubst st.subst fuel (.tensor elem1 shape1) ==
        applySubst st.subst fuel (.tensor elem2 shape2)) = false)
    (h_shape : (shape1' == shape2') = false) :
    unify st (fuel + 1) (.tensor elem1 shape1) (.tensor elem2 shape2) =
      .err "type mismatch" := by
  have h_ctor_neq' :
      (Ty.tensor elem1' shape1' == Ty.tensor elem2' shape2') = false := by
    simpa [hleft, hright] using h_ctor_neq
  simp [unify, applySubstCompat, hleft, hright, h_ctor_neq', h_shape]

/-- `FixedSizeList` unifies with itself. -/
theorem fixedSizeList_unifies_with_self
    (st : UnifyState) (fuel : Nat) (elem : Ty) (d : Dim) :
    unify st (fuel + 1) (.fixedSizeList elem d) (.fixedSizeList elem d) = .ok st := by
  simpa using (unifyReflexive' st fuel (.fixedSizeList elem d))

/-- `Tensor` unifies with itself. -/
theorem tensor_unifies_with_self
    (st : UnifyState) (fuel : Nat) (elem : Ty) (shape : List Dim) :
    unify st (fuel + 1) (.tensor elem shape) (.tensor elem shape) = .ok st := by
  simpa using (unifyReflexive' st fuel (.tensor elem shape))

/-- Fixed-size-list size mismatch does not unify. -/
theorem fixedSizeList_dim_mismatch
    (st : UnifyState) (d1 d2 : Nat) (h : d1 = d2 -> False) :
    unify st 1
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch" := by
  have h_dim : ((Dim.const d1 : Dim) == Dim.const d2) = false := by
    change (d1 == d2) = false
    exact nat_beq_false_of_ne h
  have h_neq :
      (Ty.fixedSizeList Ty.int (.const d1) == Ty.fixedSizeList Ty.int (.const d2)) = false := by
    show beqTy (Ty.fixedSizeList Ty.int (.const d1)) (Ty.fixedSizeList Ty.int (.const d2)) = false
    simp [beqTy, h_dim]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_dim]

/-- Fixed-size-list size mismatch does not unify at any successor fuel. -/
theorem fixedSizeList_dim_mismatch_any_fuel
    (st : UnifyState) (fuel d1 d2 : Nat) (h : d1 = d2 -> False) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch" := by
  have h_dim : ((Dim.const d1 : Dim) == Dim.const d2) = false := by
    change (d1 == d2) = false
    exact nat_beq_false_of_ne h
  have h_neq :
      (Ty.fixedSizeList Ty.int (.const d1) == Ty.fixedSizeList Ty.int (.const d2)) = false := by
    show beqTy (Ty.fixedSizeList Ty.int (.const d1)) (Ty.fixedSizeList Ty.int (.const d2)) = false
    simp [beqTy, h_dim]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_dim]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst, h_int, h_dim]
      exact h_neq

/-- Tensor rank mismatch (shape length mismatch) does not unify. -/
theorem tensor_rank_mismatch
    (st : UnifyState) (d : Nat) :
    unify st 1
      (.tensor .int [Dim.const d])
      (.tensor .int [Dim.const d, Dim.const (d + 1)])
      = .err "type mismatch" := by
  have h_shape :
      ((([Dim.const d] : List Dim) == [Dim.const d, Dim.const (d + 1)]) = false) := by
    simp [instBEqDim]
  have h_neq :
      (Ty.tensor Ty.int [Dim.const d] == Ty.tensor Ty.int [Dim.const d, Dim.const (d + 1)]) = false := by
    show beqTy (Ty.tensor Ty.int [Dim.const d]) (Ty.tensor Ty.int [Dim.const d, Dim.const (d + 1)]) = false
    simp [beqTy, h_shape]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_shape]

/-- Tensor rank mismatch (shape length mismatch) does not unify at any successor fuel. -/
theorem tensor_rank_mismatch_any_fuel
    (st : UnifyState) (fuel d : Nat) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d])
      (.tensor .int [Dim.const d, Dim.const (d + 1)])
      = .err "type mismatch" := by
  have h_shape :
      ((([Dim.const d] : List Dim) == [Dim.const d, Dim.const (d + 1)]) = false) := by
    simp [instBEqDim]
  have h_neq :
      (Ty.tensor Ty.int [Dim.const d] == Ty.tensor Ty.int [Dim.const d, Dim.const (d + 1)]) = false := by
    show beqTy (Ty.tensor Ty.int [Dim.const d]) (Ty.tensor Ty.int [Dim.const d, Dim.const (d + 1)]) = false
    simp [beqTy, h_shape]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_shape]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst, h_int, h_shape]
      exact h_neq

/-- Fixed-size-list size mismatch rejects unification at any successor fuel for
    arbitrary inner element types. -/
theorem fixedSizeList_dim_mismatch_any_elem_any_fuel
    (st : UnifyState) (fuel : Nat) (elem : Ty) (d1 d2 : Nat)
    (h : d1 = d2 -> False) :
    unify st (fuel + 1)
      (.fixedSizeList elem (.const d1))
      (.fixedSizeList elem (.const d2))
      = .err "type mismatch" := by
  have h_dim : ((Dim.const d1 : Dim) == Dim.const d2) = false := by
    change (d1 == d2) = false
    exact nat_beq_false_of_ne h
  have h_neq :
      (Ty.fixedSizeList elem (.const d1) == Ty.fixedSizeList elem (.const d2)) = false := by
    show beqTy (Ty.fixedSizeList elem (.const d1)) (Ty.fixedSizeList elem (.const d2)) = false
    simp [beqTy, h_dim]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_dim]
  | succ fuel' =>
      have h_neq' :
          (Ty.fixedSizeList (applySubst st.subst fuel' elem) (.const d1) ==
            Ty.fixedSizeList (applySubst st.subst fuel' elem) (.const d2)) = false := by
        simp [BEq.beq, beqTy]
        intro _
        intro hd_eq
        exact h hd_eq
      unfold unify
      simp [applySubstCompat, applySubst, h_neq', h_dim]

/-- Tensor shape mismatch rejects unification at any successor fuel for
    arbitrary inner element types. -/
theorem tensor_shape_mismatch_any_elem_any_fuel
    (st : UnifyState) (fuel : Nat) (elem : Ty) (shape1 shape2 : List Dim)
    (h_shape : (shape1 == shape2) = false) :
    unify st (fuel + 1)
      (.tensor elem shape1)
      (.tensor elem shape2)
      = .err "type mismatch" := by
  have h_neq :
      (Ty.tensor elem shape1 == Ty.tensor elem shape2) = false := by
    show beqTy (Ty.tensor elem shape1) (Ty.tensor elem shape2) = false
    simp [beqTy, h_shape]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_shape]
  | succ fuel' =>
      have h_neq' :
          (Ty.tensor (applySubst st.subst fuel' elem) shape1 ==
            Ty.tensor (applySubst st.subst fuel' elem) shape2) = false := by
        simp [BEq.beq, beqTy]
        intro _
        exact h_shape
      unfold unify
      simp [applySubstCompat, applySubst, h_neq', h_shape]

/-- Fixed-size-list var-vs-const dimensions reject unification at any
    successor fuel for arbitrary inner element types. -/
theorem fixedSizeList_var_const_dim_mismatch_any_elem_any_fuel
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    unify st (fuel + 1)
      (.fixedSizeList elem (.var v))
      (.fixedSizeList elem (.const n))
      = .err "type mismatch" := by
  have h_dim : ((Dim.var v : Dim) == Dim.const n) = false := by
    simp [BEq.beq]
  have h_neq :
      (Ty.fixedSizeList elem (.var v) == Ty.fixedSizeList elem (.const n)) = false := by
    show beqTy (Ty.fixedSizeList elem (.var v)) (Ty.fixedSizeList elem (.const n)) = false
    simp [beqTy, h_dim]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_dim]
  | succ fuel' =>
      have h_neq' :
          (Ty.fixedSizeList (applySubst st.subst fuel' elem) (.var v) ==
            Ty.fixedSizeList (applySubst st.subst fuel' elem) (.const n)) = false := by
        simp [BEq.beq, beqTy]
      unfold unify
      simp [applySubstCompat, applySubst, h_neq', h_dim]

/-- Fixed-size-list const-vs-var dimensions reject unification at any
    successor fuel for arbitrary inner element types. -/
theorem fixedSizeList_const_var_dim_mismatch_any_elem_any_fuel
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    unify st (fuel + 1)
      (.fixedSizeList elem (.const n))
      (.fixedSizeList elem (.var v))
      = .err "type mismatch" := by
  have h_dim : ((Dim.const n : Dim) == Dim.var v) = false := by
    simp [BEq.beq]
  have h_neq :
      (Ty.fixedSizeList elem (.const n) == Ty.fixedSizeList elem (.var v)) = false := by
    show beqTy (Ty.fixedSizeList elem (.const n)) (Ty.fixedSizeList elem (.var v)) = false
    simp [beqTy, h_dim]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_dim]
  | succ fuel' =>
      have h_neq' :
          (Ty.fixedSizeList (applySubst st.subst fuel' elem) (.const n) ==
            Ty.fixedSizeList (applySubst st.subst fuel' elem) (.var v)) = false := by
        simp [BEq.beq, beqTy]
      unfold unify
      simp [applySubstCompat, applySubst, h_neq', h_dim]

/-- Rank-1 tensor var-vs-const shape mismatch rejects unification at any
    successor fuel for arbitrary inner element types. -/
theorem tensor_rank1_var_const_shape_mismatch_any_elem_any_fuel
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    unify st (fuel + 1)
      (.tensor elem [Dim.var v])
      (.tensor elem [Dim.const n])
      = .err "type mismatch" := by
  have h_shape : (([Dim.var v] : List Dim) == [Dim.const n]) = false := by
    simp [List.beq, BEq.beq]
  exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.var v] [Dim.const n] h_shape

/-- Rank-1 tensor const-vs-var shape mismatch rejects unification at any
    successor fuel for arbitrary inner element types. -/
theorem tensor_rank1_const_var_shape_mismatch_any_elem_any_fuel
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    unify st (fuel + 1)
      (.tensor elem [Dim.const n])
      (.tensor elem [Dim.var v])
      = .err "type mismatch" := by
  have h_shape : (([Dim.const n] : List Dim) == [Dim.var v]) = false := by
    simp [List.beq, BEq.beq]
  exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.const n] [Dim.var v] h_shape

/-- Dim-kernel succeeds on fixed-size-list var-vs-const dimensions by binding
    the dimension variable. -/
theorem fixedSizeList_var_const_dim_kernel_success
    (fuel : Nat) (v : DimVarId) (n : Nat) :
    unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) =
      some (DimSubst.extend DimSubst.empty v (.const n)) := by
  exact unifyDim_var_const_binds DimSubst.empty fuel v n rfl

/-- Dim-kernel succeeds on fixed-size-list const-vs-var dimensions by binding
    the dimension variable. -/
theorem fixedSizeList_const_var_dim_kernel_success
    (fuel : Nat) (n : Nat) (v : DimVarId) :
    unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) =
      some (DimSubst.extend DimSubst.empty v (.const n)) := by
  exact unifyDim_const_var_binds DimSubst.empty fuel n v rfl

/-- Current constructor-level fixed-size-list unifier rejects var-vs-const
    dimensions even when the dim-kernel succeeds via variable binding. -/
theorem fixedSizeList_var_const_kernel_success_but_unify_rejects
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    ∃ s' : DimSubst,
      unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s' ∧
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .err "type mismatch" := by
  refine ⟨DimSubst.extend DimSubst.empty v (.const n), ?_, ?_⟩
  · exact fixedSizeList_var_const_dim_kernel_success fuel v n
  · exact fixedSizeList_var_const_dim_mismatch_any_elem_any_fuel st fuel elem v n

/-- Current constructor-level fixed-size-list unifier rejects const-vs-var
    dimensions even when the dim-kernel succeeds via variable binding. -/
theorem fixedSizeList_const_var_kernel_success_but_unify_rejects
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    ∃ s' : DimSubst,
      unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s' ∧
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .err "type mismatch" := by
  refine ⟨DimSubst.extend DimSubst.empty v (.const n), ?_, ?_⟩
  · exact fixedSizeList_const_var_dim_kernel_success fuel n v
  · exact fixedSizeList_const_var_dim_mismatch_any_elem_any_fuel st fuel elem n v

/-- Pointwise dim-kernel still succeeds on rank-1 tensor var-vs-const shapes
    by binding the shape variable. -/
theorem tensor_rank1_var_const_dim_kernel_success
    (fuel : Nat) (v : DimVarId) (n : Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v] [Dim.const n] =
      some (DimSubst.extend DimSubst.empty v (.const n)) := by
  exact unifyDimList_single_var_const_binds fuel v n

/-- Pointwise dim-kernel still succeeds on rank-1 tensor const-vs-var shapes
    by binding the shape variable. -/
theorem tensor_rank1_const_var_dim_kernel_success
    (fuel : Nat) (n : Nat) (v : DimVarId) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n] [Dim.var v] =
      some (DimSubst.extend DimSubst.empty v (.const n)) := by
  exact unifyDimList_single_const_var_binds fuel n v

/-- Current constructor-level tensor unifier rejects rank-1 var-vs-const
    shapes even when the pointwise dim-kernel succeeds via variable binding. -/
theorem tensor_rank1_var_const_kernel_success_but_unify_rejects
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v] [Dim.const n] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .err "type mismatch" := by
  refine ⟨DimSubst.extend DimSubst.empty v (.const n), ?_, ?_⟩
  · exact tensor_rank1_var_const_dim_kernel_success fuel v n
  · exact tensor_rank1_var_const_shape_mismatch_any_elem_any_fuel st fuel elem v n

/-- Current constructor-level tensor unifier rejects rank-1 const-vs-var
    shapes even when the pointwise dim-kernel succeeds via variable binding. -/
theorem tensor_rank1_const_var_kernel_success_but_unify_rejects
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n] [Dim.var v] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .err "type mismatch" := by
  refine ⟨DimSubst.extend DimSubst.empty v (.const n), ?_, ?_⟩
  · exact tensor_rank1_const_var_dim_kernel_success fuel n v
  · exact tensor_rank1_const_var_shape_mismatch_any_elem_any_fuel st fuel elem n v

/-- Pointwise dim-kernel succeeds on rank-2 tensor var-vs-const shapes when
    the shape variables are distinct. -/
theorem tensor_rank2_var_const_dim_kernel_success_distinct
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) (h_distinct : v1 ≠ v2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v1, Dim.var v2]
      [Dim.const n1, Dim.const n2] =
      some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) := by
  exact unifyDimList_pair_var_const_binds_distinct fuel v1 v2 n1 n2 h_distinct

/-- Current constructor-level tensor unifier still rejects rank-2 var-vs-const
    shapes even when the pointwise dim-kernel succeeds (distinct vars case). -/
theorem tensor_rank2_var_const_kernel_success_but_unify_rejects_distinct
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) (h_distinct : v1 ≠ v2) :
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2]
        [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch" := by
  refine ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2), ?_, ?_⟩
  · exact tensor_rank2_var_const_dim_kernel_success_distinct fuel v1 v2 n1 n2 h_distinct
  · have h_shape :
        (([Dim.var v1, Dim.var v2] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
      simp [instBEqDim]
    exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.var v1, Dim.var v2] [Dim.const n1, Dim.const n2] h_shape

/-- Pointwise dim-kernel succeeds on rank-2 tensor const-vs-var shapes when
    the shape variables are distinct. -/
theorem tensor_rank2_const_var_dim_kernel_success_distinct
    (fuel : Nat) (n1 n2 : Nat) (v1 v2 : DimVarId) (h_distinct : v1 ≠ v2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v1, Dim.var v2] =
      some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) := by
  exact unifyDimList_pair_const_var_binds_distinct fuel n1 n2 v1 v2 h_distinct

/-- Current constructor-level tensor unifier still rejects rank-2 const-vs-var
    shapes even when the pointwise dim-kernel succeeds (distinct vars case). -/
theorem tensor_rank2_const_var_kernel_success_but_unify_rejects_distinct
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) (h_distinct : v1 ≠ v2) :
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v1, Dim.var v2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch" := by
  refine ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2), ?_, ?_⟩
  · exact tensor_rank2_const_var_dim_kernel_success_distinct fuel n1 n2 v1 v2 h_distinct
  · have h_shape :
      (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v1, Dim.var v2]) = false := by
      simp [instBEqDim]
    exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.const n1, Dim.const n2] [Dim.var v1, Dim.var v2] h_shape

/-- Pointwise dim-kernel succeeds on rank-2 tensor repeated-var-vs-const
    shapes when both constants agree. -/
theorem tensor_rank2_same_var_const_dim_kernel_success_of_eq
    (fuel : Nat) (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v, Dim.var v]
      [Dim.const n1, Dim.const n2] =
      some (DimSubst.extend DimSubst.empty v (.const n1)) := by
  exact unifyDimList_pair_same_var_const_binds_of_eq fuel v n1 n2 h_eq

/-- Pointwise dim-kernel fails on rank-2 tensor repeated-var-vs-const
    shapes when constants disagree. -/
theorem tensor_rank2_same_var_const_dim_kernel_none_of_ne
    (fuel : Nat) (v : DimVarId) (n1 n2 : Nat) (h_ne : n1 ≠ n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v, Dim.var v]
      [Dim.const n1, Dim.const n2] = none := by
  exact unifyDimList_pair_same_var_const_none_of_ne fuel v n1 n2 h_ne

/-- Pointwise dim-kernel success for rank-2 repeated-var-vs-const shapes is
    equivalent to constant equality. -/
theorem tensor_rank2_same_var_const_dim_kernel_some_iff_eq
    (fuel : Nat) (v : DimVarId) (n1 n2 : Nat) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v, Dim.var v]
        [Dim.const n1, Dim.const n2] = some s') ↔ n1 = n2 := by
  constructor
  · intro h_some
    rcases h_some with ⟨s', h_some⟩
    by_cases h_eq : n1 = n2
    · exact h_eq
    · have h_none :
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v, Dim.var v]
            [Dim.const n1, Dim.const n2] = none :=
        tensor_rank2_same_var_const_dim_kernel_none_of_ne fuel v n1 n2 h_eq
      rw [h_none] at h_some
      cases h_some
  · intro h_eq
    exact ⟨DimSubst.extend DimSubst.empty v (.const n1),
      tensor_rank2_same_var_const_dim_kernel_success_of_eq fuel v n1 n2 h_eq⟩

/-- Constructor-level tensor unifier rejects rank-2 repeated-var-vs-const
    shapes for all constants. -/
theorem tensor_rank2_same_var_const_unify_rejects_any
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) :
    unify st (fuel + 1)
      (.tensor elem [Dim.var v, Dim.var v])
      (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch" := by
  have h_shape :
      (([Dim.var v, Dim.var v] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
    simp [instBEqDim]
  exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.var v, Dim.var v] [Dim.const n1, Dim.const n2] h_shape

/-- For rank-2 repeated-var-vs-const shapes, the naive contract
    `unify-ok ↔ dim-kernel-success` holds exactly when constants disagree
    (both sides false). -/
theorem tensor_rank2_same_var_const_ok_iff_dim_kernel_success_iff_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) :
    (unify st (fuel + 1)
      (.tensor elem [Dim.var v, Dim.var v])
      (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s') ↔
    n1 ≠ n2 := by
  have h_not_ok :
      ¬ (unify st (fuel + 1)
          (.tensor elem [Dim.var v, Dim.var v])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st) := by
    intro h_ok
    have h_err := tensor_rank2_same_var_const_unify_rejects_any st fuel elem v n1 n2
    rw [h_ok] at h_err
    cases h_err
  constructor
  · intro h_iff
    intro h_eq
    have h_kernel :
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v, Dim.var v]
            [Dim.const n1, Dim.const n2] = some s' :=
      (tensor_rank2_same_var_const_dim_kernel_some_iff_eq fuel v n1 n2).2 h_eq
    exact h_not_ok (h_iff.2 h_kernel)
  · intro h_ne
    constructor
    · intro h_ok
      exact (h_not_ok h_ok).elim
    · intro h_kernel
      have h_eq : n1 = n2 :=
        (tensor_rank2_same_var_const_dim_kernel_some_iff_eq fuel v n1 n2).1 h_kernel
      exact (h_ne h_eq).elim

/-- Current constructor-level tensor unifier rejects rank-2 repeated-var-vs-const
    shapes even when pointwise dim-kernel succeeds (equal-constants case). -/
theorem tensor_rank2_same_var_const_kernel_success_but_unify_rejects_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v, Dim.var v]
        [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch" := by
  refine ⟨DimSubst.extend DimSubst.empty v (.const n1), ?_, ?_⟩
  · exact tensor_rank2_same_var_const_dim_kernel_success_of_eq fuel v n1 n2 h_eq
  · have h_shape :
        (([Dim.var v, Dim.var v] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
      simp [instBEqDim]
    exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.var v, Dim.var v] [Dim.const n1, Dim.const n2] h_shape

/-- Pointwise dim-kernel succeeds on rank-2 tensor const-vs-repeated-var
    shapes when both constants agree. -/
theorem tensor_rank2_const_same_var_dim_kernel_success_of_eq
    (fuel : Nat) (n1 n2 : Nat) (v : DimVarId) (h_eq : n1 = n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v, Dim.var v] =
      some (DimSubst.extend DimSubst.empty v (.const n1)) := by
  exact unifyDimList_pair_const_same_var_binds_of_eq fuel n1 n2 v h_eq

/-- Rank-2 var-vs-const pointwise dim-kernel succeeds exactly when variables
    are distinct, or repeated-variable constants agree. -/
theorem tensor_rank2_var_const_dim_kernel_some_iff_var_distinct_or_consts_eq
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2]
        [Dim.const n1, Dim.const n2] = some s') ↔
    (v1 ≠ v2 ∨ n1 = n2) := by
  exact unifyDimList_pair_var_const_some_iff_var_distinct_or_consts_eq fuel v1 v2 n1 n2

/-- Rank-2 var-vs-const pointwise dim-kernel fails exactly when variables are
    equal and constants disagree. -/
theorem tensor_rank2_var_const_dim_kernel_none_iff_var_eq_and_consts_ne
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v1, Dim.var v2]
      [Dim.const n1, Dim.const n2] = none ↔
    (v1 = v2 ∧ n1 ≠ n2) := by
  exact unifyDimList_pair_var_const_none_iff_var_eq_and_consts_ne fuel v1 v2 n1 n2

/-- Rank-2 const-vs-var pointwise dim-kernel succeeds exactly when variables
    are distinct, or repeated-variable constants agree. -/
theorem tensor_rank2_const_var_dim_kernel_some_iff_var_distinct_or_consts_eq
    (fuel : Nat) (n1 n2 : Nat) (v1 v2 : DimVarId) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v1, Dim.var v2] = some s') ↔
    (v1 ≠ v2 ∨ n1 = n2) := by
  exact unifyDimList_pair_const_var_some_iff_var_distinct_or_consts_eq fuel n1 n2 v1 v2

/-- Rank-2 const-vs-var pointwise dim-kernel fails exactly when variables are
    equal and constants disagree. -/
theorem tensor_rank2_const_var_dim_kernel_none_iff_var_eq_and_consts_ne
    (fuel : Nat) (n1 n2 : Nat) (v1 v2 : DimVarId) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v1, Dim.var v2] = none ↔
    (v1 = v2 ∧ n1 ≠ n2) := by
  exact unifyDimList_pair_const_var_none_iff_var_eq_and_consts_ne fuel n1 n2 v1 v2

/-- Packaged rank-2 mixed dim-kernel decomposition by variable/constant
    equality, for both var-vs-const and const-vs-var orientations. -/
theorem tensor_rank2_mixed_dim_kernel_pair_decomposition_slice
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) :
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s') ↔
      (v1 ≠ v2 ∨ n1 = n2))
    ∧
    (unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2]
        [Dim.const n1, Dim.const n2] = none ↔
      (v1 = v2 ∧ n1 ≠ n2))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') ↔
      (v1 ≠ v2 ∨ n1 = n2))
    ∧
    (unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v1, Dim.var v2] = none ↔
      (v1 = v2 ∧ n1 ≠ n2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tensor_rank2_var_const_dim_kernel_some_iff_var_distinct_or_consts_eq fuel v1 v2 n1 n2
  · exact tensor_rank2_var_const_dim_kernel_none_iff_var_eq_and_consts_ne fuel v1 v2 n1 n2
  · exact tensor_rank2_const_var_dim_kernel_some_iff_var_distinct_or_consts_eq fuel n1 n2 v1 v2
  · exact tensor_rank2_const_var_dim_kernel_none_iff_var_eq_and_consts_ne fuel n1 n2 v1 v2

/-- Pointwise dim-kernel fails on rank-2 tensor const-vs-repeated-var
    shapes when constants disagree. -/
theorem tensor_rank2_const_same_var_dim_kernel_none_of_ne
    (fuel : Nat) (n1 n2 : Nat) (v : DimVarId) (h_ne : n1 ≠ n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v, Dim.var v] = none := by
  exact unifyDimList_pair_const_same_var_none_of_ne fuel n1 n2 v h_ne

/-- Pointwise dim-kernel success for rank-2 const-vs-repeated-var shapes is
    equivalent to constant equality. -/
theorem tensor_rank2_const_same_var_dim_kernel_some_iff_eq
    (fuel : Nat) (n1 n2 : Nat) (v : DimVarId) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v, Dim.var v] = some s') ↔ n1 = n2 := by
  constructor
  · intro h_some
    rcases h_some with ⟨s', h_some⟩
    by_cases h_eq : n1 = n2
    · exact h_eq
    · have h_none :
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v, Dim.var v] = none :=
        tensor_rank2_const_same_var_dim_kernel_none_of_ne fuel n1 n2 v h_eq
      rw [h_none] at h_some
      cases h_some
  · intro h_eq
    exact ⟨DimSubst.extend DimSubst.empty v (.const n1),
      tensor_rank2_const_same_var_dim_kernel_success_of_eq fuel n1 n2 v h_eq⟩

/-- Constructor-level tensor unifier rejects rank-2 const-vs-repeated-var
    shapes for all constants. -/
theorem tensor_rank2_const_same_var_unify_rejects_any
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) :
    unify st (fuel + 1)
      (.tensor elem [Dim.const n1, Dim.const n2])
      (.tensor elem [Dim.var v, Dim.var v]) = .err "type mismatch" := by
  have h_shape :
      (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v, Dim.var v]) = false := by
    simp [instBEqDim]
  exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.const n1, Dim.const n2] [Dim.var v, Dim.var v] h_shape

/-- For rank-2 const-vs-repeated-var shapes, the naive contract
    `unify-ok ↔ dim-kernel-success` holds exactly when constants disagree
    (both sides false). -/
theorem tensor_rank2_const_same_var_ok_iff_dim_kernel_success_iff_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) :
    (unify st (fuel + 1)
      (.tensor elem [Dim.const n1, Dim.const n2])
      (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s') ↔
    n1 ≠ n2 := by
  have h_not_ok :
      ¬ (unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v, Dim.var v]) = .ok st) := by
    intro h_ok
    have h_err := tensor_rank2_const_same_var_unify_rejects_any st fuel elem n1 n2 v
    rw [h_ok] at h_err
    cases h_err
  constructor
  · intro h_iff
    intro h_eq
    have h_kernel :
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v, Dim.var v] = some s' :=
      (tensor_rank2_const_same_var_dim_kernel_some_iff_eq fuel n1 n2 v).2 h_eq
    exact h_not_ok (h_iff.2 h_kernel)
  · intro h_ne
    constructor
    · intro h_ok
      exact (h_not_ok h_ok).elim
    · intro h_kernel
      have h_eq : n1 = n2 :=
        (tensor_rank2_const_same_var_dim_kernel_some_iff_eq fuel n1 n2 v).1 h_kernel
      exact (h_ne h_eq).elim

/-- On unequal constants, the naive rank-2 repeated-var-vs-const contract
    `unify-ok ↔ dim-kernel-success` holds vacuously (both sides false). -/
theorem tensor_rank2_same_var_const_ok_iff_dim_kernel_success_of_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_ne : n1 ≠ n2) :
    unify st (fuel + 1)
      (.tensor elem [Dim.var v, Dim.var v])
      (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v, Dim.var v]
        [Dim.const n1, Dim.const n2] = some s' := by
  exact (tensor_rank2_same_var_const_ok_iff_dim_kernel_success_iff_ne
    st fuel elem v n1 n2).2 h_ne

/-- On unequal constants, the naive rank-2 const-vs-repeated-var contract
    `unify-ok ↔ dim-kernel-success` holds vacuously (both sides false). -/
theorem tensor_rank2_const_same_var_ok_iff_dim_kernel_success_of_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) (h_ne : n1 ≠ n2) :
    unify st (fuel + 1)
      (.tensor elem [Dim.const n1, Dim.const n2])
      (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v, Dim.var v] = some s' := by
  exact (tensor_rank2_const_same_var_ok_iff_dim_kernel_success_iff_ne
    st fuel elem n1 n2 v).2 h_ne

/-- Packaged split decision for same-variable rank-2 mixed shapes:
    the naive `ok ↔ dim-kernel-success` contract holds exactly on unequal
    constants in both orientations. -/
theorem tensor_rank2_same_var_ok_iff_dim_kernel_success_split
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) :
    ((unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s') ↔
      n1 ≠ n2)
    ∧
    ((unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s') ↔
      n1 ≠ n2) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_same_var_const_ok_iff_dim_kernel_success_iff_ne
      st fuel elem v n1 n2
  · exact tensor_rank2_const_same_var_ok_iff_dim_kernel_success_iff_ne
      st fuel elem n1 n2 v

/-- For rank-2 repeated-var-vs-const shapes, non-generalization of the naive
    `ok ↔ dim-kernel-success` contract occurs exactly when constants are equal. -/
theorem tensor_rank2_same_var_const_non_generalization_iff_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s'
    ) ↔ n1 = n2 := by
  constructor
  · intro h_not
    by_cases h_eq : n1 = n2
    · exact h_eq
    · have h_iff :
          unify st (fuel + 1)
            (.tensor elem [Dim.var v, Dim.var v])
            (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
          ∃ s' : DimSubst,
            unifyDimList DimSubst.empty (fuel + 1)
              [Dim.var v, Dim.var v]
              [Dim.const n1, Dim.const n2] = some s' :=
        (tensor_rank2_same_var_const_ok_iff_dim_kernel_success_of_ne
          st fuel elem v n1 n2 h_eq)
      exact (h_not h_iff).elim
  · intro h_eq
    intro h_iff
    have h_ne : n1 ≠ n2 :=
      (tensor_rank2_same_var_const_ok_iff_dim_kernel_success_iff_ne
        st fuel elem v n1 n2).1 h_iff
    exact (h_ne h_eq).elim

/-- For rank-2 const-vs-repeated-var shapes, non-generalization of the naive
    `ok ↔ dim-kernel-success` contract occurs exactly when constants are equal. -/
theorem tensor_rank2_const_same_var_non_generalization_iff_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s'
    ) ↔ n1 = n2 := by
  constructor
  · intro h_not
    by_cases h_eq : n1 = n2
    · exact h_eq
    · have h_iff :
          unify st (fuel + 1)
            (.tensor elem [Dim.const n1, Dim.const n2])
            (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
          ∃ s' : DimSubst,
            unifyDimList DimSubst.empty (fuel + 1)
              [Dim.const n1, Dim.const n2]
              [Dim.var v, Dim.var v] = some s' :=
        (tensor_rank2_const_same_var_ok_iff_dim_kernel_success_of_ne
          st fuel elem n1 n2 v h_eq)
      exact (h_not h_iff).elim
  · intro h_eq
    intro h_iff
    have h_ne : n1 ≠ n2 :=
      (tensor_rank2_const_same_var_ok_iff_dim_kernel_success_iff_ne
        st fuel elem n1 n2 v).1 h_iff
    exact (h_ne h_eq).elim

/-- Packaged same-variable rank-2 non-generalization split:
    failure of naive `ok ↔ dim-kernel-success` contracts is exactly the
    equal-constants branch in both orientations. -/
theorem tensor_rank2_same_var_non_generalization_split_iff_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) :
    (¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s') ↔
      n1 = n2)
    ∧
    (¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s') ↔
      n1 = n2) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_same_var_const_non_generalization_iff_eq
      st fuel elem v n1 n2
  · exact tensor_rank2_const_same_var_non_generalization_iff_eq
      st fuel elem n1 n2 v

/-- Rank-2 var-vs-const mixed-shape non-generalization classified by shape
    variable equality: equal-vars case splits on constant equality, distinct-vars
    case is always non-generalizing. -/
theorem tensor_rank2_var_const_non_generalization_by_var_equality
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (v1 = v2 →
      (¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s') ↔
        n1 = n2))
    ∧
    (v1 ≠ v2 →
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s')) := by
  refine ⟨?_, ?_⟩
  · intro h_eq_vars
    subst h_eq_vars
    exact tensor_rank2_same_var_const_non_generalization_iff_eq
      st fuel elem v1 n1 n2
  · intro h_distinct
    intro h_iff
    have h_kernel :
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s' := by
      exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
        tensor_rank2_var_const_dim_kernel_success_distinct fuel v1 v2 n1 n2 h_distinct⟩
    have h_ok :
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st :=
      (h_iff.2 h_kernel)
    have h_shape :
        (([Dim.var v1, Dim.var v2] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
      simp [instBEqDim]
    have h_err := tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.var v1, Dim.var v2] [Dim.const n1, Dim.const n2] h_shape
    rw [h_ok] at h_err
    cases h_err

/-- Rank-2 const-vs-var mixed-shape non-generalization classified by shape
    variable equality: equal-vars case splits on constant equality, distinct-vars
    case is always non-generalizing. -/
theorem tensor_rank2_const_var_non_generalization_by_var_equality
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) :
    (v1 = v2 →
      (¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s') ↔
        n1 = n2))
    ∧
    (v1 ≠ v2 →
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s')) := by
  refine ⟨?_, ?_⟩
  · intro h_eq_vars
    subst h_eq_vars
    exact tensor_rank2_const_same_var_non_generalization_iff_eq
      st fuel elem n1 n2 v1
  · intro h_distinct
    intro h_iff
    have h_kernel :
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s' := by
      exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
        tensor_rank2_const_var_dim_kernel_success_distinct fuel n1 n2 v1 v2 h_distinct⟩
    have h_ok :
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st :=
      (h_iff.2 h_kernel)
    have h_shape :
        (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v1, Dim.var v2]) = false := by
      simp [instBEqDim]
    have h_err := tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.const n1, Dim.const n2] [Dim.var v1, Dim.var v2] h_shape
    rw [h_ok] at h_err
    cases h_err

/-- Packaged rank-2 mixed-shape non-generalization classification:
    each orientation splits by variable equality into an equal-vars
    equality-sensitive branch and a distinct-vars always-non-generalizing
    branch. -/
theorem tensor_rank2_mixed_non_generalization_by_var_equality_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (v1 = v2 →
      (¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s') ↔
        n1 = n2))
    ∧
    (v1 ≠ v2 →
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s'))
    ∧
    (v1 = v2 →
      (¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s') ↔
        n1 = n2))
    ∧
    (v1 ≠ v2 →
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s')) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (tensor_rank2_var_const_non_generalization_by_var_equality
      st fuel elem v1 v2 n1 n2).1
  · exact (tensor_rank2_var_const_non_generalization_by_var_equality
      st fuel elem v1 v2 n1 n2).2
  · exact (tensor_rank2_const_var_non_generalization_by_var_equality
      st fuel elem n1 n2 v1 v2).1
  · exact (tensor_rank2_const_var_non_generalization_by_var_equality
      st fuel elem n1 n2 v1 v2).2

/-- Rank-2 var-vs-const mixed-shape naive contract holds exactly when the two
    shape variables are equal and constants differ. -/
theorem tensor_rank2_var_const_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s') ↔
    (v1 = v2 ∧ n1 ≠ n2) := by
  constructor
  · intro h_contract
    by_cases h_eq_vars : v1 = v2
    · subst h_eq_vars
      refine ⟨rfl, ?_⟩
      exact (tensor_rank2_same_var_const_ok_iff_dim_kernel_success_iff_ne
        st fuel elem v1 n1 n2).1 h_contract
    · have h_not_contract :
          ¬ (
            unify st (fuel + 1)
              (.tensor elem [Dim.var v1, Dim.var v2])
              (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
            ∃ s' : DimSubst,
              unifyDimList DimSubst.empty (fuel + 1)
                [Dim.var v1, Dim.var v2]
                [Dim.const n1, Dim.const n2] = some s') :=
        (tensor_rank2_var_const_non_generalization_by_var_equality
          st fuel elem v1 v2 n1 n2).2 h_eq_vars
      exact (h_not_contract h_contract).elim
  · intro h_case
    rcases h_case with ⟨h_eq_vars, h_ne_consts⟩
    subst h_eq_vars
    exact (tensor_rank2_same_var_const_ok_iff_dim_kernel_success_iff_ne
      st fuel elem v1 n1 n2).2 h_ne_consts

/-- Rank-2 const-vs-var mixed-shape naive contract holds exactly when the two
    shape variables are equal and constants differ. -/
theorem tensor_rank2_const_var_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) :
    (unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') ↔
    (v1 = v2 ∧ n1 ≠ n2) := by
  constructor
  · intro h_contract
    by_cases h_eq_vars : v1 = v2
    · subst h_eq_vars
      refine ⟨rfl, ?_⟩
      exact (tensor_rank2_const_same_var_ok_iff_dim_kernel_success_iff_ne
        st fuel elem n1 n2 v1).1 h_contract
    · have h_not_contract :
          ¬ (
            unify st (fuel + 1)
              (.tensor elem [Dim.const n1, Dim.const n2])
              (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
            ∃ s' : DimSubst,
              unifyDimList DimSubst.empty (fuel + 1)
                [Dim.const n1, Dim.const n2]
                [Dim.var v1, Dim.var v2] = some s') :=
        (tensor_rank2_const_var_non_generalization_by_var_equality
          st fuel elem n1 n2 v1 v2).2 h_eq_vars
      exact (h_not_contract h_contract).elim
  · intro h_case
    rcases h_case with ⟨h_eq_vars, h_ne_consts⟩
    subst h_eq_vars
    exact (tensor_rank2_const_same_var_ok_iff_dim_kernel_success_iff_ne
      st fuel elem n1 n2 v1).2 h_ne_consts

/-- Packaged rank-2 mixed-shape positive classification:
    the naive contract `ok ↔ dim-kernel-success` holds exactly on the
    equal-vars + unequal-constants branch, in both orientations. -/
theorem tensor_rank2_mixed_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    ((unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s') ↔
      (v1 = v2 ∧ n1 ≠ n2))
    ∧
    ((unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') ↔
      (v1 = v2 ∧ n1 ≠ n2)) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_var_const_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_const_var_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
      st fuel elem n1 n2 v1 v2

/-- Rank-2 var-vs-const non-generalization is exactly the complement of the
    equal-vars + unequal-constants hold case. -/
theorem tensor_rank2_var_const_non_generalization_iff_not_var_eq_and_const_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s') ↔
    ¬ (v1 = v2 ∧ n1 ≠ n2) := by
  rw [tensor_rank2_var_const_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
    st fuel elem v1 v2 n1 n2]

/-- Rank-2 const-vs-var non-generalization is exactly the complement of the
    equal-vars + unequal-constants hold case. -/
theorem tensor_rank2_const_var_non_generalization_iff_not_var_eq_and_const_ne
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') ↔
    ¬ (v1 = v2 ∧ n1 ≠ n2) := by
  rw [tensor_rank2_const_var_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
    st fuel elem n1 n2 v1 v2]

/-- Packaged complement classification for rank-2 mixed shapes:
    non-generalization is exactly the complement of the equal-vars +
    unequal-constants branch, in both orientations. -/
theorem tensor_rank2_mixed_non_generalization_iff_not_var_eq_and_const_ne_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s') ↔
      ¬ (v1 = v2 ∧ n1 ≠ n2))
    ∧
    (¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') ↔
      ¬ (v1 = v2 ∧ n1 ≠ n2)) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_var_const_non_generalization_iff_not_var_eq_and_const_ne
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_const_var_non_generalization_iff_not_var_eq_and_const_ne
      st fuel elem n1 n2 v1 v2

/-- Rank-2 var-vs-const divergence witness (`dim-kernel success` + constructor
    rejection) exists exactly when variables are distinct or constants agree. -/
theorem tensor_rank2_var_const_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2]
        [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
    (v1 ≠ v2 ∨ n1 = n2) := by
  have h_unify_err :
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch" := by
    have h_shape :
        (([Dim.var v1, Dim.var v2] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
      simp [instBEqDim]
    exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.var v1, Dim.var v2] [Dim.const n1, Dim.const n2] h_shape
  constructor
  · intro h
    rcases h with ⟨s', h_kernel, _h_unify⟩
    exact (tensor_rank2_var_const_dim_kernel_some_iff_var_distinct_or_consts_eq fuel v1 v2 n1 n2).1
      ⟨s', h_kernel⟩
  · intro h_case
    rcases (tensor_rank2_var_const_dim_kernel_some_iff_var_distinct_or_consts_eq fuel v1 v2 n1 n2).2 h_case with
      ⟨s', h_kernel⟩
    exact ⟨s', h_kernel, h_unify_err⟩

/-- Rank-2 const-vs-var divergence witness (`dim-kernel success` + constructor
    rejection) exists exactly when variables are distinct or constants agree. -/
theorem tensor_rank2_const_var_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v1, Dim.var v2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") ↔
    (v1 ≠ v2 ∨ n1 = n2) := by
  have h_unify_err :
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch" := by
    have h_shape :
        (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v1, Dim.var v2]) = false := by
      simp [instBEqDim]
    exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.const n1, Dim.const n2] [Dim.var v1, Dim.var v2] h_shape
  constructor
  · intro h
    rcases h with ⟨s', h_kernel, _h_unify⟩
    exact (tensor_rank2_const_var_dim_kernel_some_iff_var_distinct_or_consts_eq fuel n1 n2 v1 v2).1
      ⟨s', h_kernel⟩
  · intro h_case
    rcases (tensor_rank2_const_var_dim_kernel_some_iff_var_distinct_or_consts_eq fuel n1 n2 v1 v2).2 h_case with
      ⟨s', h_kernel⟩
    exact ⟨s', h_kernel, h_unify_err⟩

/-- Packaged rank-2 mixed divergence-witness classification:
    `dim-kernel success` + constructor rejection witnesses exist exactly on
    the (distinct-vars OR equal-constants) branch in both orientations. -/
theorem tensor_rank2_mixed_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
      (v1 ≠ v2 ∨ n1 = n2))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") ↔
      (v1 ≠ v2 ∨ n1 = n2)) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_var_const_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_const_var_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq
      st fuel elem n1 n2 v1 v2

/-- Rank-2 var-vs-const divergence witness exists exactly when the naive
    `ok ↔ dim-kernel-success` contract fails. -/
theorem tensor_rank2_var_const_divergence_iff_not_naive_contract
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2]
        [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s') := by
  let contract :=
    (unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s')
  have h_div :
      (∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
      (v1 ≠ v2 ∨ n1 = n2) :=
    tensor_rank2_var_const_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq
      st fuel elem v1 v2 n1 n2
  have h_contract :
      contract ↔ (v1 = v2 ∧ n1 ≠ n2) :=
    tensor_rank2_var_const_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
      st fuel elem v1 v2 n1 n2
  have h_logic :
      (v1 ≠ v2 ∨ n1 = n2) ↔ ¬ (v1 = v2 ∧ n1 ≠ n2) := by
    constructor
    · intro h
      intro h_case
      rcases h_case with ⟨h_eq_vars, h_ne_consts⟩
      cases h with
      | inl h_distinct =>
          exact (h_distinct h_eq_vars).elim
      | inr h_eq_consts =>
          exact (h_ne_consts h_eq_consts).elim
    · intro h_not
      by_cases h_eq_vars : v1 = v2
      · right
        by_cases h_eq_consts : n1 = n2
        · exact h_eq_consts
        · exact (h_not ⟨h_eq_vars, h_eq_consts⟩).elim
      · left
        exact h_eq_vars
  have h_not_contract :
      ¬ (v1 = v2 ∧ n1 ≠ n2) ↔ ¬ contract := by
    constructor
    · intro h_not_case
      intro h_contract_true
      exact h_not_case (h_contract.1 h_contract_true)
    · intro h_not_contract_true
      intro h_case
      exact h_not_contract_true (h_contract.2 h_case)
  exact h_div.trans (h_logic.trans h_not_contract)

/-- Rank-2 const-vs-var divergence witness exists exactly when the naive
    `ok ↔ dim-kernel-success` contract fails. -/
theorem tensor_rank2_const_var_divergence_iff_not_naive_contract
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v1, Dim.var v2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') := by
  let contract :=
    (unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s')
  have h_div :
      (∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") ↔
      (v1 ≠ v2 ∨ n1 = n2) :=
    tensor_rank2_const_var_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq
      st fuel elem n1 n2 v1 v2
  have h_contract :
      contract ↔ (v1 = v2 ∧ n1 ≠ n2) :=
    tensor_rank2_const_var_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne
      st fuel elem n1 n2 v1 v2
  have h_logic :
      (v1 ≠ v2 ∨ n1 = n2) ↔ ¬ (v1 = v2 ∧ n1 ≠ n2) := by
    constructor
    · intro h
      intro h_case
      rcases h_case with ⟨h_eq_vars, h_ne_consts⟩
      cases h with
      | inl h_distinct =>
          exact (h_distinct h_eq_vars).elim
      | inr h_eq_consts =>
          exact (h_ne_consts h_eq_consts).elim
    · intro h_not
      by_cases h_eq_vars : v1 = v2
      · right
        by_cases h_eq_consts : n1 = n2
        · exact h_eq_consts
        · exact (h_not ⟨h_eq_vars, h_eq_consts⟩).elim
      · left
        exact h_eq_vars
  have h_not_contract :
      ¬ (v1 = v2 ∧ n1 ≠ n2) ↔ ¬ contract := by
    constructor
    · intro h_not_case
      intro h_contract_true
      exact h_not_case (h_contract.1 h_contract_true)
    · intro h_not_contract_true
      intro h_case
      exact h_not_contract_true (h_contract.2 h_case)
  exact h_div.trans (h_logic.trans h_not_contract)

/-- Packaged rank-2 mixed divergence-vs-contract relation:
    divergence witnesses exist exactly when the naive mixed contracts fail,
    in both orientations. -/
theorem tensor_rank2_mixed_divergence_iff_not_naive_contract_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s')) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_var_const_divergence_iff_not_naive_contract
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_const_var_divergence_iff_not_naive_contract
      st fuel elem n1 n2 v1 v2

/-- Packaged rank-2 mixed dim-aware classification layer bundling:
    non-generalization-by-var-equality, positive hold classification,
    divergence-witness classification, and divergence-vs-contract-failure
    equivalence for both var/const orientations. -/
structure TensorRank2MixedDimKernelClassificationSlice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) : Prop where
  nonGeneralizationByVarEquality :
    tensor_rank2_mixed_non_generalization_by_var_equality_slice
      st fuel elem v1 v2 n1 n2
  okIffVarEqAndConstNe :
    tensor_rank2_mixed_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne_slice
      st fuel elem v1 v2 n1 n2
  divergenceWitnessIffVarDistinctOrConstsEq :
    tensor_rank2_mixed_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq_slice
      st fuel elem v1 v2 n1 n2
  divergenceIffNotNaiveContract :
    tensor_rank2_mixed_divergence_iff_not_naive_contract_slice
      st fuel elem v1 v2 n1 n2

/-- Canonical witness for the packaged rank-2 mixed dim-aware classification
surface. -/
theorem tensorRank2MixedDimKernelClassificationSlice_proved
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2 := by
  refine
    { nonGeneralizationByVarEquality := ?_
      okIffVarEqAndConstNe := ?_
      divergenceWitnessIffVarDistinctOrConstsEq := ?_
      divergenceIffNotNaiveContract := ?_ }
  · exact tensor_rank2_mixed_non_generalization_by_var_equality_slice
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_mixed_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne_slice
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_mixed_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq_slice
      st fuel elem v1 v2 n1 n2
  · exact tensor_rank2_mixed_divergence_iff_not_naive_contract_slice
      st fuel elem v1 v2 n1 n2

/-- Explicit component tuple alias for `TensorRank2MixedDimKernelClassificationSlice`. -/
abbrev TensorRank2MixedDimKernelClassificationSliceComponents
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) : Prop :=
  tensor_rank2_mixed_non_generalization_by_var_equality_slice
      st fuel elem v1 v2 n1 n2 ∧
  tensor_rank2_mixed_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne_slice
      st fuel elem v1 v2 n1 n2 ∧
  tensor_rank2_mixed_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq_slice
      st fuel elem v1 v2 n1 n2 ∧
  tensor_rank2_mixed_divergence_iff_not_naive_contract_slice
      st fuel elem v1 v2 n1 n2

/-- Decompose the packaged rank-2 mixed dim-aware slice into explicit
components. -/
theorem tensorRank2MixedDimKernelClassificationSlice_as_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (slice : TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2) :
    TensorRank2MixedDimKernelClassificationSliceComponents
      st fuel elem v1 v2 n1 n2 :=
  ⟨slice.nonGeneralizationByVarEquality,
    slice.okIffVarEqAndConstNe,
    slice.divergenceWitnessIffVarDistinctOrConstsEq,
    slice.divergenceIffNotNaiveContract⟩

/-- Build the packaged rank-2 mixed dim-aware slice from explicit components. -/
theorem tensorRank2MixedDimKernelClassificationSlice_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_nonGen :
      tensor_rank2_mixed_non_generalization_by_var_equality_slice
        st fuel elem v1 v2 n1 n2)
    (h_ok :
      tensor_rank2_mixed_ok_iff_dim_kernel_success_iff_var_eq_and_const_ne_slice
        st fuel elem v1 v2 n1 n2)
    (h_divWitness :
      tensor_rank2_mixed_kernel_success_but_unify_rejects_iff_var_distinct_or_consts_eq_slice
        st fuel elem v1 v2 n1 n2)
    (h_divIff :
      tensor_rank2_mixed_divergence_iff_not_naive_contract_slice
        st fuel elem v1 v2 n1 n2) :
    TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2 :=
  { nonGeneralizationByVarEquality := h_nonGen
    okIffVarEqAndConstNe := h_ok
    divergenceWitnessIffVarDistinctOrConstsEq := h_divWitness
    divergenceIffNotNaiveContract := h_divIff }

/-- Direct components-route decomposition for
`TensorRank2MixedDimKernelClassificationSlice`. -/
theorem tensorRank2MixedDimKernelClassificationSlice_as_components_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_comp : TensorRank2MixedDimKernelClassificationSliceComponents
      st fuel elem v1 v2 n1 n2) :
    TensorRank2MixedDimKernelClassificationSliceComponents
      st fuel elem v1 v2 n1 n2 := by
  simpa using h_comp

/-- `TensorRank2MixedDimKernelClassificationSlice` is equivalent to its explicit
component tuple. -/
theorem tensorRank2MixedDimKernelClassificationSlice_iff_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2 ↔
      TensorRank2MixedDimKernelClassificationSliceComponents
        st fuel elem v1 v2 n1 n2 := by
  constructor
  · intro slice
    exact tensorRank2MixedDimKernelClassificationSlice_as_components
      st fuel elem v1 v2 n1 n2 slice
  · intro h
    rcases h with ⟨h_nonGen, h_ok, h_divWitness, h_divIff⟩
    exact tensorRank2MixedDimKernelClassificationSlice_of_components
      st fuel elem v1 v2 n1 n2 h_nonGen h_ok h_divWitness h_divIff

/-- Current constructor-level tensor unifier rejects rank-2 const-vs-repeated-var
    shapes even when pointwise dim-kernel succeeds (equal-constants case). -/
theorem tensor_rank2_const_same_var_kernel_success_but_unify_rejects_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) (h_eq : n1 = n2) :
    ∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v, Dim.var v] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .err "type mismatch" := by
  refine ⟨DimSubst.extend DimSubst.empty v (.const n1), ?_, ?_⟩
  · exact tensor_rank2_const_same_var_dim_kernel_success_of_eq fuel n1 n2 v h_eq
  · have h_shape :
        (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v, Dim.var v]) = false := by
      simp [instBEqDim]
    exact tensor_shape_mismatch_any_elem_any_fuel st fuel elem
      [Dim.const n1, Dim.const n2] [Dim.var v, Dim.var v] h_shape

/-- Packaged mixed-shape boundary witness: for fixed-size-list and tensor
    (rank-1 and rank-2), pointwise dim kernels can succeed via var/const
    bindings while current constructor-level shape unifier branches still
    reject. -/
theorem mixed_shape_kernel_boundary_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2) :
    (∃ s' : DimSubst,
      unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s' ∧
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .err "type mismatch")
    ∧ (∃ s' : DimSubst,
      unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s' ∧
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .err "type mismatch")
    ∧ (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v] [Dim.const n] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .err "type mismatch")
    ∧ (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n] [Dim.var v] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .err "type mismatch")
    ∧ (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2] [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch")
    ∧ (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2] [Dim.var v1, Dim.var v2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fixedSizeList_var_const_kernel_success_but_unify_rejects st fuel elem v n
  · exact fixedSizeList_const_var_kernel_success_but_unify_rejects st fuel elem n v
  · exact tensor_rank1_var_const_kernel_success_but_unify_rejects st fuel elem v n
  · exact tensor_rank1_const_var_kernel_success_but_unify_rejects st fuel elem n v
  · exact tensor_rank2_var_const_kernel_success_but_unify_rejects_distinct
      st fuel elem v1 v2 n1 n2 h_distinct
  · exact tensor_rank2_const_var_kernel_success_but_unify_rejects_distinct
      st fuel elem n1 n2 v1 v2 h_distinct

/-- Packaged rank-2 same-variable mixed-shape boundary witness:
    dim-kernel success on equal-constants repeated-var shapes coexists with
    constructor-level rejection in both orientations. -/
theorem tensor_rank2_same_var_kernel_boundary_slice_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v, Dim.var v]
        [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch")
    ∧ (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v, Dim.var v] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .err "type mismatch") := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_same_var_const_kernel_success_but_unify_rejects_of_eq
      st fuel elem v n1 n2 h_eq
  · exact tensor_rank2_const_same_var_kernel_success_but_unify_rejects_of_eq
      st fuel elem n1 n2 v h_eq

/-- Mixed fixed-size-list var/const dimensions are a counterexample to lifting
    the constant-shape `ok ↔ dim-kernel-success` contract naively. -/
theorem fixedSizeList_var_const_not_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    ¬ (
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s' := by
    exact ⟨DimSubst.extend DimSubst.empty v (.const n),
      fixedSizeList_var_const_dim_kernel_success fuel v n⟩
  have h_ok :
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .ok st :=
    (h_iff.2 h_kernel)
  have h_err := fixedSizeList_var_const_dim_mismatch_any_elem_any_fuel st fuel elem v n
  rw [h_ok] at h_err
  cases h_err

/-- Mixed fixed-size-list const/var dimensions are also a counterexample to
    lifting the constant-shape `ok ↔ dim-kernel-success` contract naively. -/
theorem fixedSizeList_const_var_not_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    ¬ (
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s' := by
    exact ⟨DimSubst.extend DimSubst.empty v (.const n),
      fixedSizeList_const_var_dim_kernel_success fuel n v⟩
  have h_ok :
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .ok st :=
    (h_iff.2 h_kernel)
  have h_err := fixedSizeList_const_var_dim_mismatch_any_elem_any_fuel st fuel elem n v
  rw [h_ok] at h_err
  cases h_err

/-- Mixed rank-1 tensor var/const shapes are a counterexample to lifting the
    constant-shape `ok ↔ dim-kernel-success` contract naively. -/
theorem tensor_rank1_var_const_not_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v] [Dim.const n] = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v] [Dim.const n] = some s' := by
    exact ⟨DimSubst.extend DimSubst.empty v (.const n),
      tensor_rank1_var_const_dim_kernel_success fuel v n⟩
  have h_ok :
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .ok st :=
    (h_iff.2 h_kernel)
  have h_err := tensor_rank1_var_const_shape_mismatch_any_elem_any_fuel st fuel elem v n
  rw [h_ok] at h_err
  cases h_err

/-- Mixed rank-1 tensor const/var shapes are also a counterexample to lifting
    constant-shape `ok ↔ dim-kernel-success` naively. -/
theorem tensor_rank1_const_var_not_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n] [Dim.var v] = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n] [Dim.var v] = some s' := by
    exact ⟨DimSubst.extend DimSubst.empty v (.const n),
      tensor_rank1_const_var_dim_kernel_success fuel n v⟩
  have h_ok :
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .ok st :=
    (h_iff.2 h_kernel)
  have h_err := tensor_rank1_const_var_shape_mismatch_any_elem_any_fuel st fuel elem n v
  rw [h_ok] at h_err
  cases h_err

/-- Mixed fixed-size-list var-vs-const divergence witness exists exactly when
    the naive `ok ↔ dim-kernel-success` contract fails. -/
theorem fixedSizeList_var_const_divergence_iff_not_naive_contract
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    (∃ s' : DimSubst,
      unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s' ∧
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s') := by
  constructor
  · intro _
    exact fixedSizeList_var_const_not_ok_iff_dim_kernel_success st fuel elem v n
  · intro _
    exact fixedSizeList_var_const_kernel_success_but_unify_rejects st fuel elem v n

/-- Mixed fixed-size-list const-vs-var divergence witness exists exactly when
    the naive `ok ↔ dim-kernel-success` contract fails. -/
theorem fixedSizeList_const_var_divergence_iff_not_naive_contract
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    (∃ s' : DimSubst,
      unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s' ∧
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s') := by
  constructor
  · intro _
    exact fixedSizeList_const_var_not_ok_iff_dim_kernel_success st fuel elem n v
  · intro _
    exact fixedSizeList_const_var_kernel_success_but_unify_rejects st fuel elem n v

/-- Mixed rank-1 tensor var-vs-const divergence witness exists exactly when
    the naive `ok ↔ dim-kernel-success` contract fails. -/
theorem tensor_rank1_var_const_divergence_iff_not_naive_contract
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v] [Dim.const n] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v] [Dim.const n] = some s') := by
  constructor
  · intro _
    exact tensor_rank1_var_const_not_ok_iff_dim_kernel_success st fuel elem v n
  · intro _
    exact tensor_rank1_var_const_kernel_success_but_unify_rejects st fuel elem v n

/-- Mixed rank-1 tensor const-vs-var divergence witness exists exactly when
    the naive `ok ↔ dim-kernel-success` contract fails. -/
theorem tensor_rank1_const_var_divergence_iff_not_naive_contract
    (st : UnifyState) (fuel : Nat) (elem : Ty) (n : Nat) (v : DimVarId) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n] [Dim.var v] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n] [Dim.var v] = some s') := by
  constructor
  · intro _
    exact tensor_rank1_const_var_not_ok_iff_dim_kernel_success st fuel elem n v
  · intro _
    exact tensor_rank1_const_var_kernel_success_but_unify_rejects st fuel elem n v

/-- Packaged mixed-shape rank-1/fixed-size-list divergence-vs-contract relation:
    each mixed orientation has a divergence witness exactly when the naive
    mixed contract fails. -/
theorem mixed_shape_rank1_divergence_iff_not_naive_contract_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty) (v : DimVarId) (n : Nat) :
    ((∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s' ∧
        unify st (fuel + 1)
          (.fixedSizeList elem (.var v))
          (.fixedSizeList elem (.const n)) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.fixedSizeList elem (.var v))
          (.fixedSizeList elem (.const n)) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s' ∧
        unify st (fuel + 1)
          (.fixedSizeList elem (.const n))
          (.fixedSizeList elem (.var v)) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.fixedSizeList elem (.const n))
          (.fixedSizeList elem (.var v)) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v] [Dim.const n] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v])
          (.tensor elem [Dim.const n]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v])
          (.tensor elem [Dim.const n]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v] [Dim.const n] = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n] [Dim.var v] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n])
          (.tensor elem [Dim.var v]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n])
          (.tensor elem [Dim.var v]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n] [Dim.var v] = some s')) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fixedSizeList_var_const_divergence_iff_not_naive_contract st fuel elem v n
  · exact fixedSizeList_const_var_divergence_iff_not_naive_contract st fuel elem n v
  · exact tensor_rank1_var_const_divergence_iff_not_naive_contract st fuel elem v n
  · exact tensor_rank1_const_var_divergence_iff_not_naive_contract st fuel elem n v

/-- Packaged mixed-shape divergence-vs-contract-failure slice across
    fixed-size-list, rank-1 tensor, and rank-2 tensor mixed var/const
    orientations. -/
theorem mixed_shape_divergence_iff_not_naive_contract_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat) :
    ((∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s' ∧
        unify st (fuel + 1)
          (.fixedSizeList elem (.var v))
          (.fixedSizeList elem (.const n)) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.fixedSizeList elem (.var v))
          (.fixedSizeList elem (.const n)) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s' ∧
        unify st (fuel + 1)
          (.fixedSizeList elem (.const n))
          (.fixedSizeList elem (.var v)) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.fixedSizeList elem (.const n))
          (.fixedSizeList elem (.var v)) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v] [Dim.const n] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v])
          (.tensor elem [Dim.const n]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v])
          (.tensor elem [Dim.const n]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v] [Dim.const n] = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n] [Dim.var v] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n])
          (.tensor elem [Dim.var v]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n])
          (.tensor elem [Dim.var v]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n] [Dim.var v] = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v1, Dim.var v2])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] = some s')) := by
  have h_rank1 := mixed_shape_rank1_divergence_iff_not_naive_contract_slice st fuel elem v n
  have h_rank2 := tensor_rank2_mixed_divergence_iff_not_naive_contract_slice
    st fuel elem v1 v2 n1 n2
  refine ⟨h_rank1.1, ?_⟩
  refine ⟨h_rank1.2.1, ?_⟩
  refine ⟨h_rank1.2.2.1, ?_⟩
  refine ⟨h_rank1.2.2.2, ?_⟩
  refine ⟨h_rank2.1, ?_⟩
  exact h_rank2.2

/-- Mixed rank-2 tensor var/const shapes (distinct vars) are a counterexample
    to lifting the constant-shape `ok ↔ dim-kernel-success` contract naively. -/
theorem tensor_rank2_var_const_not_ok_iff_dim_kernel_success_distinct
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v1 v2 : DimVarId) (n1 n2 : Nat) (h_distinct : v1 ≠ v2) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s' := by
    exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
      tensor_rank2_var_const_dim_kernel_success_distinct fuel v1 v2 n1 n2 h_distinct⟩
  have h_ok :
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st :=
    (h_iff.2 h_kernel)
  have h_shape :
      (([Dim.var v1, Dim.var v2] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
    simp [instBEqDim]
  have h_err := tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.var v1, Dim.var v2] [Dim.const n1, Dim.const n2] h_shape
  rw [h_ok] at h_err
  cases h_err

/-- Mixed rank-2 tensor const/var shapes (distinct vars) are also a
    counterexample to lifting `ok ↔ dim-kernel-success` naively. -/
theorem tensor_rank2_const_var_not_ok_iff_dim_kernel_success_distinct
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v1 v2 : DimVarId) (h_distinct : v1 ≠ v2) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s' := by
    exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
      tensor_rank2_const_var_dim_kernel_success_distinct fuel n1 n2 v1 v2 h_distinct⟩
  have h_ok :
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st :=
    (h_iff.2 h_kernel)
  have h_shape :
      (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v1, Dim.var v2]) = false := by
    simp [instBEqDim]
  have h_err := tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.const n1, Dim.const n2] [Dim.var v1, Dim.var v2] h_shape
  rw [h_ok] at h_err
  cases h_err

/-- Mixed rank-2 tensor repeated-var/const shapes (equal constants) are a
    counterexample to lifting `ok ↔ dim-kernel-success` naively. -/
theorem tensor_rank2_same_var_const_not_ok_iff_dim_kernel_success_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s' := by
    exact ⟨DimSubst.extend DimSubst.empty v (.const n1),
      tensor_rank2_same_var_const_dim_kernel_success_of_eq fuel v n1 n2 h_eq⟩
  have h_ok :
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st :=
    (h_iff.2 h_kernel)
  have h_shape :
      (([Dim.var v, Dim.var v] : List Dim) == [Dim.const n1, Dim.const n2]) = false := by
    simp [instBEqDim]
  have h_err := tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.var v, Dim.var v] [Dim.const n1, Dim.const n2] h_shape
  rw [h_ok] at h_err
  cases h_err

/-- Mixed rank-2 tensor const/repeated-var shapes (equal constants) are also a
    counterexample to lifting `ok ↔ dim-kernel-success` naively. -/
theorem tensor_rank2_const_same_var_not_ok_iff_dim_kernel_success_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) (h_eq : n1 = n2) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s'
    ) := by
  intro h_iff
  have h_kernel :
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s' := by
    exact ⟨DimSubst.extend DimSubst.empty v (.const n1),
      tensor_rank2_const_same_var_dim_kernel_success_of_eq fuel n1 n2 v h_eq⟩
  have h_ok :
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st :=
    (h_iff.2 h_kernel)
  have h_shape :
      (([Dim.const n1, Dim.const n2] : List Dim) == [Dim.var v, Dim.var v]) = false := by
    simp [instBEqDim]
  have h_err := tensor_shape_mismatch_any_elem_any_fuel st fuel elem
    [Dim.const n1, Dim.const n2] [Dim.var v, Dim.var v] h_shape
  rw [h_ok] at h_err
  cases h_err

/-- On equal-constants repeated-var rank-2 shapes, a divergence witness exists
    exactly when the naive `ok ↔ dim-kernel-success` contract fails
    (var-vs-const orientation). -/
theorem tensor_rank2_same_var_const_divergence_iff_not_naive_contract_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v, Dim.var v]
        [Dim.const n1, Dim.const n2] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s') := by
  constructor
  · intro _
    exact tensor_rank2_same_var_const_not_ok_iff_dim_kernel_success_of_eq
      st fuel elem v n1 n2 h_eq
  · intro _
    exact tensor_rank2_same_var_const_kernel_success_but_unify_rejects_of_eq
      st fuel elem v n1 n2 h_eq

/-- On equal-constants repeated-var rank-2 shapes, a divergence witness exists
    exactly when the naive `ok ↔ dim-kernel-success` contract fails
    (const-vs-var orientation). -/
theorem tensor_rank2_const_same_var_divergence_iff_not_naive_contract_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (n1 n2 : Nat) (v : DimVarId) (h_eq : n1 = n2) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v, Dim.var v] = some s' ∧
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .err "type mismatch") ↔
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s') := by
  constructor
  · intro _
    exact tensor_rank2_const_same_var_not_ok_iff_dim_kernel_success_of_eq
      st fuel elem n1 n2 v h_eq
  · intro _
    exact tensor_rank2_const_same_var_kernel_success_but_unify_rejects_of_eq
      st fuel elem n1 n2 v h_eq

/-- Packaged equal-constants repeated-var rank-2 divergence-vs-contract
    equivalence across both mixed orientations. -/
theorem tensor_rank2_same_var_divergence_iff_not_naive_contract_slice_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.var v, Dim.var v])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.var v, Dim.var v])
          (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v, Dim.var v]
            [Dim.const n1, Dim.const n2] = some s'))
    ∧
    ((∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s' ∧
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v, Dim.var v]) = .err "type mismatch") ↔
      ¬ (
        unify st (fuel + 1)
          (.tensor elem [Dim.const n1, Dim.const n2])
          (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
        ∃ s' : DimSubst,
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v, Dim.var v] = some s')) := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_same_var_const_divergence_iff_not_naive_contract_of_eq
      st fuel elem v n1 n2 h_eq
  · exact tensor_rank2_const_same_var_divergence_iff_not_naive_contract_of_eq
      st fuel elem n1 n2 v h_eq

/-- Packaged non-generalization boundary: constant-shape `ok ↔ dim-kernel`
    contracts do not extend naively to mixed var/const metadata for
    fixed-size-list and tensor (rank-1 and rank-2 distinct-vars cases). -/
theorem mixed_shape_non_generalization_slice
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat) (h_distinct : v1 ≠ v2) :
    ¬ (
      unify st (fuel + 1)
        (.fixedSizeList elem (.var v))
        (.fixedSizeList elem (.const n)) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) = some s')
    ∧ ¬ (
      unify st (fuel + 1)
        (.fixedSizeList elem (.const n))
        (.fixedSizeList elem (.var v)) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) = some s')
    ∧ ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v])
        (.tensor elem [Dim.const n]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v] [Dim.const n] = some s')
    ∧ ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n])
        (.tensor elem [Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n] [Dim.var v] = some s')
    ∧ ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v1, Dim.var v2])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v1, Dim.var v2]
          [Dim.const n1, Dim.const n2] = some s')
    ∧ ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v1, Dim.var v2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v1, Dim.var v2] = some s') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fixedSizeList_var_const_not_ok_iff_dim_kernel_success st fuel elem v n
  · exact fixedSizeList_const_var_not_ok_iff_dim_kernel_success st fuel elem n v
  · exact tensor_rank1_var_const_not_ok_iff_dim_kernel_success st fuel elem v n
  · exact tensor_rank1_const_var_not_ok_iff_dim_kernel_success st fuel elem n v
  · exact tensor_rank2_var_const_not_ok_iff_dim_kernel_success_distinct
      st fuel elem v1 v2 n1 n2 h_distinct
  · exact tensor_rank2_const_var_not_ok_iff_dim_kernel_success_distinct
      st fuel elem n1 n2 v1 v2 h_distinct

/-- Packaged rank-2 same-variable non-generalization boundary:
    equal-constants repeated-var mixed shapes still invalidate naive
    `ok ↔ dim-kernel-success` lifting in both orientations. -/
theorem tensor_rank2_same_var_non_generalization_slice_of_eq
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.var v, Dim.var v])
        (.tensor elem [Dim.const n1, Dim.const n2]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.var v, Dim.var v]
          [Dim.const n1, Dim.const n2] = some s')
    ∧ ¬ (
      unify st (fuel + 1)
        (.tensor elem [Dim.const n1, Dim.const n2])
        (.tensor elem [Dim.var v, Dim.var v]) = .ok st ↔
      ∃ s' : DimSubst,
        unifyDimList DimSubst.empty (fuel + 1)
          [Dim.const n1, Dim.const n2]
          [Dim.var v, Dim.var v] = some s') := by
  refine ⟨?_, ?_⟩
  · exact tensor_rank2_same_var_const_not_ok_iff_dim_kernel_success_of_eq
      st fuel elem v n1 n2 h_eq
  · exact tensor_rank2_const_same_var_not_ok_iff_dim_kernel_success_of_eq
      st fuel elem n1 n2 v h_eq

/-- Packaged equal-constants repeated-var rank-2 boundary suite combining:
    kernel-boundary witnesses, divergence-vs-contract equivalence, and direct
    non-generalization across both mixed orientations. -/
structure TensorRank2SameVarEqBoundarySuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) : Prop where
  kernelBoundary :
    tensor_rank2_same_var_kernel_boundary_slice_of_eq
      st fuel elem v n1 n2 h_eq
  divergenceIffNotNaiveContract :
    tensor_rank2_same_var_divergence_iff_not_naive_contract_slice_of_eq
      st fuel elem v n1 n2 h_eq
  nonGeneralization :
    tensor_rank2_same_var_non_generalization_slice_of_eq
      st fuel elem v n1 n2 h_eq

/-- Canonical witness for the equal-constants repeated-var rank-2 boundary
suite package. -/
theorem tensorRank2SameVarEqBoundarySuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    TensorRank2SameVarEqBoundarySuite st fuel elem v n1 n2 h_eq := by
  refine
    { kernelBoundary := ?_
      divergenceIffNotNaiveContract := ?_
      nonGeneralization := ?_ }
  · exact tensor_rank2_same_var_kernel_boundary_slice_of_eq
      st fuel elem v n1 n2 h_eq
  · exact tensor_rank2_same_var_divergence_iff_not_naive_contract_slice_of_eq
      st fuel elem v n1 n2 h_eq
  · exact tensor_rank2_same_var_non_generalization_slice_of_eq
      st fuel elem v n1 n2 h_eq

/-- Explicit component tuple alias for `TensorRank2SameVarEqBoundarySuite`. -/
abbrev TensorRank2SameVarEqBoundarySuiteComponents
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) : Prop :=
  tensor_rank2_same_var_kernel_boundary_slice_of_eq
      st fuel elem v n1 n2 h_eq ∧
  tensor_rank2_same_var_divergence_iff_not_naive_contract_slice_of_eq
      st fuel elem v n1 n2 h_eq ∧
  tensor_rank2_same_var_non_generalization_slice_of_eq
      st fuel elem v n1 n2 h_eq

/-- Decompose `TensorRank2SameVarEqBoundarySuite` into explicit components. -/
theorem tensorRank2SameVarEqBoundarySuite_as_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2)
    (suite : TensorRank2SameVarEqBoundarySuite st fuel elem v n1 n2 h_eq) :
    TensorRank2SameVarEqBoundarySuiteComponents
      st fuel elem v n1 n2 h_eq :=
  ⟨suite.kernelBoundary, suite.divergenceIffNotNaiveContract, suite.nonGeneralization⟩

/-- Build `TensorRank2SameVarEqBoundarySuite` from explicit components. -/
theorem tensorRank2SameVarEqBoundarySuite_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2)
    (h_kernel :
      tensor_rank2_same_var_kernel_boundary_slice_of_eq
        st fuel elem v n1 n2 h_eq)
    (h_div :
      tensor_rank2_same_var_divergence_iff_not_naive_contract_slice_of_eq
        st fuel elem v n1 n2 h_eq)
    (h_nonGen :
      tensor_rank2_same_var_non_generalization_slice_of_eq
        st fuel elem v n1 n2 h_eq) :
    TensorRank2SameVarEqBoundarySuite st fuel elem v n1 n2 h_eq :=
  { kernelBoundary := h_kernel
    divergenceIffNotNaiveContract := h_div
    nonGeneralization := h_nonGen }

/-- Direct component-route decomposition for
`TensorRank2SameVarEqBoundarySuite`. -/
theorem tensorRank2SameVarEqBoundarySuite_as_components_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2)
    (h_comp : TensorRank2SameVarEqBoundarySuiteComponents
      st fuel elem v n1 n2 h_eq) :
    TensorRank2SameVarEqBoundarySuiteComponents
      st fuel elem v n1 n2 h_eq := by
  simpa using h_comp

/-- `TensorRank2SameVarEqBoundarySuite` is equivalent to its explicit component
tuple. -/
theorem tensorRank2SameVarEqBoundarySuite_iff_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    TensorRank2SameVarEqBoundarySuite st fuel elem v n1 n2 h_eq ↔
      TensorRank2SameVarEqBoundarySuiteComponents
        st fuel elem v n1 n2 h_eq := by
  constructor
  · intro suite
    exact tensorRank2SameVarEqBoundarySuite_as_components
      st fuel elem v n1 n2 h_eq suite
  · intro h
    rcases h with ⟨h_kernel, h_div, h_nonGen⟩
    exact tensorRank2SameVarEqBoundarySuite_of_components
      st fuel elem v n1 n2 h_eq h_kernel h_div h_nonGen

/-- Packaged distinct-vars mixed-shape dim-kernel boundary suite combining:
    witness-level kernel-vs-constructor mismatch, divergence-vs-contract
    equivalence, and direct non-generalization across fixed-size-list, rank-1
    tensor, and rank-2 tensor mixed var/const routes. -/
structure MixedShapeVarConstBoundarySuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2) : Prop where
  kernelBoundary :
    mixed_shape_kernel_boundary_slice
      st fuel elem v n v1 v2 n1 n2 h_distinct
  divergenceIffNotNaiveContract :
    mixed_shape_divergence_iff_not_naive_contract_slice
      st fuel elem v n v1 v2 n1 n2
  nonGeneralization :
    mixed_shape_non_generalization_slice
      st fuel elem v n v1 v2 n1 n2 h_distinct

/-- Canonical witness for the packaged distinct-vars mixed-shape boundary
suite. -/
theorem mixedShapeVarConstBoundarySuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2) :
    MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct := by
  refine
    { kernelBoundary := ?_
      divergenceIffNotNaiveContract := ?_
      nonGeneralization := ?_ }
  · exact mixed_shape_kernel_boundary_slice
      st fuel elem v n v1 v2 n1 n2 h_distinct
  · exact mixed_shape_divergence_iff_not_naive_contract_slice
      st fuel elem v n v1 v2 n1 n2
  · exact mixed_shape_non_generalization_slice
      st fuel elem v n v1 v2 n1 n2 h_distinct

/-- Explicit component tuple alias for `MixedShapeVarConstBoundarySuite`. -/
abbrev MixedShapeVarConstBoundarySuiteComponents
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2) : Prop :=
  mixed_shape_kernel_boundary_slice
      st fuel elem v n v1 v2 n1 n2 h_distinct ∧
  mixed_shape_divergence_iff_not_naive_contract_slice
      st fuel elem v n v1 v2 n1 n2 ∧
  mixed_shape_non_generalization_slice
      st fuel elem v n v1 v2 n1 n2 h_distinct

/-- Decompose `MixedShapeVarConstBoundarySuite` into explicit components. -/
theorem mixedShapeVarConstBoundarySuite_as_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (suite : MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct) :
    MixedShapeVarConstBoundarySuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct :=
  ⟨suite.kernelBoundary, suite.divergenceIffNotNaiveContract, suite.nonGeneralization⟩

/-- Build `MixedShapeVarConstBoundarySuite` from explicit components. -/
theorem mixedShapeVarConstBoundarySuite_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (h_kernel :
      mixed_shape_kernel_boundary_slice
        st fuel elem v n v1 v2 n1 n2 h_distinct)
    (h_div :
      mixed_shape_divergence_iff_not_naive_contract_slice
        st fuel elem v n v1 v2 n1 n2)
    (h_nonGen :
      mixed_shape_non_generalization_slice
        st fuel elem v n v1 v2 n1 n2 h_distinct) :
    MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct :=
  { kernelBoundary := h_kernel
    divergenceIffNotNaiveContract := h_div
    nonGeneralization := h_nonGen }

/-- Direct component-route decomposition for
`MixedShapeVarConstBoundarySuite`. -/
theorem mixedShapeVarConstBoundarySuite_as_components_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (h_comp : MixedShapeVarConstBoundarySuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct) :
    MixedShapeVarConstBoundarySuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct := by
  simpa using h_comp

/-- `MixedShapeVarConstBoundarySuite` is equivalent to its explicit component
tuple. -/
theorem mixedShapeVarConstBoundarySuite_iff_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2) :
    MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct ↔
      MixedShapeVarConstBoundarySuiteComponents
        st fuel elem v n v1 v2 n1 n2 h_distinct := by
  constructor
  · intro suite
    exact mixedShapeVarConstBoundarySuite_as_components
      st fuel elem v n v1 v2 n1 n2 h_distinct suite
  · intro h
    rcases h with ⟨h_kernel, h_div, h_nonGen⟩
    exact mixedShapeVarConstBoundarySuite_of_components
      st fuel elem v n v1 v2 n1 n2 h_distinct h_kernel h_div h_nonGen

/-- Master mixed-shape dim-aware boundary suite combining:
    rank-2 mixed classification, distinct-vars boundary packaging, and
    same-var/equal-constants boundary packaging. -/
structure MixedShapeDeepDimKernelMasterSuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) : Prop where
  rank2Classification :
    TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2
  distinctVarBoundary :
    MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct
  sameVarEqBoundary :
    TensorRank2SameVarEqBoundarySuite st fuel elem vSame n1 n2 h_eq

/-- Canonical master mixed-shape dim-aware boundary suite witness. -/
theorem mixedShapeDeepDimKernelMasterSuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) :
    MixedShapeDeepDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq := by
  refine
    { rank2Classification := ?_
      distinctVarBoundary := ?_
      sameVarEqBoundary := ?_ }
  · exact tensorRank2MixedDimKernelClassificationSlice_proved
      st fuel elem v1 v2 n1 n2
  · exact mixedShapeVarConstBoundarySuite
      st fuel elem v n v1 v2 n1 n2 h_distinct
  · exact tensorRank2SameVarEqBoundarySuite
      st fuel elem vSame n1 n2 h_eq

/-- Explicit component tuple alias for `MixedShapeDeepDimKernelMasterSuite`. -/
abbrev MixedShapeDeepDimKernelMasterSuiteComponents
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) : Prop :=
  TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2 ∧
  MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct ∧
  TensorRank2SameVarEqBoundarySuite st fuel elem vSame n1 n2 h_eq

/-- Decompose `MixedShapeDeepDimKernelMasterSuite` into explicit components. -/
theorem mixedShapeDeepDimKernelMasterSuite_as_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2)
    (suite : MixedShapeDeepDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq) :
    MixedShapeDeepDimKernelMasterSuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq :=
  ⟨suite.rank2Classification, suite.distinctVarBoundary, suite.sameVarEqBoundary⟩

/-- Build `MixedShapeDeepDimKernelMasterSuite` from explicit components. -/
theorem mixedShapeDeepDimKernelMasterSuite_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2)
    (h_rank2 :
      TensorRank2MixedDimKernelClassificationSlice st fuel elem v1 v2 n1 n2)
    (h_distinct_suite :
      MixedShapeVarConstBoundarySuite st fuel elem v n v1 v2 n1 n2 h_distinct)
    (h_same :
      TensorRank2SameVarEqBoundarySuite st fuel elem vSame n1 n2 h_eq) :
    MixedShapeDeepDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq :=
  { rank2Classification := h_rank2
    distinctVarBoundary := h_distinct_suite
    sameVarEqBoundary := h_same }

/-- Direct component-route decomposition for
`MixedShapeDeepDimKernelMasterSuite`. -/
theorem mixedShapeDeepDimKernelMasterSuite_as_components_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2)
    (h_comp : MixedShapeDeepDimKernelMasterSuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq) :
    MixedShapeDeepDimKernelMasterSuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq := by
  simpa using h_comp

/-- `MixedShapeDeepDimKernelMasterSuite` is equivalent to its explicit
component tuple. -/
theorem mixedShapeDeepDimKernelMasterSuite_iff_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) :
    MixedShapeDeepDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq ↔
      MixedShapeDeepDimKernelMasterSuiteComponents
        st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq := by
  constructor
  · intro suite
    exact mixedShapeDeepDimKernelMasterSuite_as_components
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq suite
  · intro h
    rcases h with ⟨h_rank2, h_distinct_suite, h_same⟩
    exact mixedShapeDeepDimKernelMasterSuite_of_components
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq
      h_rank2 h_distinct_suite h_same

/-- Fixed-size-list element mismatch does not unify when size matches. -/
theorem fixedSizeList_elem_mismatch
    (st : UnifyState) (d : Nat) :
    unify st 2
      (.fixedSizeList .int (.const d))
      (.fixedSizeList .bool (.const d))
      = .err "type mismatch" := by
  have h_neq :
      (Ty.fixedSizeList Ty.int (.const d) == Ty.fixedSizeList Ty.bool (.const d)) = false := by
    show beqTy (Ty.fixedSizeList Ty.int (.const d)) (Ty.fixedSizeList Ty.bool (.const d)) = false
    simp [beqTy]
  have h_int_bool_beq : (Ty.int == Ty.bool) = false := by
    simp [BEq.beq, beqTy]
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    simp [unify, applySubstCompat, applySubst, h_int_bool_beq]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- Tensor element mismatch does not unify when shape matches. -/
theorem tensor_elem_mismatch
    (st : UnifyState) (d : Nat) :
    unify st 2
      (.tensor .int [Dim.const d, Dim.const (d + 1)])
      (.tensor .bool [Dim.const d, Dim.const (d + 1)])
      = .err "type mismatch" := by
  have h_neq :
      (Ty.tensor Ty.int [Dim.const d, Dim.const (d + 1)] ==
        Ty.tensor Ty.bool [Dim.const d, Dim.const (d + 1)]) = false := by
    show beqTy (Ty.tensor Ty.int [Dim.const d, Dim.const (d + 1)])
      (Ty.tensor Ty.bool [Dim.const d, Dim.const (d + 1)]) = false
    simp [beqTy]
  have h_int_bool_beq : (Ty.int == Ty.bool) = false := by
    simp [BEq.beq, beqTy]
  have h_inner : unify st 1 .int .bool = .err "type mismatch" := by
    simp [unify, applySubstCompat, applySubst, h_int_bool_beq]
  unfold unify
  simp [applySubstCompat, applySubst, h_neq, h_inner]

/-- `FixedSizeList` free vars are exactly its element free vars. -/
theorem fixedSizeList_free_vars (elem : Ty) (d : Dim) :
    freeTypeVars (.fixedSizeList elem d) = freeTypeVars elem /\
      freeRowVars (.fixedSizeList elem d) = freeRowVars elem := by
  simp [freeTypeVars, freeRowVars]

/-- `Tensor` free vars are exactly its element free vars. -/
theorem tensor_free_vars (elem : Ty) (shape : List Dim) :
    freeTypeVars (.tensor elem shape) = freeTypeVars elem /\
      freeRowVars (.tensor elem shape) = freeRowVars elem := by
  simp [freeTypeVars, freeRowVars]

/-- Constant-dimension kernel success lifts to fixed-size-list unifier success. -/
theorem fixedSizeList_unify_consts_of_dim_kernel_success
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .ok st := by
  have hd_eq : d1 = d2 := (unifyDim_const_some_iff_eq DimSubst.empty fuel d1 d2).1 h_dim
  subst hd_eq
  simpa using (fixedSizeList_unifies_with_self st fuel .int (.const d1))

/-- Equal fixed-size-list constant dimensions are accepted. -/
theorem fixedSizeList_unify_consts_accept_of_eq
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_eq : d1 = d2) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .ok st := by
  subst h_eq
  have h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d1) = some DimSubst.empty := by
    simpa using (unifyDim_reflexive DimSubst.empty fuel (.const d1))
  exact fixedSizeList_unify_consts_of_dim_kernel_success st fuel d1 d1 h_dim

/-- Constant-dimension kernel failure forces fixed-size-list unifier rejection. -/
theorem fixedSizeList_unify_consts_reject_of_dim_kernel_none
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch" := by
  have hd_ne : d1 ≠ d2 := by
    intro hd_eq
    cases hd_eq
    have h_self : unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d1) = some DimSubst.empty := by
      simpa using (unifyDim_reflexive DimSubst.empty fuel (.const d1))
    have : False := by
      rw [h_dim] at h_self
      cases h_self
    exact this.elim
  exact fixedSizeList_dim_mismatch_any_fuel st fuel d1 d2 (fun h_eq => hd_ne h_eq)

/-- Distinct fixed-size-list constant dimensions are rejected. -/
theorem fixedSizeList_unify_consts_reject_of_ne
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_ne : d1 ≠ d2) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch" := by
  have h_none :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none :=
    (unifyDim_const_none_iff_ne DimSubst.empty fuel d1 d2).2 h_ne
  exact fixedSizeList_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_none

/-- Fixed-size-list constant-dimension unifier success iff dim-kernel succeeds. -/
theorem fixedSizeList_unify_consts_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .ok st ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty := by
  constructor
  · intro h_ok
    have h_not_none :
        unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none -> False := by
      intro h_none
      have h_err := fixedSizeList_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_none
      rw [h_ok] at h_err
      cases h_err
    have h_dec := unifyDim_const_decision DimSubst.empty fuel d1 d2
    cases hbeq : (d1 == d2) with
    | true =>
        simpa [hbeq] using h_dec
    | false =>
        have h_none :
            unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none := by
          simpa [hbeq] using h_dec
        exact (h_not_none h_none).elim
  · intro h_dim
    exact fixedSizeList_unify_consts_of_dim_kernel_success st fuel d1 d2 h_dim

/-- Fixed-size-list constant-dimension unifier rejection iff dim-kernel fails. -/
theorem fixedSizeList_unify_consts_err_iff_dim_kernel_none
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch" ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none := by
  constructor
  · intro h_err
    have h_dec := unifyDim_const_decision DimSubst.empty fuel d1 d2
    cases hbeq : (d1 == d2) with
    | true =>
        have h_dim :
            unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty := by
          simpa [hbeq] using h_dec
        have h_ok := (fixedSizeList_unify_consts_ok_iff_dim_kernel_success st fuel d1 d2).2 h_dim
        rw [h_ok] at h_err
        cases h_err
    | false =>
        simpa [hbeq] using h_dec
  · intro h_dim
    exact fixedSizeList_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_dim

/-- Fixed-size-list constant-dimension unifier result is decided by dim-kernel
    failure. -/
theorem fixedSizeList_unify_consts_decision_of_dim_kernel_none
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      =
      if unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
      then .err "type mismatch"
      else .ok st := by
  cases h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
  | none =>
      have h_err := fixedSizeList_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_dim
      simp [h_dim, h_err]
  | some s' =>
      have hs_empty : s' = DimSubst.empty :=
        unifyDim_const_some_implies_empty fuel d1 d2 s' h_dim
      subst hs_empty
      have h_ok := fixedSizeList_unify_consts_of_dim_kernel_success st fuel d1 d2 h_dim
      simp [h_dim, h_ok]

/-- Fixed-size-list constant-dimension unification follows exact
    dim-kernel match-decision behavior. -/
theorem fixedSizeList_unify_consts_match_decision
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      =
      (match unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
       | some _ => .ok st
       | none => .err "type mismatch") := by
  cases h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
  | none =>
      have h_err := fixedSizeList_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_dim
      simp [h_err]
  | some s' =>
      have hs_empty : s' = DimSubst.empty :=
        unifyDim_const_some_implies_empty fuel d1 d2 s' h_dim
      subst hs_empty
      have h_ok := fixedSizeList_unify_consts_of_dim_kernel_success st fuel d1 d2 h_dim
      simp [h_ok]

/-- Constant-dimension kernel success lifts to rank-1 tensor unifier success. -/
theorem tensor_rank1_unify_consts_of_dim_kernel_success
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .ok st := by
  have hd_eq : d1 = d2 := (unifyDim_const_some_iff_eq DimSubst.empty fuel d1 d2).1 h_dim
  subst hd_eq
  simpa using (tensor_unifies_with_self st fuel .int [Dim.const d1])

/-- Equal rank-1 tensor constant dimensions are accepted. -/
theorem tensor_rank1_unify_consts_accept_of_eq
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_eq : d1 = d2) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .ok st := by
  subst h_eq
  have h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d1) = some DimSubst.empty := by
    simpa using (unifyDim_reflexive DimSubst.empty fuel (.const d1))
  exact tensor_rank1_unify_consts_of_dim_kernel_success st fuel d1 d1 h_dim

/-- Pointwise constant-dimension list-kernel success lifts to tensor unifier
    success for arbitrary constant-rank shapes and arbitrary shared inner
    element types. -/
theorem tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat)
    (h_shape :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .ok st := by
  have h_eq : shape1 = shape2 := (unifyDimList_consts_some_iff_eq fuel shape1 shape2).1 h_shape
  subst h_eq
  simpa using (tensor_unifies_with_self st fuel elemTy (shape1.map Dim.const))

/-- Pointwise constant-dimension list-kernel success lifts to tensor unifier
    success for arbitrary constant-rank shapes. -/
theorem tensor_unify_const_shapes_of_dim_list_kernel_success
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat)
    (h_shape :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .ok st := by
  exact tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
    st fuel .int shape1 shape2 h_shape

/-- Equal arbitrary-rank tensor constant shapes with arbitrary shared inner
    element types are accepted. -/
theorem tensor_unify_const_shapes_accept_of_eq_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat)
    (h_eq : shape1 = shape2) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .ok st := by
  subst h_eq
  have h_shape :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape1.map Dim.const) = some DimSubst.empty := by
    exact unifyDimList_reflexive DimSubst.empty fuel (shape1.map Dim.const)
  exact tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
    st fuel elemTy shape1 shape1 h_shape

/-- Equal arbitrary-rank tensor constant shapes are accepted. -/
theorem tensor_unify_const_shapes_accept_of_eq
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat)
    (h_eq : shape1 = shape2) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .ok st := by
  exact tensor_unify_const_shapes_accept_of_eq_any_elem
    st fuel .int shape1 shape2 h_eq

/-- Pointwise constant dim-list kernel failure forces arbitrary-rank tensor
    constant-shape unifier rejection for arbitrary shared inner element
    types. -/
theorem tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat)
    (h_shape :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .err "type mismatch" := by
  have h_shape_beq :
      ((shape1.map Dim.const) == (shape2.map Dim.const)) = false :=
    unifyDimList_consts_none_implies_beq_false fuel shape1 shape2 h_shape
  exact tensor_shape_mismatch_any_elem_any_fuel st fuel elemTy
    (shape1.map Dim.const) (shape2.map Dim.const) h_shape_beq

/-- Pointwise constant dim-list kernel failure forces arbitrary-rank tensor
    constant-shape unifier rejection. -/
theorem tensor_unify_const_shapes_reject_of_dim_list_kernel_none
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat)
    (h_shape :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .err "type mismatch" := by
  exact tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
    st fuel .int shape1 shape2 h_shape

/-- Distinct arbitrary-rank tensor constant shapes with arbitrary shared inner
    element types are rejected. -/
theorem tensor_unify_const_shapes_reject_of_ne_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat)
    (h_ne : shape1 ≠ shape2) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .err "type mismatch" := by
  have h_none :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none :=
    (unifyDimList_consts_none_iff_ne fuel shape1 shape2).2 h_ne
  exact tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
    st fuel elemTy shape1 shape2 h_none

/-- Distinct arbitrary-rank tensor constant shapes are rejected. -/
theorem tensor_unify_const_shapes_reject_of_ne
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat)
    (h_ne : shape1 ≠ shape2) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .err "type mismatch" := by
  exact tensor_unify_const_shapes_reject_of_ne_any_elem
    st fuel .int shape1 shape2 h_ne

/-- Arbitrary-rank tensor constant-shape unifier rejects on constant-list
    length mismatch. -/
theorem tensor_unify_const_shapes_reject_of_length_mismatch
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat)
    (h_len : shape1.length ≠ shape2.length) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .err "type mismatch" := by
  have h_none :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none :=
    unifyDimList_consts_length_mismatch_none fuel shape1 shape2 h_len
  exact tensor_unify_const_shapes_reject_of_dim_list_kernel_none st fuel shape1 shape2 h_none

/-- Arbitrary-rank tensor constant-shape unifier rejects on constant-head
    mismatch (regardless of tails). -/
theorem tensor_unify_const_shapes_reject_of_head_mismatch
    (st : UnifyState) (fuel a b : Nat) (tail1 tail2 : List Nat)
    (h_head : a ≠ b) :
    unify st (fuel + 1)
      (.tensor .int ((a :: tail1).map Dim.const))
      (.tensor .int ((b :: tail2).map Dim.const))
      = .err "type mismatch" := by
  have h_none :
      unifyDimList DimSubst.empty (fuel + 1)
        ((a :: tail1).map Dim.const) ((b :: tail2).map Dim.const) = none := by
    exact unifyDimList_head_const_mismatch_none fuel a b
      (tail1.map Dim.const) (tail2.map Dim.const) h_head
  exact tensor_unify_const_shapes_reject_of_dim_list_kernel_none st fuel
    (a :: tail1) (b :: tail2) h_none

/-- Arbitrary-rank tensor constant-shape unifier success iff pointwise
    constant dim-list kernel succeeds, for arbitrary shared inner element
    types. -/
theorem tensor_unify_const_shapes_ok_iff_dim_list_kernel_success_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .ok st ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty := by
  constructor
  · intro h_ok
    by_cases h_none :
        unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) = none
    · have h_err := tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
          st fuel elemTy shape1 shape2 h_none
      rw [h_ok] at h_err
      cases h_err
    · cases h_res :
          unifyDimList DimSubst.empty (fuel + 1)
            (shape1.map Dim.const) (shape2.map Dim.const) with
      | none =>
          contradiction
      | some s' =>
          have hs_empty : s' = DimSubst.empty :=
            unifyDimList_consts_some_implies_empty fuel shape1 shape2 s' h_res
          subst hs_empty
          rfl
  · intro h_shape
    exact tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
      st fuel elemTy shape1 shape2 h_shape

/-- Arbitrary-rank tensor constant-shape unifier rejection iff pointwise
    dim-list kernel fails, for arbitrary shared inner element types. -/
theorem tensor_unify_const_shapes_err_iff_dim_list_kernel_none_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .err "type mismatch" ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none := by
  constructor
  · intro h_err
    cases h_shape :
        unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) with
    | none =>
        exact h_shape
    | some s' =>
        have hs_empty : s' = DimSubst.empty :=
          unifyDimList_consts_some_implies_empty fuel shape1 shape2 s' h_shape
        subst hs_empty
        have h_ok := tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
          st fuel elemTy shape1 shape2 h_shape
        rw [h_ok] at h_err
        cases h_err
  · intro h_shape
    exact tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
      st fuel elemTy shape1 shape2 h_shape

/-- Arbitrary-rank tensor constant-shape unifier result is decided by pointwise
    dim-list-kernel failure, for arbitrary shared inner element types. -/
theorem tensor_unify_const_shapes_decision_of_dim_list_kernel_none_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      =
      if unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) = none
      then .err "type mismatch"
      else .ok st := by
  by_cases h_none :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none
  · have h_err := tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
      st fuel elemTy shape1 shape2 h_none
    simp [h_none, h_err]
  · cases h_shape :
        unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) with
    | none =>
        contradiction
    | some s' =>
        have hs_empty : s' = DimSubst.empty :=
          unifyDimList_consts_some_implies_empty fuel shape1 shape2 s' h_shape
        subst hs_empty
        have h_ok := tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
          st fuel elemTy shape1 shape2 h_shape
        simp [h_none, h_ok]

/-- Arbitrary-rank tensor constant-shape unification follows exact pointwise
    dim-list-kernel match-decision behavior, for arbitrary shared inner
    element types. -/
theorem tensor_unify_const_shapes_match_decision_any_elem
    (st : UnifyState) (fuel : Nat) (elemTy : Ty) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      =
      (match unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) with
       | some _ => .ok st
       | none => .err "type mismatch") := by
  cases h_shape :
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) with
  | none =>
      have h_err := tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
        st fuel elemTy shape1 shape2 h_shape
      simp [h_err]
  | some s' =>
      have hs_empty : s' = DimSubst.empty :=
        unifyDimList_consts_some_implies_empty fuel shape1 shape2 s' h_shape
      subst hs_empty
      have h_ok := tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
        st fuel elemTy shape1 shape2 h_shape
      simp [h_ok]

/-- Arbitrary-rank tensor constant-shape unifier success iff pointwise
    constant dim-list kernel succeeds. -/
theorem tensor_unify_const_shapes_ok_iff_dim_list_kernel_success
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .ok st ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty := by
  exact tensor_unify_const_shapes_ok_iff_dim_list_kernel_success_any_elem
    st fuel .int shape1 shape2

/-- Arbitrary-rank tensor constant-shape unifier rejection iff pointwise
    dim-list kernel fails. -/
theorem tensor_unify_const_shapes_err_iff_dim_list_kernel_none
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .err "type mismatch" ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none := by
  exact tensor_unify_const_shapes_err_iff_dim_list_kernel_none_any_elem
    st fuel .int shape1 shape2

/-- Arbitrary-rank tensor constant-shape unifier result is decided by pointwise
    dim-list-kernel failure. -/
theorem tensor_unify_const_shapes_decision_of_dim_list_kernel_none
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      =
      if unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) = none
      then .err "type mismatch"
      else .ok st := by
  exact tensor_unify_const_shapes_decision_of_dim_list_kernel_none_any_elem
    st fuel .int shape1 shape2

/-- Arbitrary-rank tensor constant-shape unification follows exact pointwise
    dim-list-kernel match-decision behavior. -/
theorem tensor_unify_const_shapes_match_decision
    (st : UnifyState) (fuel : Nat) (shape1 shape2 : List Nat) :
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      =
      (match unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) with
       | some _ => .ok st
       | none => .err "type mismatch") := by
  exact tensor_unify_const_shapes_match_decision_any_elem
    st fuel .int shape1 shape2

/-- Constant-dimension kernel failure forces rank-1 tensor unifier rejection. -/
theorem tensor_rank1_unify_consts_reject_of_dim_kernel_none
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .err "type mismatch" := by
  have hd_ne : d1 ≠ d2 := by
    intro hd_eq
    cases hd_eq
    have h_self : unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d1) = some DimSubst.empty := by
      simpa using (unifyDim_reflexive DimSubst.empty fuel (.const d1))
    have : False := by
      rw [h_dim] at h_self
      cases h_self
    exact this.elim
  have h_dim_beq : ((Dim.const d1 : Dim) == Dim.const d2) = false := by
    change (d1 == d2) = false
    exact nat_beq_false_of_ne hd_ne
  have h_shape :
      ((([Dim.const d1] : List Dim) == [Dim.const d2]) = false) := by
    simp [h_dim_beq]
  have h_neq :
      (Ty.tensor Ty.int [Dim.const d1] == Ty.tensor Ty.int [Dim.const d2]) = false := by
    show beqTy (Ty.tensor Ty.int [Dim.const d1]) (Ty.tensor Ty.int [Dim.const d2]) = false
    simp [beqTy, h_shape]
  cases fuel with
  | zero =>
      unfold unify
      simp [applySubstCompat, applySubst, h_neq, h_shape]
  | succ fuel' =>
      have h_int : applySubst st.subst fuel' .int = .int := applySubst_int st.subst fuel'
      unfold unify
      simp [applySubstCompat, applySubst, h_int, h_shape]
      exact h_neq

/-- Distinct rank-1 tensor constant dimensions are rejected. -/
theorem tensor_rank1_unify_consts_reject_of_ne
    (st : UnifyState) (fuel d1 d2 : Nat)
    (h_ne : d1 ≠ d2) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .err "type mismatch" := by
  have h_none :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none :=
    (unifyDim_const_none_iff_ne DimSubst.empty fuel d1 d2).2 h_ne
  exact tensor_rank1_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_none

/-- Rank-1 tensor constant-dimension unifier success iff dim-kernel succeeds. -/
theorem tensor_rank1_unify_consts_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .ok st ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty := by
  constructor
  · intro h_ok
    have h_not_none :
        unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none -> False := by
      intro h_none
      have h_err := tensor_rank1_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_none
      rw [h_ok] at h_err
      cases h_err
    have h_dec := unifyDim_const_decision DimSubst.empty fuel d1 d2
    cases hbeq : (d1 == d2) with
    | true =>
        simpa [hbeq] using h_dec
    | false =>
        have h_none :
            unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none := by
          simpa [hbeq] using h_dec
        exact (h_not_none h_none).elim
  · intro h_dim
    exact tensor_rank1_unify_consts_of_dim_kernel_success st fuel d1 d2 h_dim

/-- Rank-1 tensor constant-dimension unifier rejection iff dim-kernel fails. -/
theorem tensor_rank1_unify_consts_err_iff_dim_kernel_none
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .err "type mismatch" ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none := by
  constructor
  · intro h_err
    have h_dec := unifyDim_const_decision DimSubst.empty fuel d1 d2
    cases hbeq : (d1 == d2) with
    | true =>
        have h_dim :
            unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty := by
          simpa [hbeq] using h_dec
        have h_ok := (tensor_rank1_unify_consts_ok_iff_dim_kernel_success st fuel d1 d2).2 h_dim
        rw [h_ok] at h_err
        cases h_err
    | false =>
        simpa [hbeq] using h_dec
  · intro h_dim
    exact tensor_rank1_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_dim

/-- Rank-1 tensor constant-dimension unifier result is decided by dim-kernel
    failure. -/
theorem tensor_rank1_unify_consts_decision_of_dim_kernel_none
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      =
      if unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
      then .err "type mismatch"
      else .ok st := by
  cases h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
  | none =>
      have h_err := tensor_rank1_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_dim
      simp [h_dim, h_err]
  | some s' =>
      have hs_empty : s' = DimSubst.empty :=
        unifyDim_const_some_implies_empty fuel d1 d2 s' h_dim
      subst hs_empty
      have h_ok := tensor_rank1_unify_consts_of_dim_kernel_success st fuel d1 d2 h_dim
      simp [h_dim, h_ok]

/-- Rank-1 tensor constant-dimension unification follows exact dim-kernel
    match-decision behavior. -/
theorem tensor_rank1_unify_consts_match_decision
    (st : UnifyState) (fuel d1 d2 : Nat) :
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      =
      (match unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
       | some _ => .ok st
       | none => .err "type mismatch") := by
  cases h_dim :
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
  | none =>
      have h_err := tensor_rank1_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_dim
      simp [h_err]
  | some s' =>
      have hs_empty : s' = DimSubst.empty :=
        unifyDim_const_some_implies_empty fuel d1 d2 s' h_dim
      subst hs_empty
      have h_ok := tensor_rank1_unify_consts_of_dim_kernel_success st fuel d1 d2 h_dim
      simp [h_ok]

/-- Packaged rank-1 shape constructor contracts keyed by the scalar dim-kernel. -/
structure Rank1ShapeConstDimKernelSlice : Prop where
  fixedSizeList_ok_iff_dim_kernel_success :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.fixedSizeList .int (.const d1))
        (.fixedSizeList .int (.const d2))
        = .ok st ↔
        unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty
  fixedSizeList_match_decision :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.fixedSizeList .int (.const d1))
        (.fixedSizeList .int (.const d2))
        =
        (match unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
         | some _ => .ok st
         | none => .err "type mismatch")
  fixedSizeList_reject_of_dim_kernel_none :
    ∀ st fuel d1 d2,
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none →
      unify st (fuel + 1)
        (.fixedSizeList .int (.const d1))
        (.fixedSizeList .int (.const d2))
        = .err "type mismatch"
  fixedSizeList_err_iff_dim_kernel_none :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.fixedSizeList .int (.const d1))
        (.fixedSizeList .int (.const d2))
        = .err "type mismatch" ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
  fixedSizeList_decision_of_dim_kernel_none :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.fixedSizeList .int (.const d1))
        (.fixedSizeList .int (.const d2))
        =
        if unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
        then .err "type mismatch"
        else .ok st
  tensor_rank1_ok_iff_dim_kernel_success :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.tensor .int [Dim.const d1])
        (.tensor .int [Dim.const d2])
        = .ok st ↔
        unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty
  tensor_rank1_match_decision :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.tensor .int [Dim.const d1])
        (.tensor .int [Dim.const d2])
        =
        (match unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
         | some _ => .ok st
         | none => .err "type mismatch")
  tensor_rank1_reject_of_dim_kernel_none :
    ∀ st fuel d1 d2,
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none →
      unify st (fuel + 1)
        (.tensor .int [Dim.const d1])
        (.tensor .int [Dim.const d2])
        = .err "type mismatch"
  tensor_rank1_err_iff_dim_kernel_none :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.tensor .int [Dim.const d1])
        (.tensor .int [Dim.const d2])
        = .err "type mismatch" ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
  tensor_rank1_decision_of_dim_kernel_none :
    ∀ st fuel d1 d2,
      unify st (fuel + 1)
        (.tensor .int [Dim.const d1])
        (.tensor .int [Dim.const d2])
        =
        if unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
        then .err "type mismatch"
        else .ok st

/-- Canonical rank-1 shape/dim-kernel contract package for downstream reuse. -/
theorem rank1ShapeConstDimKernelSlice : Rank1ShapeConstDimKernelSlice := by
  refine
    { fixedSizeList_ok_iff_dim_kernel_success := ?_
      fixedSizeList_match_decision := ?_
      fixedSizeList_reject_of_dim_kernel_none := ?_
      fixedSizeList_err_iff_dim_kernel_none := ?_
      fixedSizeList_decision_of_dim_kernel_none := ?_
      tensor_rank1_ok_iff_dim_kernel_success := ?_
      tensor_rank1_match_decision := ?_
      tensor_rank1_reject_of_dim_kernel_none := ?_
      tensor_rank1_err_iff_dim_kernel_none := ?_
      tensor_rank1_decision_of_dim_kernel_none := ?_ }
  · intro st fuel d1 d2
    exact fixedSizeList_unify_consts_ok_iff_dim_kernel_success st fuel d1 d2
  · intro st fuel d1 d2
    exact fixedSizeList_unify_consts_match_decision st fuel d1 d2
  · intro st fuel d1 d2 h_none
    exact fixedSizeList_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_none
  · intro st fuel d1 d2
    exact fixedSizeList_unify_consts_err_iff_dim_kernel_none st fuel d1 d2
  · intro st fuel d1 d2
    exact fixedSizeList_unify_consts_decision_of_dim_kernel_none st fuel d1 d2
  · intro st fuel d1 d2
    exact tensor_rank1_unify_consts_ok_iff_dim_kernel_success st fuel d1 d2
  · intro st fuel d1 d2
    exact tensor_rank1_unify_consts_match_decision st fuel d1 d2
  · intro st fuel d1 d2 h_none
    exact tensor_rank1_unify_consts_reject_of_dim_kernel_none st fuel d1 d2 h_none
  · intro st fuel d1 d2
    exact tensor_rank1_unify_consts_err_iff_dim_kernel_none st fuel d1 d2
  · intro st fuel d1 d2
    exact tensor_rank1_unify_consts_decision_of_dim_kernel_none st fuel d1 d2

/-- Explicit component contract tuple for `Rank1ShapeConstDimKernelSlice`. -/
abbrev Rank1ShapeConstDimKernelSliceComponents : Prop :=
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .ok st ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty)
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      =
      (match unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
       | some _ => .ok st
       | none => .err "type mismatch"))
  ∧
  (∀ st fuel d1 d2,
    unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none →
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch")
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      = .err "type mismatch" ↔
    unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none)
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.fixedSizeList .int (.const d1))
      (.fixedSizeList .int (.const d2))
      =
      if unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
      then .err "type mismatch"
      else .ok st)
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .ok st ↔
      unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = some DimSubst.empty)
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      =
      (match unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) with
       | some _ => .ok st
       | none => .err "type mismatch"))
  ∧
  (∀ st fuel d1 d2,
    unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none →
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .err "type mismatch")
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      = .err "type mismatch" ↔
    unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none)
  ∧
  (∀ st fuel d1 d2,
    unify st (fuel + 1)
      (.tensor .int [Dim.const d1])
      (.tensor .int [Dim.const d2])
      =
      if unifyDim DimSubst.empty (fuel + 1) (.const d1) (.const d2) = none
      then .err "type mismatch"
      else .ok st)

/-- Decompose `Rank1ShapeConstDimKernelSlice` into explicit component
    contracts. -/
theorem rank1ShapeConstDimKernelSlice_as_components
    (slice : Rank1ShapeConstDimKernelSlice) :
    Rank1ShapeConstDimKernelSliceComponents :=
  ⟨slice.fixedSizeList_ok_iff_dim_kernel_success,
    slice.fixedSizeList_match_decision,
    slice.fixedSizeList_reject_of_dim_kernel_none,
    slice.fixedSizeList_err_iff_dim_kernel_none,
    slice.fixedSizeList_decision_of_dim_kernel_none,
    slice.tensor_rank1_ok_iff_dim_kernel_success,
    slice.tensor_rank1_match_decision,
    slice.tensor_rank1_reject_of_dim_kernel_none,
    slice.tensor_rank1_err_iff_dim_kernel_none,
    slice.tensor_rank1_decision_of_dim_kernel_none⟩

/-- Build `Rank1ShapeConstDimKernelSlice` from explicit component contracts. -/
theorem rank1ShapeConstDimKernelSlice_of_components
    (h_comp : Rank1ShapeConstDimKernelSliceComponents) :
    Rank1ShapeConstDimKernelSlice :=
  { fixedSizeList_ok_iff_dim_kernel_success := h_comp.1
    fixedSizeList_match_decision := h_comp.2.1
    fixedSizeList_reject_of_dim_kernel_none := h_comp.2.2.1
    fixedSizeList_err_iff_dim_kernel_none := h_comp.2.2.2.1
    fixedSizeList_decision_of_dim_kernel_none := h_comp.2.2.2.2.1
    tensor_rank1_ok_iff_dim_kernel_success := h_comp.2.2.2.2.2.1
    tensor_rank1_match_decision := h_comp.2.2.2.2.2.2.1
    tensor_rank1_reject_of_dim_kernel_none := h_comp.2.2.2.2.2.2.2.1
    tensor_rank1_err_iff_dim_kernel_none := h_comp.2.2.2.2.2.2.2.2.1
    tensor_rank1_decision_of_dim_kernel_none := h_comp.2.2.2.2.2.2.2.2.2 }

/-- `Rank1ShapeConstDimKernelSlice` is equivalent to its explicit component
    contract tuple. -/
theorem rank1ShapeConstDimKernelSlice_iff_components
    (slice : Rank1ShapeConstDimKernelSlice) :
    Rank1ShapeConstDimKernelSlice ↔ Rank1ShapeConstDimKernelSliceComponents := by
  constructor
  · intro h
    exact rank1ShapeConstDimKernelSlice_as_components h
  · intro h_comp
    exact rank1ShapeConstDimKernelSlice_of_components h_comp

/-- Direct components-route decomposition for
    `Rank1ShapeConstDimKernelSlice`. -/
theorem rank1ShapeConstDimKernelSlice_as_components_of_components
    (h_comp : Rank1ShapeConstDimKernelSliceComponents) :
    Rank1ShapeConstDimKernelSliceComponents := by
  simpa using h_comp

/-- Packaged arbitrary-rank tensor constant-shape contracts keyed by the
    pointwise dim-list kernel. -/
structure TensorConstShapeDimListKernelSlice : Prop where
  success_of_dim_list_kernel_success_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty →
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        = .ok st
  reject_of_dim_list_kernel_none_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none →
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        = .err "type mismatch"
  reject_of_ne_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      shape1 ≠ shape2 →
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        = .err "type mismatch"
  reject_of_length_mismatch :
    ∀ st fuel shape1 shape2,
      shape1.length ≠ shape2.length →
      unify st (fuel + 1)
        (.tensor .int (shape1.map Dim.const))
        (.tensor .int (shape2.map Dim.const))
        = .err "type mismatch"
  reject_of_head_mismatch :
    ∀ st fuel a b tail1 tail2,
      a ≠ b →
      unify st (fuel + 1)
        (.tensor .int ((a :: tail1).map Dim.const))
        (.tensor .int ((b :: tail2).map Dim.const))
        = .err "type mismatch"
  ok_iff_dim_list_kernel_success_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        = .ok st ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty
  err_iff_dim_list_kernel_none_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        = .err "type mismatch" ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none
  decision_of_dim_list_kernel_none_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        =
        if unifyDimList DimSubst.empty (fuel + 1)
            (shape1.map Dim.const) (shape2.map Dim.const) = none
        then .err "type mismatch"
        else .ok st
  match_decision_any_elem :
    ∀ st fuel elemTy shape1 shape2,
      unify st (fuel + 1)
        (.tensor elemTy (shape1.map Dim.const))
        (.tensor elemTy (shape2.map Dim.const))
        =
        (match unifyDimList DimSubst.empty (fuel + 1)
            (shape1.map Dim.const) (shape2.map Dim.const) with
         | some _ => .ok st
         | none => .err "type mismatch")
  ok_iff_dim_list_kernel_success :
    ∀ st fuel shape1 shape2,
      unify st (fuel + 1)
        (.tensor .int (shape1.map Dim.const))
        (.tensor .int (shape2.map Dim.const))
        = .ok st ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty
  err_iff_dim_list_kernel_none :
    ∀ st fuel shape1 shape2,
      unify st (fuel + 1)
        (.tensor .int (shape1.map Dim.const))
        (.tensor .int (shape2.map Dim.const))
        = .err "type mismatch" ↔
      unifyDimList DimSubst.empty (fuel + 1)
        (shape1.map Dim.const) (shape2.map Dim.const) = none
  decision_of_dim_list_kernel_none :
    ∀ st fuel shape1 shape2,
      unify st (fuel + 1)
        (.tensor .int (shape1.map Dim.const))
        (.tensor .int (shape2.map Dim.const))
        =
        if unifyDimList DimSubst.empty (fuel + 1)
            (shape1.map Dim.const) (shape2.map Dim.const) = none
        then .err "type mismatch"
        else .ok st
  match_decision :
    ∀ st fuel shape1 shape2,
      unify st (fuel + 1)
        (.tensor .int (shape1.map Dim.const))
        (.tensor .int (shape2.map Dim.const))
        =
        (match unifyDimList DimSubst.empty (fuel + 1)
            (shape1.map Dim.const) (shape2.map Dim.const) with
         | some _ => .ok st
         | none => .err "type mismatch")

/-- Canonical arbitrary-rank tensor constant-shape/dim-kernel package. -/
theorem tensorConstShapeDimListKernelSlice : TensorConstShapeDimListKernelSlice := by
  refine
    { success_of_dim_list_kernel_success_any_elem := ?_
      reject_of_dim_list_kernel_none_any_elem := ?_
      reject_of_ne_any_elem := ?_
      reject_of_length_mismatch := ?_
      reject_of_head_mismatch := ?_
      ok_iff_dim_list_kernel_success_any_elem := ?_
      err_iff_dim_list_kernel_none_any_elem := ?_
      decision_of_dim_list_kernel_none_any_elem := ?_
      match_decision_any_elem := ?_
      ok_iff_dim_list_kernel_success := ?_
      err_iff_dim_list_kernel_none := ?_
      decision_of_dim_list_kernel_none := ?_
      match_decision := ?_ }
  · intro st fuel elemTy shape1 shape2 h_shape
    exact tensor_unify_const_shapes_of_dim_list_kernel_success_any_elem
      st fuel elemTy shape1 shape2 h_shape
  · intro st fuel elemTy shape1 shape2 h_shape
    exact tensor_unify_const_shapes_reject_of_dim_list_kernel_none_any_elem
      st fuel elemTy shape1 shape2 h_shape
  · intro st fuel elemTy shape1 shape2 h_ne
    exact tensor_unify_const_shapes_reject_of_ne_any_elem
      st fuel elemTy shape1 shape2 h_ne
  · intro st fuel shape1 shape2 h_len
    exact tensor_unify_const_shapes_reject_of_length_mismatch
      st fuel shape1 shape2 h_len
  · intro st fuel a b tail1 tail2 h_head
    exact tensor_unify_const_shapes_reject_of_head_mismatch
      st fuel a b tail1 tail2 h_head
  · intro st fuel elemTy shape1 shape2
    exact tensor_unify_const_shapes_ok_iff_dim_list_kernel_success_any_elem
      st fuel elemTy shape1 shape2
  · intro st fuel elemTy shape1 shape2
    exact tensor_unify_const_shapes_err_iff_dim_list_kernel_none_any_elem
      st fuel elemTy shape1 shape2
  · intro st fuel elemTy shape1 shape2
    exact tensor_unify_const_shapes_decision_of_dim_list_kernel_none_any_elem
      st fuel elemTy shape1 shape2
  · intro st fuel elemTy shape1 shape2
    exact tensor_unify_const_shapes_match_decision_any_elem
      st fuel elemTy shape1 shape2
  · intro st fuel shape1 shape2
    exact tensor_unify_const_shapes_ok_iff_dim_list_kernel_success
      st fuel shape1 shape2
  · intro st fuel shape1 shape2
    exact tensor_unify_const_shapes_err_iff_dim_list_kernel_none
      st fuel shape1 shape2
  · intro st fuel shape1 shape2
    exact tensor_unify_const_shapes_decision_of_dim_list_kernel_none
      st fuel shape1 shape2
  · intro st fuel shape1 shape2
    exact tensor_unify_const_shapes_match_decision
      st fuel shape1 shape2

/-- Explicit component contract tuple for
    `TensorConstShapeDimListKernelSlice`. -/
abbrev TensorConstShapeDimListKernelSliceComponents : Prop :=
  (∀ st fuel elemTy shape1 shape2,
    unifyDimList DimSubst.empty (fuel + 1)
      (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty →
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .ok st)
  ∧
  (∀ st fuel elemTy shape1 shape2,
    unifyDimList DimSubst.empty (fuel + 1)
      (shape1.map Dim.const) (shape2.map Dim.const) = none →
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .err "type mismatch")
  ∧
  (∀ st fuel elemTy shape1 shape2,
    shape1 ≠ shape2 →
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .err "type mismatch")
  ∧
  (∀ st fuel shape1 shape2,
    shape1.length ≠ shape2.length →
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .err "type mismatch")
  ∧
  (∀ st fuel a b tail1 tail2,
    a ≠ b →
    unify st (fuel + 1)
      (.tensor .int ((a :: tail1).map Dim.const))
      (.tensor .int ((b :: tail2).map Dim.const))
      = .err "type mismatch")
  ∧
  (∀ st fuel elemTy shape1 shape2,
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .ok st ↔
    unifyDimList DimSubst.empty (fuel + 1)
      (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty)
  ∧
  (∀ st fuel elemTy shape1 shape2,
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      = .err "type mismatch" ↔
    unifyDimList DimSubst.empty (fuel + 1)
      (shape1.map Dim.const) (shape2.map Dim.const) = none)
  ∧
  (∀ st fuel elemTy shape1 shape2,
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      =
      if unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) = none
      then .err "type mismatch"
      else .ok st)
  ∧
  (∀ st fuel elemTy shape1 shape2,
    unify st (fuel + 1)
      (.tensor elemTy (shape1.map Dim.const))
      (.tensor elemTy (shape2.map Dim.const))
      =
      (match unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) with
       | some _ => .ok st
       | none => .err "type mismatch"))
  ∧
  (∀ st fuel shape1 shape2,
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .ok st ↔
    unifyDimList DimSubst.empty (fuel + 1)
      (shape1.map Dim.const) (shape2.map Dim.const) = some DimSubst.empty)
  ∧
  (∀ st fuel shape1 shape2,
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      = .err "type mismatch" ↔
    unifyDimList DimSubst.empty (fuel + 1)
      (shape1.map Dim.const) (shape2.map Dim.const) = none)
  ∧
  (∀ st fuel shape1 shape2,
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      =
      if unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) = none
      then .err "type mismatch"
      else .ok st)
  ∧
  (∀ st fuel shape1 shape2,
    unify st (fuel + 1)
      (.tensor .int (shape1.map Dim.const))
      (.tensor .int (shape2.map Dim.const))
      =
      (match unifyDimList DimSubst.empty (fuel + 1)
          (shape1.map Dim.const) (shape2.map Dim.const) with
       | some _ => .ok st
       | none => .err "type mismatch"))

/-- Decompose `TensorConstShapeDimListKernelSlice` into explicit component
    contracts. -/
theorem tensorConstShapeDimListKernelSlice_as_components
    (slice : TensorConstShapeDimListKernelSlice) :
    TensorConstShapeDimListKernelSliceComponents :=
  ⟨slice.success_of_dim_list_kernel_success_any_elem,
    slice.reject_of_dim_list_kernel_none_any_elem,
    slice.reject_of_ne_any_elem,
    slice.reject_of_length_mismatch,
    slice.reject_of_head_mismatch,
    slice.ok_iff_dim_list_kernel_success_any_elem,
    slice.err_iff_dim_list_kernel_none_any_elem,
    slice.decision_of_dim_list_kernel_none_any_elem,
    slice.match_decision_any_elem,
    slice.ok_iff_dim_list_kernel_success,
    slice.err_iff_dim_list_kernel_none,
    slice.decision_of_dim_list_kernel_none,
    slice.match_decision⟩

/-- Build `TensorConstShapeDimListKernelSlice` from explicit component
    contracts. -/
theorem tensorConstShapeDimListKernelSlice_of_components
    (h_comp : TensorConstShapeDimListKernelSliceComponents) :
    TensorConstShapeDimListKernelSlice := by
  rcases h_comp with
    ⟨h_success_any, h_reject_none_any, h_reject_ne_any, h_reject_len,
      h_reject_head, h_ok_iff_any, h_err_iff_any, h_dec_any, h_match_any,
      h_ok_iff, h_err_iff, h_dec, h_match⟩
  exact
    { success_of_dim_list_kernel_success_any_elem := h_success_any
      reject_of_dim_list_kernel_none_any_elem := h_reject_none_any
      reject_of_ne_any_elem := h_reject_ne_any
      reject_of_length_mismatch := h_reject_len
      reject_of_head_mismatch := h_reject_head
      ok_iff_dim_list_kernel_success_any_elem := h_ok_iff_any
      err_iff_dim_list_kernel_none_any_elem := h_err_iff_any
      decision_of_dim_list_kernel_none_any_elem := h_dec_any
      match_decision_any_elem := h_match_any
      ok_iff_dim_list_kernel_success := h_ok_iff
      err_iff_dim_list_kernel_none := h_err_iff
      decision_of_dim_list_kernel_none := h_dec
      match_decision := h_match }

/-- `TensorConstShapeDimListKernelSlice` is equivalent to its explicit
    component contract tuple. -/
theorem tensorConstShapeDimListKernelSlice_iff_components
    (slice : TensorConstShapeDimListKernelSlice) :
    TensorConstShapeDimListKernelSlice ↔
      TensorConstShapeDimListKernelSliceComponents := by
  constructor
  · intro h
    exact tensorConstShapeDimListKernelSlice_as_components h
  · intro h_comp
    exact tensorConstShapeDimListKernelSlice_of_components h_comp

/-- Direct components-route decomposition for
    `TensorConstShapeDimListKernelSlice`. -/
theorem tensorConstShapeDimListKernelSlice_as_components_of_components
    (h_comp : TensorConstShapeDimListKernelSliceComponents) :
    TensorConstShapeDimListKernelSliceComponents := by
  simpa using h_comp

/-- Top-level packaged shape/dimension kernel suite for constant-shape
    constructor routes. -/
structure ShapeConstDimKernelSuite : Prop where
  dimKernel : DimKernelSuite
  scalarKernel : DimConstKernelSlice
  dimListKernel : DimConstListKernelSlice
  rank1ShapeKernel : Rank1ShapeConstDimKernelSlice
  tensorShapeKernel : TensorConstShapeDimListKernelSlice

/-- Explicit component tuple alias for `ShapeConstDimKernelSuite`. -/
abbrev ShapeConstDimKernelSuiteComponents : Prop :=
  DimKernelSuite ∧
    DimConstKernelSlice ∧
    DimConstListKernelSlice ∧
    Rank1ShapeConstDimKernelSlice ∧
    TensorConstShapeDimListKernelSlice

/-- Canonical constant-shape shape/dimension kernel suite. -/
theorem shapeConstDimKernelSuite : ShapeConstDimKernelSuite := by
  exact
    { dimKernel := dimKernelSuite
      scalarKernel := dimConstKernelSlice
      dimListKernel := dimConstListKernelSlice
      rank1ShapeKernel := rank1ShapeConstDimKernelSlice
      tensorShapeKernel := tensorConstShapeDimListKernelSlice }

/-- Decompose the top-level shape/dimension suite into explicit components. -/
theorem shapeConstDimKernelSuite_as_components
    (suite : ShapeConstDimKernelSuite) :
    ShapeConstDimKernelSuiteComponents :=
  ⟨suite.dimKernel, suite.scalarKernel, suite.dimListKernel,
    suite.rank1ShapeKernel, suite.tensorShapeKernel⟩

/-- Build the top-level shape/dimension suite from explicit components. -/
theorem shapeConstDimKernelSuite_of_components
    (dimKernel : DimKernelSuite)
    (scalarKernel : DimConstKernelSlice)
    (dimListKernel : DimConstListKernelSlice)
    (rank1ShapeKernel : Rank1ShapeConstDimKernelSlice)
    (tensorShapeKernel : TensorConstShapeDimListKernelSlice) :
    ShapeConstDimKernelSuite :=
  { dimKernel := dimKernel
    scalarKernel := scalarKernel
    dimListKernel := dimListKernel
    rank1ShapeKernel := rank1ShapeKernel
    tensorShapeKernel := tensorShapeKernel }

/-- Direct component-route decomposition for `ShapeConstDimKernelSuite`. -/
theorem shapeConstDimKernelSuite_as_components_of_components
    (h_comp : ShapeConstDimKernelSuiteComponents) :
    ShapeConstDimKernelSuiteComponents := by
  simpa using h_comp

/-- `ShapeConstDimKernelSuite` is equivalent to its explicit component tuple. -/
theorem shapeConstDimKernelSuite_iff_components :
    ShapeConstDimKernelSuite ↔
      ShapeConstDimKernelSuiteComponents := by
  constructor
  · intro suite
    exact shapeConstDimKernelSuite_as_components suite
  · intro h
    exact shapeConstDimKernelSuite_of_components
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Unified numeric+shape kernel suite:
    combines numeric constructor contracts with constant-shape contracts. -/
structure NumericShapeConstDimKernelSuite : Prop where
  numericKernel : NumericConstructorKernelSuite
  shapeKernel : ShapeConstDimKernelSuite

/-- Explicit component pair alias for `NumericShapeConstDimKernelSuite`. -/
abbrev NumericShapeConstDimKernelSuiteComponents : Prop :=
  NumericConstructorKernelSuite ∧ ShapeConstDimKernelSuite

/-- Canonical numeric+shape kernel suite. -/
theorem numericShapeConstDimKernelSuite : NumericShapeConstDimKernelSuite := by
  exact
    { numericKernel := numericConstructorKernelSuite
      shapeKernel := shapeConstDimKernelSuite }

/-- Decompose the numeric+shape suite into explicit components. -/
theorem numericShapeConstDimKernelSuite_as_components
    (suite : NumericShapeConstDimKernelSuite) :
    NumericShapeConstDimKernelSuiteComponents :=
  ⟨suite.numericKernel, suite.shapeKernel⟩

/-- Build the numeric+shape suite from explicit components. -/
theorem numericShapeConstDimKernelSuite_of_components
    (numericKernel : NumericConstructorKernelSuite)
    (shapeKernel : ShapeConstDimKernelSuite) :
    NumericShapeConstDimKernelSuite :=
  { numericKernel := numericKernel
    shapeKernel := shapeKernel }

/-- Direct components-route decomposition for
    `NumericShapeConstDimKernelSuite`. -/
theorem numericShapeConstDimKernelSuite_as_components_of_components
    (h_comp : NumericShapeConstDimKernelSuiteComponents) :
    NumericShapeConstDimKernelSuiteComponents := by
  simpa using h_comp

/-- `NumericShapeConstDimKernelSuite` is equivalent to its explicit component
    pair. -/
theorem numericShapeConstDimKernelSuite_iff_components :
    NumericShapeConstDimKernelSuite ↔
      NumericShapeConstDimKernelSuiteComponents := by
  constructor
  · intro suite
    exact numericShapeConstDimKernelSuite_as_components suite
  · intro h
    exact numericShapeConstDimKernelSuite_of_components h.1 h.2

/-- Extended constant-shape suite that pairs the existing shape suite with the
extended dimension-kernel package (`DimKernelExtendedSuite`). -/
structure ShapeConstDimKernelExtendedSuite : Prop where
  shapeKernel : ShapeConstDimKernelSuite
  dimKernelExtended : DimKernelExtendedSuite

/-- Explicit component pair alias for `ShapeConstDimKernelExtendedSuite`. -/
abbrev ShapeConstDimKernelExtendedSuiteComponents : Prop :=
  ShapeConstDimKernelSuite ∧ DimKernelExtendedSuite

/-- Canonical extended constant-shape suite witness. -/
theorem shapeConstDimKernelExtendedSuite : ShapeConstDimKernelExtendedSuite := by
  exact
    { shapeKernel := shapeConstDimKernelSuite
      dimKernelExtended := dimKernelExtendedSuite }

/-- Decompose `ShapeConstDimKernelExtendedSuite` into explicit components. -/
theorem shapeConstDimKernelExtendedSuite_as_components
    (suite : ShapeConstDimKernelExtendedSuite) :
    ShapeConstDimKernelExtendedSuiteComponents :=
  ⟨suite.shapeKernel, suite.dimKernelExtended⟩

/-- Build `ShapeConstDimKernelExtendedSuite` from explicit components. -/
theorem shapeConstDimKernelExtendedSuite_of_components
    (shapeKernel : ShapeConstDimKernelSuite)
    (dimKernelExtended : DimKernelExtendedSuite) :
    ShapeConstDimKernelExtendedSuite :=
  { shapeKernel := shapeKernel
    dimKernelExtended := dimKernelExtended }

/-- Direct components-route decomposition for
`ShapeConstDimKernelExtendedSuite`. -/
theorem shapeConstDimKernelExtendedSuite_as_components_of_components
    (h_comp : ShapeConstDimKernelExtendedSuiteComponents) :
    ShapeConstDimKernelExtendedSuiteComponents := by
  simpa using h_comp

/-- `ShapeConstDimKernelExtendedSuite` is equivalent to its explicit component
pair. -/
theorem shapeConstDimKernelExtendedSuite_iff_components :
    ShapeConstDimKernelExtendedSuite ↔
      ShapeConstDimKernelExtendedSuiteComponents := by
  constructor
  · intro suite
    exact shapeConstDimKernelExtendedSuite_as_components suite
  · intro h
    exact shapeConstDimKernelExtendedSuite_of_components h.1 h.2

/-- Unified numeric + extended-shape kernel suite:
    combines numeric constructor contracts with the extended shape/dimension
    package that includes deeper rank-2 var/const kernel contracts. -/
structure NumericShapeConstDimKernelExtendedSuite : Prop where
  numericKernel : NumericConstructorKernelSuite
  shapeKernelExtended : ShapeConstDimKernelExtendedSuite

/-- Explicit component pair alias for `NumericShapeConstDimKernelExtendedSuite`. -/
abbrev NumericShapeConstDimKernelExtendedSuiteComponents : Prop :=
  NumericConstructorKernelSuite ∧ ShapeConstDimKernelExtendedSuite

/-- Canonical numeric + extended-shape suite witness. -/
theorem numericShapeConstDimKernelExtendedSuite :
    NumericShapeConstDimKernelExtendedSuite := by
  exact
    { numericKernel := numericConstructorKernelSuite
      shapeKernelExtended := shapeConstDimKernelExtendedSuite }

/-- Decompose `NumericShapeConstDimKernelExtendedSuite` into explicit components. -/
theorem numericShapeConstDimKernelExtendedSuite_as_components
    (suite : NumericShapeConstDimKernelExtendedSuite) :
    NumericShapeConstDimKernelExtendedSuiteComponents :=
  ⟨suite.numericKernel, suite.shapeKernelExtended⟩

/-- Build `NumericShapeConstDimKernelExtendedSuite` from explicit components. -/
theorem numericShapeConstDimKernelExtendedSuite_of_components
    (numericKernel : NumericConstructorKernelSuite)
    (shapeKernelExtended : ShapeConstDimKernelExtendedSuite) :
    NumericShapeConstDimKernelExtendedSuite :=
  { numericKernel := numericKernel
    shapeKernelExtended := shapeKernelExtended }

/-- Direct components-route decomposition for
`NumericShapeConstDimKernelExtendedSuite`. -/
theorem numericShapeConstDimKernelExtendedSuite_as_components_of_components
    (h_comp : NumericShapeConstDimKernelExtendedSuiteComponents) :
    NumericShapeConstDimKernelExtendedSuiteComponents := by
  simpa using h_comp

/-- `NumericShapeConstDimKernelExtendedSuite` is equivalent to its explicit
component pair. -/
theorem numericShapeConstDimKernelExtendedSuite_iff_components :
    NumericShapeConstDimKernelExtendedSuite ↔
      NumericShapeConstDimKernelExtendedSuiteComponents := by
  constructor
  · intro suite
    exact numericShapeConstDimKernelExtendedSuite_as_components suite
  · intro h
    exact numericShapeConstDimKernelExtendedSuite_of_components h.1 h.2

/-- Top-level mixed+constant numeric shape suite:
    combines the numeric/extended-constant-shape suite with the mixed-shape
    boundary master package. -/
structure NumericShapeMixedDimKernelMasterSuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) : Prop where
  constShapeExtended : NumericShapeConstDimKernelExtendedSuite
  mixedBoundary :
    MixedShapeDeepDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq

/-- Explicit component pair alias for `NumericShapeMixedDimKernelMasterSuite`. -/
abbrev NumericShapeMixedDimKernelMasterSuiteComponents
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) : Prop :=
  NumericShapeConstDimKernelExtendedSuite ∧
  MixedShapeDeepDimKernelMasterSuite
    st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq

/-- Canonical top-level mixed+constant numeric shape suite witness. -/
theorem numericShapeMixedDimKernelMasterSuite
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) :
    NumericShapeMixedDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq := by
  exact
    { constShapeExtended := numericShapeConstDimKernelExtendedSuite
      mixedBoundary := mixedShapeDeepDimKernelMasterSuite
        st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq }

/-- Decompose `NumericShapeMixedDimKernelMasterSuite` into explicit components. -/
theorem numericShapeMixedDimKernelMasterSuite_as_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2)
    (suite : NumericShapeMixedDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq) :
    NumericShapeMixedDimKernelMasterSuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq :=
  ⟨suite.constShapeExtended, suite.mixedBoundary⟩

/-- Build `NumericShapeMixedDimKernelMasterSuite` from explicit components. -/
theorem numericShapeMixedDimKernelMasterSuite_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2)
    (constShapeExtended : NumericShapeConstDimKernelExtendedSuite)
    (mixedBoundary :
      MixedShapeDeepDimKernelMasterSuite
        st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq) :
    NumericShapeMixedDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq :=
  { constShapeExtended := constShapeExtended
    mixedBoundary := mixedBoundary }

/-- Direct components-route decomposition for
`NumericShapeMixedDimKernelMasterSuite`. -/
theorem numericShapeMixedDimKernelMasterSuite_as_components_of_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2)
    (h_comp : NumericShapeMixedDimKernelMasterSuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq) :
    NumericShapeMixedDimKernelMasterSuiteComponents
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq := by
  simpa using h_comp

/-- `NumericShapeMixedDimKernelMasterSuite` is equivalent to its explicit
component pair. -/
theorem numericShapeMixedDimKernelMasterSuite_iff_components
    (st : UnifyState) (fuel : Nat) (elem : Ty)
    (v : DimVarId) (n : Nat)
    (v1 v2 : DimVarId) (n1 n2 : Nat)
    (h_distinct : v1 ≠ v2)
    (vSame : DimVarId) (h_eq : n1 = n2) :
    NumericShapeMixedDimKernelMasterSuite
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq ↔
      NumericShapeMixedDimKernelMasterSuiteComponents
        st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq := by
  constructor
  · intro suite
    exact numericShapeMixedDimKernelMasterSuite_as_components
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq suite
  · intro h
    exact numericShapeMixedDimKernelMasterSuite_of_components
      st fuel elem v n v1 v2 n1 n2 h_distinct vSame h_eq h.1 h.2
