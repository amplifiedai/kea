/-
  Kea.Dimensions — Dimension-variable kernel for precision/shape work.

  This module is intentionally standalone from `Ty` unification so we can
  prove Dim/DimVar substitution and unification properties before wiring
  Decimal/Tensor constructors into the main type-unifier surface.
-/

import Kea.Ty

/-- Free dimension variables in a dimension expression. -/
def freeDimVars : Dim → List DimVarId
  | .const _ => []
  | .var v => [v]

/-- Dimension-variable substitution map. -/
structure DimSubst where
  map : DimVarId → Option Dim

namespace DimSubst

/-- Empty dimension substitution. -/
def empty : DimSubst :=
  { map := fun _ => none }

/-- Extend a dimension substitution with one binding. -/
def extend (s : DimSubst) (v : DimVarId) (d : Dim) : DimSubst :=
  { map := fun w => if w = v then some d else s.map w }

/-- Ground-range substitutions map every variable to a constant dimension. -/
structure GroundRange (s : DimSubst) : Prop where
  ground : ∀ v d, s.map v = some d → ∃ n, d = .const n

end DimSubst

/-- Fuel-bounded dimension substitution (mirrors type substitution style). -/
def applyDimSubst (s : DimSubst) : Nat → Dim → Dim
  | 0, d => d
  | _ + 1, .const n => .const n
  | fuel + 1, .var v =>
    match s.map v with
    | none => .var v
    | some d => applyDimSubst s fuel d

/-- Occurs check for a dimension variable in a dimension expression. -/
def occursInDim (v : DimVarId) : Dim → Bool
  | .const _ => false
  | .var w => v == w

/-- Bind a dimension variable, rejecting occurs-check cycles. -/
def bindDimVar (s : DimSubst) (v : DimVarId) (d : Dim) (fuel : Nat) : Option DimSubst :=
  let d' := applyDimSubst s fuel d
  if occursInDim v d' then none else some (DimSubst.extend s v d')

/-- Unify two dimension expressions under a substitution state. -/
def unifyDim (s : DimSubst) (fuel : Nat) (a b : Dim) : Option DimSubst :=
  let a' := applyDimSubst s fuel a
  let b' := applyDimSubst s fuel b
  if a' == b' then some s else
    match a', b' with
    | .var v, d => bindDimVar s v d fuel
    | d, .var v => bindDimVar s v d fuel
    | .const _, .const _ => none

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases h_beq : (a == b) with
  | false => rfl
  | true =>
    have hab : a = b := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h_beq)
    exact (h hab).elim

/-- Dimension BEq reflexivity. -/
theorem beqDim_refl (d : Dim) : (d == d) = true := by
  cases d <;> simp [BEq.beq]

/-- Substituting any constant dimension is a no-op. -/
theorem applyDimSubst_const (s : DimSubst) (fuel n : Nat) :
    applyDimSubst s fuel (.const n) = .const n := by
  cases fuel <;> simp [applyDimSubst]

/-- Empty dimension substitution is identity at all fuels. -/
theorem applyDimSubst_empty (fuel : Nat) (d : Dim) :
    applyDimSubst DimSubst.empty fuel d = d := by
  cases fuel with
  | zero =>
    rfl
  | succ n =>
    cases d with
    | const k => rfl
    | var v => simp [applyDimSubst, DimSubst.empty]

/-- If all free vars are unmapped, dimension substitution is a no-op. -/
theorem applyDimSubst_noop (s : DimSubst) :
    ∀ fuel d, (∀ v ∈ freeDimVars d, s.map v = none) → applyDimSubst s fuel d = d := by
  intro fuel d h
  cases fuel with
  | zero =>
    rfl
  | succ n =>
    cases d with
    | const k =>
      rfl
    | var v =>
      have hv : s.map v = none := h v (by simp [freeDimVars])
      simp [applyDimSubst, hv]

/-- Ground-range substitutions are idempotent under repeated application. -/
theorem applyDimSubst_idempotent_ground
    (s : DimSubst) (h_ground : DimSubst.GroundRange s) :
    ∀ fuel d, applyDimSubst s fuel (applyDimSubst s fuel d) = applyDimSubst s fuel d := by
  intro fuel d
  cases fuel with
  | zero =>
    rfl
  | succ n =>
    cases d with
    | const k =>
      rfl
    | var v =>
      cases h_map : s.map v with
      | none =>
        simp [applyDimSubst, h_map]
      | some resolved =>
        rcases h_ground.ground v resolved h_map with ⟨k, hk⟩
        subst hk
        have h_const_inner : applyDimSubst s n (.const k) = .const k := by
          exact applyDimSubst_const s n k
        simp [applyDimSubst, h_map, h_const_inner]

/-- Dimension unification is reflexive. -/
theorem unifyDim_reflexive (s : DimSubst) (fuel : Nat) (d : Dim) :
    unifyDim s (fuel + 1) d d = some s := by
  have h_eq : (applyDimSubst s (fuel + 1) d == applyDimSubst s (fuel + 1) d) = true :=
    beqDim_refl _
  simp [unifyDim, h_eq]

/-- If normalized dimensions compare equal, unification returns the current substitution. -/
theorem unifyDim_of_beq_true
    (s : DimSubst) (fuel : Nat) (a b : Dim)
    (h_eq : (applyDimSubst s (fuel + 1) a == applyDimSubst s (fuel + 1) b) = true) :
    unifyDim s (fuel + 1) a b = some s := by
  unfold unifyDim
  simp [h_eq]

/-- Constant-constant dimension unification is exactly BEq-driven. -/
theorem unifyDim_const_decision
    (s : DimSubst) (fuel a b : Nat) :
    unifyDim s (fuel + 1) (.const a) (.const b) =
      (if a == b then some s else none) := by
  cases h : (a == b) with
  | true =>
      have hd : ((Dim.const a : Dim) == Dim.const b) = true := by
        simpa [BEq.beq] using h
      simp [unifyDim, applyDimSubst, hd]
  | false =>
      have hd : ((Dim.const a : Dim) == Dim.const b) = false := by
        simpa [BEq.beq] using h
      simp [unifyDim, applyDimSubst, hd]

/-- Constant-constant unification succeeds exactly on equal constants. -/
theorem unifyDim_const_some_iff_eq
    (s : DimSubst) (fuel a b : Nat) :
    unifyDim s (fuel + 1) (.const a) (.const b) = some s ↔ a = b := by
  rw [unifyDim_const_decision]
  cases h : (a == b) with
  | true =>
      have hab : a = b := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h)
      simp [hab]
  | false =>
      have hab : a ≠ b := by
        intro hab
        subst hab
        simp [BEq.beq] at h
      simp [hab]

/-- Constant-constant unification fails exactly on distinct constants. -/
theorem unifyDim_const_none_iff_ne
    (s : DimSubst) (fuel a b : Nat) :
    unifyDim s (fuel + 1) (.const a) (.const b) = none ↔ a ≠ b := by
  constructor
  · intro h_none
    intro h_eq
    subst h_eq
    have h_self : unifyDim s (fuel + 1) (.const a) (.const a) = some s := by
      simpa using (unifyDim_reflexive s fuel (.const a))
    rw [h_none] at h_self
    cases h_self
  · intro h_ne
    have h_dec := unifyDim_const_decision s fuel a b
    have h_beq_false : (a == b) = false := nat_beq_false_of_ne h_ne
    simpa [h_beq_false] using h_dec

/-- Constant-constant unification from `DimSubst.empty` cannot produce a
    non-empty substitution. -/
theorem unifyDim_const_some_implies_empty
    (fuel a b : Nat) (s' : DimSubst)
    (h_some :
      unifyDim DimSubst.empty (fuel + 1) (.const a) (.const b) = some s') :
    s' = DimSubst.empty := by
  have h_dec := unifyDim_const_decision DimSubst.empty fuel a b
  cases hbeq : (a == b) with
  | true =>
      rw [hbeq] at h_dec
      simp at h_dec
      rw [h_some] at h_dec
      injection h_dec with hs
  | false =>
      rw [hbeq] at h_dec
      simp at h_dec
      rw [h_some] at h_dec
      cases h_dec

/-- Distinct constants do not unify. -/
theorem unifyDim_const_mismatch (s : DimSubst) (fuel a b : Nat) (h : a ≠ b) :
    unifyDim s (fuel + 1) (.const a) (.const b) = none := by
  unfold unifyDim
  have h_beq : ((.const a : Dim) == (.const b : Dim)) = false := by
    change (a == b) = false
    exact nat_beq_false_of_ne h
  simp [applyDimSubst, h_beq]

/-- Unifying an unbound variable with a constant adds the expected binding. -/
theorem unifyDim_var_const_binds
    (s : DimSubst) (fuel : Nat) (v : DimVarId) (n : Nat)
    (h_unbound : s.map v = none) :
    unifyDim s (fuel + 1) (.var v) (.const n) =
      some (DimSubst.extend s v (.const n)) := by
  unfold unifyDim
  simp [applyDimSubst, h_unbound, bindDimVar, occursInDim, DimSubst.extend]

/-- Unifying a constant with an unbound variable adds the expected binding. -/
theorem unifyDim_const_var_binds
    (s : DimSubst) (fuel : Nat) (n : Nat) (v : DimVarId)
    (h_unbound : s.map v = none) :
    unifyDim s (fuel + 1) (.const n) (.var v) =
      some (DimSubst.extend s v (.const n)) := by
  unfold unifyDim
  simp [applyDimSubst, h_unbound, bindDimVar, occursInDim, DimSubst.extend]

/-- Dimension variables have no free vars after substituting with constants. -/
theorem freeDimVars_applyDimSubst_ground
    (s : DimSubst) (h_ground : DimSubst.GroundRange s) (fuel : Nat) (v : DimVarId)
    (h_bound : ∃ d, s.map v = some d) :
    freeDimVars (applyDimSubst s (fuel + 1) (.var v)) = [] := by
  rcases h_bound with ⟨d, h_map⟩
  rcases h_ground.ground v d h_map with ⟨n, hn⟩
  subst hn
  have h_const_inner : applyDimSubst s fuel (.const n) = .const n := by
    exact applyDimSubst_const s fuel n
  simp [applyDimSubst, h_map, h_const_inner, freeDimVars]

/-- Unify two dimension lists pointwise under a shared substitution state. -/
def unifyDimList (s : DimSubst) (fuel : Nat) : List Dim → List Dim → Option DimSubst
  | [], [] => some s
  | d1 :: ds1, d2 :: ds2 =>
      match unifyDim s fuel d1 d2 with
      | some s' => unifyDimList s' fuel ds1 ds2
      | none => none
  | _, _ => none

/-- Single-element var-vs-const dim-list unification binds the variable. -/
theorem unifyDimList_single_var_const_binds
    (fuel : Nat) (v : DimVarId) (n : Nat) :
    unifyDimList DimSubst.empty (fuel + 1) [Dim.var v] [Dim.const n] =
      some (DimSubst.extend DimSubst.empty v (.const n)) := by
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n) =
        some (DimSubst.extend DimSubst.empty v (.const n)) := by
    exact unifyDim_var_const_binds DimSubst.empty fuel v n rfl
  simp [unifyDimList, h_head]

/-- Single-element const-vs-var dim-list unification binds the variable. -/
theorem unifyDimList_single_const_var_binds
    (fuel : Nat) (n : Nat) (v : DimVarId) :
    unifyDimList DimSubst.empty (fuel + 1) [Dim.const n] [Dim.var v] =
      some (DimSubst.extend DimSubst.empty v (.const n)) := by
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.const n) (.var v) =
        some (DimSubst.extend DimSubst.empty v (.const n)) := by
    exact unifyDim_const_var_binds DimSubst.empty fuel n v rfl
  simp [unifyDimList, h_head]

/-- Two-element var-vs-const dim-list unification binds each distinct
    variable to the corresponding constant. -/
theorem unifyDimList_pair_var_const_binds_distinct
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) (h_distinct : v1 ≠ v2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v1, Dim.var v2]
      [Dim.const n1, Dim.const n2] =
      some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) := by
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.var v1) (.const n1) =
        some (DimSubst.extend DimSubst.empty v1 (.const n1)) := by
    exact unifyDim_var_const_binds DimSubst.empty fuel v1 n1 rfl
  have h_v2_unbound :
      (DimSubst.extend DimSubst.empty v1 (.const n1)).map v2 = none := by
    have h_v2_ne_v1 : v2 ≠ v1 := by
      intro h_eq
      exact h_distinct h_eq.symm
    simp [DimSubst.extend, DimSubst.empty, h_v2_ne_v1]
  have h_tail_head :
      unifyDim (DimSubst.extend DimSubst.empty v1 (.const n1)) (fuel + 1)
        (.var v2) (.const n2) =
        some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) := by
    exact unifyDim_var_const_binds
      (DimSubst.extend DimSubst.empty v1 (.const n1)) fuel v2 n2 h_v2_unbound
  simp [unifyDimList, h_head, h_tail_head]

/-- Two-element const-vs-var dim-list unification binds each distinct
    variable to the corresponding constant. -/
theorem unifyDimList_pair_const_var_binds_distinct
    (fuel : Nat) (n1 n2 : Nat) (v1 v2 : DimVarId) (h_distinct : v1 ≠ v2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v1, Dim.var v2] =
      some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) := by
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.const n1) (.var v1) =
        some (DimSubst.extend DimSubst.empty v1 (.const n1)) := by
    exact unifyDim_const_var_binds DimSubst.empty fuel n1 v1 rfl
  have h_v2_unbound :
      (DimSubst.extend DimSubst.empty v1 (.const n1)).map v2 = none := by
    have h_v2_ne_v1 : v2 ≠ v1 := by
      intro h_eq
      exact h_distinct h_eq.symm
    simp [DimSubst.extend, DimSubst.empty, h_v2_ne_v1]
  have h_tail_head :
      unifyDim (DimSubst.extend DimSubst.empty v1 (.const n1)) (fuel + 1)
        (.const n2) (.var v2) =
        some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) := by
    exact unifyDim_const_var_binds
      (DimSubst.extend DimSubst.empty v1 (.const n1)) fuel n2 v2 h_v2_unbound
  simp [unifyDimList, h_head, h_tail_head]

/-- Two-element var-vs-const dim-list unification with the same variable on
    both positions succeeds exactly when the constants are equal. -/
theorem unifyDimList_pair_same_var_const_binds_of_eq
    (fuel : Nat) (v : DimVarId) (n1 n2 : Nat) (h_eq : n1 = n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v, Dim.var v]
      [Dim.const n1, Dim.const n2] =
      some (DimSubst.extend DimSubst.empty v (.const n1)) := by
  subst h_eq
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n1) =
        some (DimSubst.extend DimSubst.empty v (.const n1)) := by
    exact unifyDim_var_const_binds DimSubst.empty fuel v n1 rfl
  let s1 : DimSubst := DimSubst.extend DimSubst.empty v (.const n1)
  have h_dim_beq_true : ((Dim.const n1 : Dim) == Dim.const n1) = true := by
    simp [BEq.beq]
  have h_tail_beq :
      (applyDimSubst s1 (fuel + 1) (.var v) == applyDimSubst s1 (fuel + 1) (.const n1)) = true := by
    cases fuel with
    | zero =>
        simp [applyDimSubst, s1, DimSubst.extend, h_dim_beq_true]
    | succ fuel' =>
        simp [applyDimSubst, s1, DimSubst.extend, h_dim_beq_true]
  have h_tail_head :
      unifyDim s1 (fuel + 1) (.var v) (.const n1) = some s1 := by
    exact unifyDim_of_beq_true s1 fuel (.var v) (.const n1) h_tail_beq
  simp [unifyDimList, h_head, h_tail_head, s1]

/-- Two-element var-vs-const dim-list unification with the same variable on
    both positions fails when constants disagree. -/
theorem unifyDimList_pair_same_var_const_none_of_ne
    (fuel : Nat) (v : DimVarId) (n1 n2 : Nat) (h_ne : n1 ≠ n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v, Dim.var v]
      [Dim.const n1, Dim.const n2] = none := by
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.var v) (.const n1) =
        some (DimSubst.extend DimSubst.empty v (.const n1)) := by
    exact unifyDim_var_const_binds DimSubst.empty fuel v n1 rfl
  let s1 : DimSubst := DimSubst.extend DimSubst.empty v (.const n1)
  have h_beq_false : (n1 == n2) = false := nat_beq_false_of_ne h_ne
  have h_dim_beq_false : ((Dim.const n1 : Dim) == Dim.const n2) = false := by
    simpa [BEq.beq] using h_beq_false
  have h_tail_head :
      unifyDim s1 (fuel + 1) (.var v) (.const n2) = none := by
    cases fuel with
    | zero =>
        simp [unifyDim, applyDimSubst, s1, DimSubst.extend, h_dim_beq_false]
    | succ fuel' =>
        simp [unifyDim, applyDimSubst, s1, DimSubst.extend, h_dim_beq_false]
  simp [unifyDimList, h_head, h_tail_head, s1]

/-- Exact decision contract for two-element var-vs-const dim-list unification
    with a repeated variable on the left. -/
theorem unifyDimList_pair_same_var_const_decision
    (fuel : Nat) (v : DimVarId) (n1 n2 : Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v, Dim.var v]
      [Dim.const n1, Dim.const n2] =
      (if n1 = n2 then
        some (DimSubst.extend DimSubst.empty v (.const n1))
      else none) := by
  by_cases h_eq : n1 = n2
  · simp [unifyDimList_pair_same_var_const_binds_of_eq, h_eq]
  · simp [unifyDimList_pair_same_var_const_none_of_ne, h_eq]

/-- Two-element const-vs-var dim-list unification with the same variable on
    both positions succeeds exactly when the constants are equal. -/
theorem unifyDimList_pair_const_same_var_binds_of_eq
    (fuel : Nat) (n1 n2 : Nat) (v : DimVarId) (h_eq : n1 = n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v, Dim.var v] =
      some (DimSubst.extend DimSubst.empty v (.const n1)) := by
  subst h_eq
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.const n1) (.var v) =
        some (DimSubst.extend DimSubst.empty v (.const n1)) := by
    exact unifyDim_const_var_binds DimSubst.empty fuel n1 v rfl
  let s1 : DimSubst := DimSubst.extend DimSubst.empty v (.const n1)
  have h_dim_beq_true : ((Dim.const n1 : Dim) == Dim.const n1) = true := by
    simp [BEq.beq]
  have h_tail_beq :
      (applyDimSubst s1 (fuel + 1) (.const n1) == applyDimSubst s1 (fuel + 1) (.var v)) = true := by
    cases fuel with
    | zero =>
        simp [applyDimSubst, s1, DimSubst.extend, h_dim_beq_true]
    | succ fuel' =>
        simp [applyDimSubst, s1, DimSubst.extend, h_dim_beq_true]
  have h_tail_head :
      unifyDim s1 (fuel + 1) (.const n1) (.var v) = some s1 := by
    exact unifyDim_of_beq_true s1 fuel (.const n1) (.var v) h_tail_beq
  simp [unifyDimList, h_head, h_tail_head, s1]

/-- Two-element const-vs-var dim-list unification with the same variable on
    both positions fails when constants disagree. -/
theorem unifyDimList_pair_const_same_var_none_of_ne
    (fuel : Nat) (n1 n2 : Nat) (v : DimVarId) (h_ne : n1 ≠ n2) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v, Dim.var v] = none := by
  have h_head :
      unifyDim DimSubst.empty (fuel + 1) (.const n1) (.var v) =
        some (DimSubst.extend DimSubst.empty v (.const n1)) := by
    exact unifyDim_const_var_binds DimSubst.empty fuel n1 v rfl
  let s1 : DimSubst := DimSubst.extend DimSubst.empty v (.const n1)
  have h_beq_false : (n2 == n1) = false := by
    exact nat_beq_false_of_ne (fun h => h_ne h.symm)
  have h_dim_beq_false : ((Dim.const n2 : Dim) == Dim.const n1) = false := by
    simpa [BEq.beq] using h_beq_false
  have h_tail_head :
      unifyDim s1 (fuel + 1) (.const n2) (.var v) = none := by
    cases fuel with
    | zero =>
        simp [unifyDim, applyDimSubst, s1, DimSubst.extend, h_dim_beq_false]
    | succ fuel' =>
        simp [unifyDim, applyDimSubst, s1, DimSubst.extend, h_dim_beq_false]
  simp [unifyDimList, h_head, h_tail_head, s1]

/-- Exact decision contract for two-element const-vs-var dim-list unification
    with a repeated variable on the right. -/
theorem unifyDimList_pair_const_same_var_decision
    (fuel : Nat) (n1 n2 : Nat) (v : DimVarId) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v, Dim.var v] =
      (if n1 = n2 then
        some (DimSubst.extend DimSubst.empty v (.const n1))
      else none) := by
  by_cases h_eq : n1 = n2
  · simp [unifyDimList_pair_const_same_var_binds_of_eq, h_eq]
  · simp [unifyDimList_pair_const_same_var_none_of_ne, h_eq]

/-- Rank-2 var-vs-const dim-list unification succeeds exactly when either
    variables are distinct, or repeated-variable constants agree. -/
theorem unifyDimList_pair_var_const_some_iff_var_distinct_or_consts_eq
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.var v1, Dim.var v2]
        [Dim.const n1, Dim.const n2] = some s') ↔
    (v1 ≠ v2 ∨ n1 = n2) := by
  constructor
  · intro h_some
    by_cases h_distinct : v1 ≠ v2
    · exact Or.inl h_distinct
    · have h_eq_vars : v1 = v2 := Classical.not_not.mp h_distinct
      subst h_eq_vars
      by_cases h_eq_consts : n1 = n2
      · exact Or.inr h_eq_consts
      · have h_none :
            unifyDimList DimSubst.empty (fuel + 1)
              [Dim.var v1, Dim.var v1]
              [Dim.const n1, Dim.const n2] = none :=
          unifyDimList_pair_same_var_const_none_of_ne fuel v1 n1 n2 h_eq_consts
        rcases h_some with ⟨s', h_some_eq⟩
        rw [h_none] at h_some_eq
        cases h_some_eq
  · intro h_case
    cases h_case with
    | inl h_distinct =>
        exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
          unifyDimList_pair_var_const_binds_distinct fuel v1 v2 n1 n2 h_distinct⟩
    | inr h_eq_consts =>
        by_cases h_eq_vars : v1 = v2
        · subst h_eq_vars
          exact ⟨DimSubst.extend DimSubst.empty v1 (.const n1),
            unifyDimList_pair_same_var_const_binds_of_eq fuel v1 n1 n2 h_eq_consts⟩
        · exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
            unifyDimList_pair_var_const_binds_distinct fuel v1 v2 n1 n2 h_eq_vars⟩

/-- Rank-2 var-vs-const dim-list unification fails exactly when variables are
    equal and constants disagree. -/
theorem unifyDimList_pair_var_const_none_iff_var_eq_and_consts_ne
    (fuel : Nat) (v1 v2 : DimVarId) (n1 n2 : Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.var v1, Dim.var v2]
      [Dim.const n1, Dim.const n2] = none ↔
    (v1 = v2 ∧ n1 ≠ n2) := by
  constructor
  · intro h_none
    by_cases h_eq_vars : v1 = v2
    · subst h_eq_vars
      refine ⟨rfl, ?_⟩
      intro h_eq_consts
      have h_some :
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v1]
            [Dim.const n1, Dim.const n2] =
            some (DimSubst.extend DimSubst.empty v1 (.const n1)) :=
        unifyDimList_pair_same_var_const_binds_of_eq fuel v1 n1 n2 h_eq_consts
      rw [h_none] at h_some
      cases h_some
    · have h_some :
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.var v1, Dim.var v2]
            [Dim.const n1, Dim.const n2] =
            some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) :=
        unifyDimList_pair_var_const_binds_distinct fuel v1 v2 n1 n2 h_eq_vars
      rw [h_none] at h_some
      cases h_some
  · intro h_case
    rcases h_case with ⟨h_eq_vars, h_ne_consts⟩
    subst h_eq_vars
    exact unifyDimList_pair_same_var_const_none_of_ne fuel v1 n1 n2 h_ne_consts

/-- Rank-2 const-vs-var dim-list unification succeeds exactly when either
    variables are distinct, or repeated-variable constants agree. -/
theorem unifyDimList_pair_const_var_some_iff_var_distinct_or_consts_eq
    (fuel : Nat) (n1 n2 : Nat) (v1 v2 : DimVarId) :
    (∃ s' : DimSubst,
      unifyDimList DimSubst.empty (fuel + 1)
        [Dim.const n1, Dim.const n2]
        [Dim.var v1, Dim.var v2] = some s') ↔
    (v1 ≠ v2 ∨ n1 = n2) := by
  constructor
  · intro h_some
    by_cases h_distinct : v1 ≠ v2
    · exact Or.inl h_distinct
    · have h_eq_vars : v1 = v2 := Classical.not_not.mp h_distinct
      subst h_eq_vars
      by_cases h_eq_consts : n1 = n2
      · exact Or.inr h_eq_consts
      · have h_none :
            unifyDimList DimSubst.empty (fuel + 1)
              [Dim.const n1, Dim.const n2]
              [Dim.var v1, Dim.var v1] = none :=
          unifyDimList_pair_const_same_var_none_of_ne fuel n1 n2 v1 h_eq_consts
        rcases h_some with ⟨s', h_some_eq⟩
        rw [h_none] at h_some_eq
        cases h_some_eq
  · intro h_case
    cases h_case with
    | inl h_distinct =>
        exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
          unifyDimList_pair_const_var_binds_distinct fuel n1 n2 v1 v2 h_distinct⟩
    | inr h_eq_consts =>
        by_cases h_eq_vars : v1 = v2
        · subst h_eq_vars
          exact ⟨DimSubst.extend DimSubst.empty v1 (.const n1),
            unifyDimList_pair_const_same_var_binds_of_eq fuel n1 n2 v1 h_eq_consts⟩
        · exact ⟨DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2),
            unifyDimList_pair_const_var_binds_distinct fuel n1 n2 v1 v2 h_eq_vars⟩

/-- Rank-2 const-vs-var dim-list unification fails exactly when variables are
    equal and constants disagree. -/
theorem unifyDimList_pair_const_var_none_iff_var_eq_and_consts_ne
    (fuel : Nat) (n1 n2 : Nat) (v1 v2 : DimVarId) :
    unifyDimList DimSubst.empty (fuel + 1)
      [Dim.const n1, Dim.const n2]
      [Dim.var v1, Dim.var v2] = none ↔
    (v1 = v2 ∧ n1 ≠ n2) := by
  constructor
  · intro h_none
    by_cases h_eq_vars : v1 = v2
    · subst h_eq_vars
      refine ⟨rfl, ?_⟩
      intro h_eq_consts
      have h_some :
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v1] =
            some (DimSubst.extend DimSubst.empty v1 (.const n1)) :=
        unifyDimList_pair_const_same_var_binds_of_eq fuel n1 n2 v1 h_eq_consts
      rw [h_none] at h_some
      cases h_some
    · have h_some :
          unifyDimList DimSubst.empty (fuel + 1)
            [Dim.const n1, Dim.const n2]
            [Dim.var v1, Dim.var v2] =
            some (DimSubst.extend (DimSubst.extend DimSubst.empty v1 (.const n1)) v2 (.const n2)) :=
        unifyDimList_pair_const_var_binds_distinct fuel n1 n2 v1 v2 h_eq_vars
      rw [h_none] at h_some
      cases h_some
  · intro h_case
    rcases h_case with ⟨h_eq_vars, h_ne_consts⟩
    subst h_eq_vars
    exact unifyDimList_pair_const_same_var_none_of_ne fuel n1 n2 v1 h_ne_consts

/-- Pointwise dimension-list unification is reflexive. -/
theorem unifyDimList_reflexive (s : DimSubst) (fuel : Nat) :
    ∀ ds : List Dim, unifyDimList s (fuel + 1) ds ds = some s := by
  intro ds
  induction ds with
  | nil =>
      simp [unifyDimList]
  | cons d ds ih =>
      simp [unifyDimList, unifyDim_reflexive, ih]

/-- Constant dimension-list unification succeeds exactly on list equality. -/
theorem unifyDimList_consts_some_iff_eq
    (fuel : Nat) (xs ys : List Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      (xs.map Dim.const) (ys.map Dim.const) = some DimSubst.empty ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp [unifyDimList]
      | cons y ys =>
          simp [unifyDimList]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [unifyDimList]
      | cons y ys =>
          constructor
          · intro h_ok
            have hxy : x = y := by
              by_cases hxy : x = y
              · exact hxy
              · have h_head_none :
                    unifyDim DimSubst.empty (fuel + 1) (.const x) (.const y) = none := by
                  exact (unifyDim_const_none_iff_ne DimSubst.empty fuel x y).2 hxy
                have : False := by
                  simp [unifyDimList, h_head_none] at h_ok
                exact False.elim this
            have h_head :
                unifyDim DimSubst.empty (fuel + 1) (.const x) (.const y) =
                  some DimSubst.empty := by
              cases hxy
              simpa using (unifyDim_reflexive DimSubst.empty fuel (.const x))
            have h_tail :
                unifyDimList DimSubst.empty (fuel + 1)
                  (xs.map Dim.const) (ys.map Dim.const) = some DimSubst.empty := by
              simpa [unifyDimList, h_head] using h_ok
            have h_eq_tail : xs = ys := (ih ys).1 h_tail
            cases hxy
            simp [h_eq_tail]
          · intro h_eq
            cases h_eq
            have h_head :
                unifyDim DimSubst.empty (fuel + 1) (.const x) (.const x) =
                  some DimSubst.empty := by
              simpa using (unifyDim_reflexive DimSubst.empty fuel (.const x))
            have h_tail :
                unifyDimList DimSubst.empty (fuel + 1)
                  (xs.map Dim.const) (xs.map Dim.const) = some DimSubst.empty := by
              exact (ih xs).2 rfl
            simpa [unifyDimList, h_head] using h_tail

/-- Constant dim-list unification cannot produce non-empty substitutions. -/
theorem unifyDimList_consts_some_implies_empty
    (fuel : Nat) (xs ys : List Nat) (s' : DimSubst)
    (h_some :
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = some s') :
    s' = DimSubst.empty := by
  induction xs generalizing ys s' with
  | nil =>
      cases ys with
      | nil =>
          have hs : DimSubst.empty = s' := by
            simpa [unifyDimList] using h_some
          exact hs.symm
      | cons y ys =>
          simp [unifyDimList] at h_some
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [unifyDimList] at h_some
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            have h_head :
                unifyDim DimSubst.empty (fuel + 1) (.const x) (.const x) =
                  some DimSubst.empty := by
              simpa using (unifyDim_reflexive DimSubst.empty fuel (.const x))
            have h_tail :
                unifyDimList DimSubst.empty (fuel + 1)
                  (xs.map Dim.const) (ys.map Dim.const) = some s' := by
              simpa [unifyDimList, h_head] using h_some
            exact ih ys s' h_tail
          · have h_head_none :
                unifyDim DimSubst.empty (fuel + 1) (.const x) (.const y) = none := by
              exact (unifyDim_const_none_iff_ne DimSubst.empty fuel x y).2 hxy
            simp [unifyDimList, h_head_none] at h_some

/-- Constant dim-list unification fails exactly on list inequality. -/
theorem unifyDimList_consts_none_iff_ne
    (fuel : Nat) (xs ys : List Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      (xs.map Dim.const) (ys.map Dim.const) = none ↔ xs ≠ ys := by
  constructor
  · intro h_none
    intro h_eq
    have h_some :
        unifyDimList DimSubst.empty (fuel + 1)
          (xs.map Dim.const) (ys.map Dim.const) = some DimSubst.empty := by
      exact (unifyDimList_consts_some_iff_eq fuel xs ys).2 h_eq
    rw [h_none] at h_some
    cases h_some
  · intro h_ne
    by_cases h_none :
        unifyDimList DimSubst.empty (fuel + 1)
          (xs.map Dim.const) (ys.map Dim.const) = none
    · exact h_none
    · cases h_res :
          unifyDimList DimSubst.empty (fuel + 1)
            (xs.map Dim.const) (ys.map Dim.const) with
      | none =>
          contradiction
      | some s' =>
          have hs_empty : s' = DimSubst.empty :=
            unifyDimList_consts_some_implies_empty fuel xs ys s' h_res
          have h_some_empty :
              unifyDimList DimSubst.empty (fuel + 1)
                (xs.map Dim.const) (ys.map Dim.const) = some DimSubst.empty := by
            simpa [hs_empty] using h_res
          have h_eq : xs = ys := (unifyDimList_consts_some_iff_eq fuel xs ys).1 h_some_empty
          exact (h_ne h_eq).elim

/-- Constant dim-list unification follows exact equality-vs-mismatch decision. -/
theorem unifyDimList_consts_decision
    (fuel : Nat) (xs ys : List Nat) :
    unifyDimList DimSubst.empty (fuel + 1)
      (xs.map Dim.const) (ys.map Dim.const) =
      (if xs = ys then some DimSubst.empty else none) := by
  by_cases h_eq : xs = ys
  · subst h_eq
    simpa using (unifyDimList_consts_some_iff_eq fuel xs xs).2 rfl
  · have h_none :
        unifyDimList DimSubst.empty (fuel + 1)
          (xs.map Dim.const) (ys.map Dim.const) = none :=
      (unifyDimList_consts_none_iff_ne fuel xs ys).2 h_eq
    simp [h_eq, h_none]

/-- Constant-head mismatch forces pointwise dim-list unification failure. -/
theorem unifyDimList_head_const_mismatch_none
    (fuel a b : Nat) (xs ys : List Dim) (h : a ≠ b) :
    unifyDimList DimSubst.empty (fuel + 1)
      (.const a :: xs) (.const b :: ys) = none := by
  have h_head_none :
      unifyDim DimSubst.empty (fuel + 1) (.const a) (.const b) = none :=
    (unifyDim_const_none_iff_ne DimSubst.empty fuel a b).2 h
  simp [unifyDimList, h_head_none]

/-- Constant dim-list length mismatch forces pointwise unification failure. -/
theorem unifyDimList_consts_length_mismatch_none
    (fuel : Nat) (xs ys : List Nat) (h_len : xs.length ≠ ys.length) :
    unifyDimList DimSubst.empty (fuel + 1)
      (xs.map Dim.const) (ys.map Dim.const) = none := by
  have h_ne : xs ≠ ys := by
    intro h_eq
    apply h_len
    simp [h_eq]
  exact (unifyDimList_consts_none_iff_ne fuel xs ys).2 h_ne

/-- Constant dim-list kernel failure implies list-BEq failure on mapped dims. -/
theorem unifyDimList_consts_none_implies_beq_false
    (fuel : Nat) (xs ys : List Nat)
    (h_none :
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = none) :
    ((xs.map Dim.const) == (ys.map Dim.const)) = false := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp [unifyDimList] at h_none
      | cons y ys =>
          simp [BEq.beq]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [BEq.beq]
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            have h_head :
                unifyDim DimSubst.empty (fuel + 1) (.const x) (.const x) =
                  some DimSubst.empty := by
              simpa using (unifyDim_reflexive DimSubst.empty fuel (.const x))
            have h_tail_none :
                unifyDimList DimSubst.empty (fuel + 1)
                  (xs.map Dim.const) (ys.map Dim.const) = none := by
              simpa [unifyDimList, h_head] using h_none
            have h_tail_beq :
                ((xs.map Dim.const) == (ys.map Dim.const)) = false :=
              ih ys h_tail_none
            simp [h_tail_beq]
          · have h_head_none :
                unifyDim DimSubst.empty (fuel + 1) (.const x) (.const y) = none := by
              exact (unifyDim_const_none_iff_ne DimSubst.empty fuel x y).2 hxy
            simp
            intro h_head_true
            have hxy_true : x = y := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h_head_true)
            exact (hxy hxy_true).elim

/-- Packaged constant-dimension kernel contracts for pointwise list unification. -/
structure DimConstListKernelSlice : Prop where
  some_iff_eq :
    ∀ fuel xs ys,
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = some DimSubst.empty ↔ xs = ys
  some_implies_empty :
    ∀ fuel xs ys s',
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = some s' →
        s' = DimSubst.empty
  none_iff_ne :
    ∀ fuel xs ys,
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = none ↔ xs ≠ ys
  decision :
    ∀ fuel xs ys,
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) =
        (if xs = ys then some DimSubst.empty else none)
  head_const_mismatch_none :
    ∀ fuel a b xs ys, a ≠ b →
      unifyDimList DimSubst.empty (fuel + 1)
        (.const a :: xs) (.const b :: ys) = none
  length_mismatch_none :
    ∀ fuel xs ys, xs.length ≠ ys.length →
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = none
  none_implies_beq_false :
    ∀ fuel xs ys,
      unifyDimList DimSubst.empty (fuel + 1)
        (xs.map Dim.const) (ys.map Dim.const) = none →
        ((xs.map Dim.const) == (ys.map Dim.const)) = false

/-- Reusable theorem package for constant-dimension list unification behavior. -/
theorem dimConstListKernelSlice : DimConstListKernelSlice := by
  refine
    { some_iff_eq := ?_
      some_implies_empty := ?_
      none_iff_ne := ?_
      decision := ?_
      head_const_mismatch_none := ?_
      length_mismatch_none := ?_
      none_implies_beq_false := ?_ }
  · intro fuel xs ys
    exact unifyDimList_consts_some_iff_eq fuel xs ys
  · intro fuel xs ys s' h_some
    exact unifyDimList_consts_some_implies_empty fuel xs ys s' h_some
  · intro fuel xs ys
    exact unifyDimList_consts_none_iff_ne fuel xs ys
  · intro fuel xs ys
    exact unifyDimList_consts_decision fuel xs ys
  · intro fuel a b xs ys h_ne
    exact unifyDimList_head_const_mismatch_none fuel a b xs ys h_ne
  · intro fuel xs ys h_len
    exact unifyDimList_consts_length_mismatch_none fuel xs ys h_len
  · intro fuel xs ys h_none
    exact unifyDimList_consts_none_implies_beq_false fuel xs ys h_none
