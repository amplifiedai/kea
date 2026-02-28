/-
  Kea.Properties.DecimalParity — Decimal constructor parity slice.

  Current scope: decimal is modeled as a dimensioned constructor in `Ty` and
  participates in substitution/unification through BEq decomposition.
  Full dim-aware unifier integration remains future work.
-/

import Kea.Properties.UnifyReflexive
import Kea.Dimensions

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases h_beq : (a == b) with
  | false => rfl
  | true =>
    have hab : a = b := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h_beq)
    exact (h hab).elim

/-- Decimal is a substitution leaf under the current substitution model. -/
theorem decimal_is_substitution_leaf (s : Subst) (fuel : Nat) (p sc : Dim) :
    applySubst s fuel (.decimal p sc) = .decimal p sc := by
  cases fuel <;> simp [applySubst]

/-- Decimal unifies with itself. -/
theorem decimal_unifies_with_self (st : UnifyState) (fuel : Nat) (p sc : Dim) :
    unify st (fuel + 1) (.decimal p sc) (.decimal p sc) = .ok st := by
  simpa using (unifyReflexive' st fuel (.decimal p sc))

/-- Decimal unifies when constructor-level BEq succeeds. -/
theorem decimal_unify_of_constructor_beq_true
    (st : UnifyState) (fuel : Nat) (p1 p2 s1 s2 : Dim)
    (h_eq : (Ty.decimal p1 s1 == Ty.decimal p2 s2) = true) :
    unify st (fuel + 1) (.decimal p1 s1) (.decimal p2 s2) = .ok st := by
  unfold unify
  simp [applySubstCompat, decimal_is_substitution_leaf, h_eq]

/-- Decimal fails to unify when constructor-level BEq fails. -/
theorem decimal_unify_of_constructor_beq_false
    (st : UnifyState) (fuel : Nat) (p1 p2 s1 s2 : Dim)
    (h_neq : (Ty.decimal p1 s1 == Ty.decimal p2 s2) = false) :
    unify st (fuel + 1) (.decimal p1 s1) (.decimal p2 s2) = .err "type mismatch" := by
  unfold unify
  simp [applySubstCompat, decimal_is_substitution_leaf, h_neq]

/-- Decimal unification is exactly decided by constructor-level BEq. -/
theorem decimal_unify_decision
    (st : UnifyState) (fuel : Nat) (p1 p2 s1 s2 : Dim) :
    unify st (fuel + 1) (.decimal p1 s1) (.decimal p2 s2) =
      if (Ty.decimal p1 s1 == Ty.decimal p2 s2) then .ok st else .err "type mismatch" := by
  by_cases h_eq : (Ty.decimal p1 s1 == Ty.decimal p2 s2) = true
  · simp [decimal_unify_of_constructor_beq_true, h_eq]
  · have h_neq : (Ty.decimal p1 s1 == Ty.decimal p2 s2) = false := by
      cases hbeq : (Ty.decimal p1 s1 == Ty.decimal p2 s2) with
      | true => exact (h_eq hbeq).elim
      | false => rfl
    simp [decimal_unify_of_constructor_beq_false, h_neq]

/-- Decimal unifies successfully iff constructor-level BEq is true. -/
theorem decimal_unify_ok_iff_constructor_beq_true
    (st : UnifyState) (fuel : Nat) (p1 p2 s1 s2 : Dim) :
    unify st (fuel + 1) (.decimal p1 s1) (.decimal p2 s2) = .ok st ↔
      (Ty.decimal p1 s1 == Ty.decimal p2 s2) = true := by
  constructor
  · intro h_unify
    have h_dec := decimal_unify_decision st fuel p1 p2 s1 s2
    rw [h_dec] at h_unify
    cases hbeq : (Ty.decimal p1 s1 == Ty.decimal p2 s2) with
    | true =>
        rfl
    | false =>
        simp [hbeq] at h_unify
  · intro hbeq
    exact decimal_unify_of_constructor_beq_true st fuel p1 p2 s1 s2 hbeq

/-- Decimal precision mismatch (with equal scale) does not unify. -/
theorem decimal_precision_mismatch
    (st : UnifyState) (fuel p1 p2 scale : Nat) (h : p1 ≠ p2) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const scale))
      (.decimal (.const p2) (.const scale))
      = .err "type mismatch" := by
  have h_dim : ((Dim.const p1 : Dim) == Dim.const p2) = false := by
    change (p1 == p2) = false
    exact nat_beq_false_of_ne h
  have h_neq :
      (Ty.decimal (.const p1) (.const scale) == Ty.decimal (.const p2) (.const scale)) = false := by
    show beqTy (Ty.decimal (.const p1) (.const scale)) (Ty.decimal (.const p2) (.const scale)) = false
    simp [beqTy, instBEqDim, h_dim]
  unfold unify
  simp [applySubstCompat, decimal_is_substitution_leaf, h_neq]

/-- Decimal scale mismatch (with equal precision) does not unify. -/
theorem decimal_scale_mismatch
    (st : UnifyState) (fuel prec s1 s2 : Nat) (h : s1 ≠ s2) :
    unify st (fuel + 1)
      (.decimal (.const prec) (.const s1))
      (.decimal (.const prec) (.const s2))
      = .err "type mismatch" := by
  have h_dim : ((Dim.const s1 : Dim) == Dim.const s2) = false := by
    change (s1 == s2) = false
    exact nat_beq_false_of_ne h
  have h_neq :
      (Ty.decimal (.const prec) (.const s1) == Ty.decimal (.const prec) (.const s2)) = false := by
    show beqTy (Ty.decimal (.const prec) (.const s1)) (Ty.decimal (.const prec) (.const s2)) = false
    simp [beqTy, instBEqDim, h_dim]
  unfold unify
  simp [applySubstCompat, decimal_is_substitution_leaf, h_neq]

/-- Decimal has no free type or row variables. -/
theorem decimal_has_no_free_vars (p sc : Dim) :
    freeTypeVars (.decimal p sc) = [] ∧ freeRowVars (.decimal p sc) = [] := by
  simp [freeTypeVars, freeRowVars]

/--
Bridge slice: dim-kernel reflexivity premises are sufficient to recover the
decimal reflexive unification witness in the current decimal BEq model.
-/
theorem decimal_reflexive_of_dim_kernel_reflexive
    (fuel : Nat) (p sc : Dim)
    (_h_p : unifyDim DimSubst.empty fuel p p = some DimSubst.empty)
    (_h_sc : unifyDim DimSubst.empty fuel sc sc = some DimSubst.empty) :
    ∀ st, unify st (fuel + 1) (.decimal p sc) (.decimal p sc) = .ok st := by
  intro st
  exact decimal_unifies_with_self st fuel p sc

/-- Constant-dimension kernel success lifts to decimal-unifier success. -/
theorem decimal_unify_consts_of_dim_kernel_success
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat)
    (h_prec :
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = some DimSubst.empty)
    (h_scale :
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = some DimSubst.empty) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      = .ok st := by
  have h_p_beq_true : (p1 == p2) = true := by
    by_cases hp : (p1 == p2) = true
    · exact hp
    · have hp_false : (p1 == p2) = false := by
        cases hpb : (p1 == p2) with
        | true => exact (hp hpb).elim
        | false => rfl
      have h_dec := unifyDim_const_decision DimSubst.empty fuel p1 p2
      rw [h_dec] at h_prec
      simp [hp_false] at h_prec
  have h_s_beq_true : (s1 == s2) = true := by
    by_cases hs : (s1 == s2) = true
    · exact hs
    · have hs_false : (s1 == s2) = false := by
        cases hsb : (s1 == s2) with
        | true => exact (hs hsb).elim
        | false => rfl
      have h_dec := unifyDim_const_decision DimSubst.empty fuel s1 s2
      rw [h_dec] at h_scale
      simp [hs_false] at h_scale
  have hp_eq : p1 = p2 := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h_p_beq_true)
  have hs_eq : s1 = s2 := Nat.eq_of_beq_eq_true (by simpa [BEq.beq] using h_s_beq_true)
  have h_dec_beq :
      (Ty.decimal (.const p1) (.const s1) == Ty.decimal (.const p2) (.const s2)) = true := by
    subst hp_eq
    subst hs_eq
    simp [BEq.beq, beqTy]
  exact decimal_unify_of_constructor_beq_true st fuel
    (.const p1) (.const p2) (.const s1) (.const s2) h_dec_beq

/-- Precision-kernel failure on constant dimensions forces decimal rejection. -/
theorem decimal_unify_consts_reject_of_prec_dim_kernel_none
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat)
    (h_prec :
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      = .err "type mismatch" := by
  have hp_ne : p1 ≠ p2 := by
    intro hp_eq
    cases hp_eq
    have h_self : unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p1) = some DimSubst.empty := by
      simpa using (unifyDim_reflexive DimSubst.empty fuel (.const p1))
    have : False := by
      rw [h_prec] at h_self
      cases h_self
    exact this.elim
  have h_p_beq_false : ((Dim.const p1 : Dim) == Dim.const p2) = false := by
    change (p1 == p2) = false
    exact nat_beq_false_of_ne hp_ne
  have h_dec_beq :
      (Ty.decimal (.const p1) (.const s1) == Ty.decimal (.const p2) (.const s2)) = false := by
    show beqTy (Ty.decimal (.const p1) (.const s1)) (Ty.decimal (.const p2) (.const s2)) = false
    simp [beqTy, instBEqDim, h_p_beq_false]
  exact decimal_unify_of_constructor_beq_false st fuel
    (.const p1) (.const p2) (.const s1) (.const s2) h_dec_beq

/-- Scale-kernel failure on constant dimensions forces decimal rejection. -/
theorem decimal_unify_consts_reject_of_scale_dim_kernel_none
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat)
    (h_scale :
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      = .err "type mismatch" := by
  have hs_ne : s1 ≠ s2 := by
    intro hs_eq
    cases hs_eq
    have h_self : unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s1) = some DimSubst.empty := by
      simpa using (unifyDim_reflexive DimSubst.empty fuel (.const s1))
    have : False := by
      rw [h_scale] at h_self
      cases h_self
    exact this.elim
  have h_s_beq_false : ((Dim.const s1 : Dim) == Dim.const s2) = false := by
    change (s1 == s2) = false
    exact nat_beq_false_of_ne hs_ne
  have h_dec_beq :
      (Ty.decimal (.const p1) (.const s1) == Ty.decimal (.const p2) (.const s2)) = false := by
    show beqTy (Ty.decimal (.const p1) (.const s1)) (Ty.decimal (.const p2) (.const s2)) = false
    simp [beqTy, instBEqDim, h_s_beq_false]
  exact decimal_unify_of_constructor_beq_false st fuel
    (.const p1) (.const p2) (.const s1) (.const s2) h_dec_beq

/-- Any constant-dimension kernel failure forces decimal unifier rejection. -/
theorem decimal_unify_consts_reject_of_dim_kernel_none
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat)
    (h_none :
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none ∨
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      = .err "type mismatch" := by
  cases h_none with
  | inl h_prec =>
      exact decimal_unify_consts_reject_of_prec_dim_kernel_none st fuel p1 p2 s1 s2 h_prec
  | inr h_scale =>
      exact decimal_unify_consts_reject_of_scale_dim_kernel_none st fuel p1 p2 s1 s2 h_scale

/-- Decimal constant-dimension unifier success iff both dim-kernel checks succeed. -/
theorem decimal_unify_consts_ok_iff_dim_kernel_success
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      = .ok st ↔
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = some DimSubst.empty ∧
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = some DimSubst.empty := by
  constructor
  · intro h_ok
    have h_prec_not_none :
        unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none -> False := by
      intro h_prec_none
      have h_err := decimal_unify_consts_reject_of_prec_dim_kernel_none st fuel p1 p2 s1 s2 h_prec_none
      rw [h_ok] at h_err
      cases h_err
    have h_scale_not_none :
        unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none -> False := by
      intro h_scale_none
      have h_err := decimal_unify_consts_reject_of_scale_dim_kernel_none st fuel p1 p2 s1 s2 h_scale_none
      rw [h_ok] at h_err
      cases h_err
    have h_prec_dec := unifyDim_const_decision DimSubst.empty fuel p1 p2
    have h_scale_dec := unifyDim_const_decision DimSubst.empty fuel s1 s2
    have h_prec :
        unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = some DimSubst.empty := by
      cases hpb : (p1 == p2) with
      | true =>
          simpa [hpb] using h_prec_dec
      | false =>
          have h_none :
              unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none := by
            simpa [hpb] using h_prec_dec
          exact (h_prec_not_none h_none).elim
    have h_scale :
        unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = some DimSubst.empty := by
      cases hsb : (s1 == s2) with
      | true =>
          simpa [hsb] using h_scale_dec
      | false =>
          have h_none :
              unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none := by
            simpa [hsb] using h_scale_dec
          exact (h_scale_not_none h_none).elim
    exact ⟨h_prec, h_scale⟩
  · intro h_dim
    exact decimal_unify_consts_of_dim_kernel_success st fuel p1 p2 s1 s2 h_dim.1 h_dim.2

/-- Decimal constant-dimension unifier rejects iff either dim-kernel check fails. -/
theorem decimal_unify_consts_err_iff_dim_kernel_none
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      = .err "type mismatch" ↔
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none ∨
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none := by
  constructor
  · intro h_err
    by_cases h_prec_none :
        unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none
    · exact Or.inl h_prec_none
    · by_cases h_scale_none :
          unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none
      · exact Or.inr h_scale_none
      · have hp_eq : p1 = p2 := by
          by_contra hp_ne
          exact h_prec_none
            ((unifyDim_const_none_iff_ne DimSubst.empty fuel p1 p2).2 hp_ne)
        have hs_eq : s1 = s2 := by
          by_contra hs_ne
          exact h_scale_none
            ((unifyDim_const_none_iff_ne DimSubst.empty fuel s1 s2).2 hs_ne)
        have h_prec_some :
            unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = some DimSubst.empty :=
          (unifyDim_const_some_iff_eq DimSubst.empty fuel p1 p2).2 hp_eq
        have h_scale_some :
            unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = some DimSubst.empty :=
          (unifyDim_const_some_iff_eq DimSubst.empty fuel s1 s2).2 hs_eq
        have h_ok := decimal_unify_consts_of_dim_kernel_success st fuel p1 p2 s1 s2
          h_prec_some h_scale_some
        rw [h_ok] at h_err
        cases h_err
  · intro h_none
    exact decimal_unify_consts_reject_of_dim_kernel_none st fuel p1 p2 s1 s2 h_none

/-- Decimal constant-dimension unifier result is decided by dim-kernel failure. -/
theorem decimal_unify_consts_decision_of_dim_kernel_none
    (st : UnifyState) (fuel p1 p2 s1 s2 : Nat) :
    unify st (fuel + 1)
      (.decimal (.const p1) (.const s1))
      (.decimal (.const p2) (.const s2))
      =
      if (unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none ∨
          unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none)
      then .err "type mismatch"
      else .ok st := by
  by_cases h_none :
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none ∨
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none
  · have h_err := decimal_unify_consts_reject_of_dim_kernel_none st fuel p1 p2 s1 s2 h_none
    simp [h_none, h_err]
  · have h_prec_some :
      unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = some DimSubst.empty := by
      by_contra h_prec_not_some
      have h_prec_dec := unifyDim_const_decision DimSubst.empty fuel p1 p2
      cases hpb : (p1 == p2) with
      | true =>
          have h_prec_eq :
              unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = some DimSubst.empty := by
            simpa [hpb] using h_prec_dec
          exact h_prec_not_some h_prec_eq
      | false =>
          have h_prec_none :
              unifyDim DimSubst.empty (fuel + 1) (.const p1) (.const p2) = none := by
            simpa [hpb] using h_prec_dec
          exact h_none (Or.inl h_prec_none)
    have h_scale_some :
      unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = some DimSubst.empty := by
      by_contra h_scale_not_some
      have h_scale_dec := unifyDim_const_decision DimSubst.empty fuel s1 s2
      cases hsb : (s1 == s2) with
      | true =>
          have h_scale_eq :
              unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = some DimSubst.empty := by
            simpa [hsb] using h_scale_dec
          exact h_scale_not_some h_scale_eq
      | false =>
          have h_scale_none :
              unifyDim DimSubst.empty (fuel + 1) (.const s1) (.const s2) = none := by
            simpa [hsb] using h_scale_dec
          exact h_none (Or.inr h_scale_none)
    have h_ok := decimal_unify_consts_of_dim_kernel_success st fuel p1 p2 s1 s2
      h_prec_some h_scale_some
    simp [h_none, h_ok]

/-- Decimal and non-decimal types do not unify. -/
theorem decimal_non_decimal_mismatch (st : UnifyState) :
    unify st 1
      (.decimal (.const 10) (.const 2))
      .int
      = .err "type mismatch" := by
  have h_neq : (Ty.decimal (.const 10) (.const 2) == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq]

/-- Boundary-sensitive sites where decimal shape checks are enforced. -/
inductive DecimalBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level decimal boundary policy.
    Current scope:
    - decimal precision and scale must both match when decimal wrappers are
      expected/actual
    - non-decimal actuals are rejected when decimal wrappers are expected
    - otherwise allowed (outside this boundary surface) -/
def decimalBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .decimal p1 s1, .decimal p2 s2 => (p1 == p2) && (s1 == s2)
  | .decimal _ _, _ => false
  | _, _ => true

/-- Site-level wrapper for decimal boundary checks. -/
def decimalBoundaryAllowsAtSite
    (_site : DecimalBoundarySite) (expected actual : Ty) : Bool :=
  decimalBoundaryAllows expected actual

/-- Decimal boundary policy is currently site-invariant. -/
theorem decimal_boundary_policy_site_invariant
    (site1 site2 : DecimalBoundarySite) (expected actual : Ty) :
    decimalBoundaryAllowsAtSite site1 expected actual =
      decimalBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Decimal scale mismatch is rejected by boundary policy. -/
theorem decimal_boundary_rejects_scale_mismatch :
    decimalBoundaryAllows
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 10) (.const 3))
      = false := by
  native_decide

/-- Decimal precision mismatch is rejected by boundary policy. -/
theorem decimal_boundary_rejects_precision_mismatch :
    decimalBoundaryAllows
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 11) (.const 2))
      = false := by
  native_decide

/-- Non-decimal actuals are rejected when decimal wrappers are expected. -/
theorem decimal_boundary_rejects_non_decimal_actual :
    decimalBoundaryAllows
      (.decimal (.const 10) (.const 2))
      .int
      = false := by
  native_decide

/-- Packaged decimal boundary surface slice:
    site invariance + decimal precision/scale mismatch and non-decimal
    rejection, with closure to concrete mismatch/reflexive unifier witnesses. -/
theorem decimal_boundary_surface_slice
    (st : UnifyState) (site : DecimalBoundarySite) :
    (decimalBoundaryAllowsAtSite site
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 10) (.const 3)) = false)
    ∧
    (decimalBoundaryAllowsAtSite site
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 11) (.const 2)) = false)
    ∧
    (decimalBoundaryAllowsAtSite site
      (.decimal (.const 10) (.const 2))
      .int = false)
    ∧
    (unify st 1
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 10) (.const 3))
      = .err "type mismatch")
    ∧
    (unify st 1
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 11) (.const 2))
      = .err "type mismatch")
    ∧
    (unify st 1
      (.decimal (.const 10) (.const 2))
      .int
      = .err "type mismatch")
    ∧
    (unify st 1
      (.decimal (.const 10) (.const 2))
      (.decimal (.const 10) (.const 2))
      = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact decimal_boundary_rejects_scale_mismatch
  · cases site <;> exact decimal_boundary_rejects_precision_mismatch
  · cases site <;> exact decimal_boundary_rejects_non_decimal_actual
  · exact decimal_scale_mismatch st 0 10 2 3 (by decide)
  · exact decimal_precision_mismatch st 0 10 11 2 (by decide)
  · exact decimal_non_decimal_mismatch st
  · exact decimal_unifies_with_self st 0 (.const 10) (.const 2)
