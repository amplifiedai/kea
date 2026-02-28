/-
  Kea.Properties.PrecisionLeafParity — Precision numeric constructor parity.

  Maps to Rust-side precision typing behavior:
    - Int32/Int64 and Float32/Float64 annotation mismatch diagnostics
    - Reflexive typing/unification for width-qualified numeric constructors

  These theorems certify IntN/FloatN as substitution leaves and provide
  concrete mismatch witnesses across width/signedness distinctions.
-/

import Kea.Properties.UnifyReflexive

/-- IntN is a substitution leaf. -/
theorem intN_is_substitution_leaf (s : Subst) (fuel : Nat) (w : IntWidth) (sgn : Signedness) :
    applySubst s fuel (.intN w sgn) = .intN w sgn := by
  cases fuel <;> simp [applySubst]

/-- FloatN is a substitution leaf. -/
theorem floatN_is_substitution_leaf (s : Subst) (fuel : Nat) (w : FloatWidth) :
    applySubst s fuel (.floatN w) = .floatN w := by
  cases fuel <;> simp [applySubst]

/-- Option(IntN) remains stable under substitution. -/
theorem option_intN_is_substitution_leaf
    (s : Subst) (fuel : Nat) (w : IntWidth) (sgn : Signedness) :
    applySubst s fuel (.option (.intN w sgn)) = .option (.intN w sgn) := by
  cases fuel with
  | zero => rfl
  | succ n =>
    simp [applySubst, intN_is_substitution_leaf s n w sgn]

/-- List(FloatN) remains stable under substitution. -/
theorem list_floatN_is_substitution_leaf (s : Subst) (fuel : Nat) (w : FloatWidth) :
    applySubst s fuel (.list (.floatN w)) = .list (.floatN w) := by
  cases fuel with
  | zero => rfl
  | succ n =>
    simp [applySubst, floatN_is_substitution_leaf s n w]

/-- IntN unifies with itself. -/
theorem intN_unifies_with_self
    (st : UnifyState) (fuel : Nat) (w : IntWidth) (sgn : Signedness) :
    unify st (fuel + 1) (.intN w sgn) (.intN w sgn) = .ok st := by
  simpa using (unifyReflexive' st fuel (.intN w sgn))

/-- FloatN unifies with itself. -/
theorem floatN_unifies_with_self (st : UnifyState) (fuel : Nat) (w : FloatWidth) :
    unify st (fuel + 1) (.floatN w) (.floatN w) = .ok st := by
  simpa using (unifyReflexive' st fuel (.floatN w))

/-- IntN unification is exactly decided by constructor-level BEq. -/
theorem intN_unify_decision
    (st : UnifyState) (fuel : Nat)
    (w1 w2 : IntWidth) (s1 s2 : Signedness) :
    unify st (fuel + 1) (.intN w1 s1) (.intN w2 s2) =
      if (Ty.intN w1 s1 == Ty.intN w2 s2) then .ok st else .err "type mismatch" := by
  by_cases h_eq : (Ty.intN w1 s1 == Ty.intN w2 s2) = true
  · unfold unify
    simp [applySubstCompat, intN_is_substitution_leaf, h_eq]
  · have h_neq : (Ty.intN w1 s1 == Ty.intN w2 s2) = false := by
      cases hbeq : (Ty.intN w1 s1 == Ty.intN w2 s2) with
      | true => exact (h_eq hbeq).elim
      | false => rfl
    unfold unify
    simp [applySubstCompat, intN_is_substitution_leaf, h_neq]

/-- IntN unifies successfully iff constructor-level BEq is true. -/
theorem intN_unify_ok_iff_constructor_beq_true
    (st : UnifyState) (fuel : Nat)
    (w1 w2 : IntWidth) (s1 s2 : Signedness) :
    unify st (fuel + 1) (.intN w1 s1) (.intN w2 s2) = .ok st ↔
      (Ty.intN w1 s1 == Ty.intN w2 s2) = true := by
  rw [intN_unify_decision st fuel w1 w2 s1 s2]
  by_cases hbeq : (Ty.intN w1 s1 == Ty.intN w2 s2) = true
  · simp [hbeq]
  · simp [hbeq]

/-- IntN unifier rejection is equivalent to constructor-level BEq failure. -/
theorem intN_unify_err_iff_constructor_beq_false
    (st : UnifyState) (fuel : Nat)
    (w1 w2 : IntWidth) (s1 s2 : Signedness) :
    unify st (fuel + 1) (.intN w1 s1) (.intN w2 s2) = .err "type mismatch" ↔
      (Ty.intN w1 s1 == Ty.intN w2 s2) = false := by
  constructor
  · intro h_err
    rw [intN_unify_decision st fuel w1 w2 s1 s2] at h_err
    cases hbeq : (Ty.intN w1 s1 == Ty.intN w2 s2) with
    | true =>
        simp [hbeq] at h_err
    | false =>
        simpa [hbeq]
  · intro hbeq_false
    rw [intN_unify_decision st fuel w1 w2 s1 s2]
    simp [hbeq_false]

/-- FloatN unification is exactly decided by constructor-level BEq. -/
theorem floatN_unify_decision
    (st : UnifyState) (fuel : Nat)
    (w1 w2 : FloatWidth) :
    unify st (fuel + 1) (.floatN w1) (.floatN w2) =
      if (Ty.floatN w1 == Ty.floatN w2) then .ok st else .err "type mismatch" := by
  by_cases h_eq : (Ty.floatN w1 == Ty.floatN w2) = true
  · unfold unify
    simp [applySubstCompat, floatN_is_substitution_leaf, h_eq]
  · have h_neq : (Ty.floatN w1 == Ty.floatN w2) = false := by
      cases hbeq : (Ty.floatN w1 == Ty.floatN w2) with
      | true => exact (h_eq hbeq).elim
      | false => rfl
    unfold unify
    simp [applySubstCompat, floatN_is_substitution_leaf, h_neq]

/-- FloatN unifies successfully iff constructor-level BEq is true. -/
theorem floatN_unify_ok_iff_constructor_beq_true
    (st : UnifyState) (fuel : Nat)
    (w1 w2 : FloatWidth) :
    unify st (fuel + 1) (.floatN w1) (.floatN w2) = .ok st ↔
      (Ty.floatN w1 == Ty.floatN w2) = true := by
  rw [floatN_unify_decision st fuel w1 w2]
  by_cases hbeq : (Ty.floatN w1 == Ty.floatN w2) = true
  · simp [hbeq]
  · simp [hbeq]

/-- FloatN unifier rejection is equivalent to constructor-level BEq failure. -/
theorem floatN_unify_err_iff_constructor_beq_false
    (st : UnifyState) (fuel : Nat)
    (w1 w2 : FloatWidth) :
    unify st (fuel + 1) (.floatN w1) (.floatN w2) = .err "type mismatch" ↔
      (Ty.floatN w1 == Ty.floatN w2) = false := by
  constructor
  · intro h_err
    rw [floatN_unify_decision st fuel w1 w2] at h_err
    cases hbeq : (Ty.floatN w1 == Ty.floatN w2) with
    | true =>
        simp [hbeq] at h_err
    | false =>
        simpa [hbeq]
  · intro hbeq_false
    rw [floatN_unify_decision st fuel w1 w2]
    simp [hbeq_false]

/-- Packaged precision constructor unification contracts for IntN/FloatN. -/
structure PrecisionConstructorKernelSlice : Prop where
  intN_ok_iff_constructor_beq_true :
    ∀ st fuel w1 w2 s1 s2,
      unify st (fuel + 1) (.intN w1 s1) (.intN w2 s2) = .ok st ↔
        (Ty.intN w1 s1 == Ty.intN w2 s2) = true
  intN_err_iff_constructor_beq_false :
    ∀ st fuel w1 w2 s1 s2,
      unify st (fuel + 1) (.intN w1 s1) (.intN w2 s2) = .err "type mismatch" ↔
        (Ty.intN w1 s1 == Ty.intN w2 s2) = false
  intN_decision :
    ∀ st fuel w1 w2 s1 s2,
      unify st (fuel + 1) (.intN w1 s1) (.intN w2 s2) =
        if (Ty.intN w1 s1 == Ty.intN w2 s2) then .ok st else .err "type mismatch"
  floatN_ok_iff_constructor_beq_true :
    ∀ st fuel w1 w2,
      unify st (fuel + 1) (.floatN w1) (.floatN w2) = .ok st ↔
        (Ty.floatN w1 == Ty.floatN w2) = true
  floatN_err_iff_constructor_beq_false :
    ∀ st fuel w1 w2,
      unify st (fuel + 1) (.floatN w1) (.floatN w2) = .err "type mismatch" ↔
        (Ty.floatN w1 == Ty.floatN w2) = false
  floatN_decision :
    ∀ st fuel w1 w2,
      unify st (fuel + 1) (.floatN w1) (.floatN w2) =
        if (Ty.floatN w1 == Ty.floatN w2) then .ok st else .err "type mismatch"

/-- Canonical precision constructor kernel package. -/
theorem precisionConstructorKernelSlice : PrecisionConstructorKernelSlice := by
  refine
    { intN_ok_iff_constructor_beq_true := ?_
      intN_err_iff_constructor_beq_false := ?_
      intN_decision := ?_
      floatN_ok_iff_constructor_beq_true := ?_
      floatN_err_iff_constructor_beq_false := ?_
      floatN_decision := ?_ }
  · intro st fuel w1 w2 s1 s2
    exact intN_unify_ok_iff_constructor_beq_true st fuel w1 w2 s1 s2
  · intro st fuel w1 w2 s1 s2
    exact intN_unify_err_iff_constructor_beq_false st fuel w1 w2 s1 s2
  · intro st fuel w1 w2 s1 s2
    exact intN_unify_decision st fuel w1 w2 s1 s2
  · intro st fuel w1 w2
    exact floatN_unify_ok_iff_constructor_beq_true st fuel w1 w2
  · intro st fuel w1 w2
    exact floatN_unify_err_iff_constructor_beq_false st fuel w1 w2
  · intro st fuel w1 w2
    exact floatN_unify_decision st fuel w1 w2

/-- Signedness mismatch on same width does not unify. -/
theorem intN_signedness_mismatch
    (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) (.intN .i32 .signed) (.intN .i32 .unsigned) = .err "type mismatch" := by
  have hneq : (Ty.intN .i32 .signed == Ty.intN .i32 .unsigned) = false := by
    show beqTy (Ty.intN .i32 .signed) (Ty.intN .i32 .unsigned) = false
    native_decide
  unfold unify
  simp [applySubstCompat, intN_is_substitution_leaf, hneq]

/-- Width mismatch on same signedness does not unify. -/
theorem intN_width_mismatch
    (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) (.intN .i32 .signed) (.intN .i64 .signed) = .err "type mismatch" := by
  have hneq : (Ty.intN .i32 .signed == Ty.intN .i64 .signed) = false := by
    show beqTy (Ty.intN .i32 .signed) (Ty.intN .i64 .signed) = false
    native_decide
  unfold unify
  simp [applySubstCompat, intN_is_substitution_leaf, hneq]

/-- Float width mismatch does not unify. -/
theorem floatN_width_mismatch (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) (.floatN .f32) (.floatN .f64) = .err "type mismatch" := by
  have hneq : (Ty.floatN .f32 == Ty.floatN .f64) = false := by
    show beqTy (Ty.floatN .f32) (Ty.floatN .f64) = false
    native_decide
  unfold unify
  simp [applySubstCompat, floatN_is_substitution_leaf, hneq]

/-- IntN and non-IntN types do not unify. -/
theorem intN_non_intN_mismatch (st : UnifyState) :
    unify st 1 (.intN .i32 .signed) .int = .err "type mismatch" := by
  have hneq : (Ty.intN .i32 .signed == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, hneq]

/-- FloatN and non-FloatN types do not unify. -/
theorem floatN_non_floatN_mismatch (st : UnifyState) :
    unify st 1 (.floatN .f32) .float = .err "type mismatch" := by
  have hneq : (Ty.floatN .f32 == Ty.float) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, hneq]

/-- Boundary-sensitive sites where precision constructor checks are enforced. -/
inductive PrecisionBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level precision boundary policy.
    Current scope:
    - `IntN` must match width+signedness exactly
    - `FloatN` must match width exactly
    - non-precision actuals are rejected when precision wrappers are expected
    - otherwise allowed (outside this boundary surface) -/
def precisionBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .intN ew es, .intN aw assn => (ew == aw) && (es == assn)
  | .intN _ _, _ => false
  | .floatN ew, .floatN aw => ew == aw
  | .floatN _, _ => false
  | _, _ => true

/-- Site-level wrapper for precision boundary checks. -/
def precisionBoundaryAllowsAtSite
    (_site : PrecisionBoundarySite) (expected actual : Ty) : Bool :=
  precisionBoundaryAllows expected actual

/-- Precision boundary policy is currently site-invariant. -/
theorem precision_boundary_policy_site_invariant
    (site1 site2 : PrecisionBoundarySite) (expected actual : Ty) :
    precisionBoundaryAllowsAtSite site1 expected actual =
      precisionBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- IntN width mismatch is rejected by boundary policy. -/
theorem precision_boundary_rejects_int_width_mismatch :
    precisionBoundaryAllows
      (.intN .i32 .signed)
      (.intN .i64 .signed)
      = false := by
  native_decide

/-- FloatN width mismatch is rejected by boundary policy. -/
theorem precision_boundary_rejects_float_width_mismatch :
    precisionBoundaryAllows
      (.floatN .f32)
      (.floatN .f64)
      = false := by
  native_decide

/-- Non-precision actuals are rejected when precision wrappers are expected. -/
theorem precision_boundary_rejects_non_precision_actual :
    precisionBoundaryAllows
      (.intN .i32 .signed)
      .int
      = false := by
  native_decide

/-- Packaged precision boundary surface slice:
    site invariance + precision mismatch/non-precision rejection, with closure
    to concrete mismatch/reflexive unifier witnesses. -/
theorem precision_boundary_surface_slice
    (st : UnifyState) (site : PrecisionBoundarySite) :
    (precisionBoundaryAllowsAtSite site
      (.intN .i32 .signed)
      (.intN .i64 .signed) = false)
    ∧
    (precisionBoundaryAllowsAtSite site
      (.floatN .f32)
      (.floatN .f64) = false)
    ∧
    (precisionBoundaryAllowsAtSite site
      (.intN .i32 .signed)
      .int = false)
    ∧
    (unify st 1
      (.intN .i32 .signed)
      (.intN .i64 .signed)
      = .err "type mismatch")
    ∧
    (unify st 1
      (.floatN .f32)
      (.floatN .f64)
      = .err "type mismatch")
    ∧
    (unify st 1
      (.intN .i32 .signed)
      .int
      = .err "type mismatch")
    ∧
    (unify st 1
      (.intN .i32 .signed)
      (.intN .i32 .signed)
      = .ok st)
    ∧
    (unify st 1
      (.floatN .f32)
      (.floatN .f32)
      = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact precision_boundary_rejects_int_width_mismatch
  · cases site <;> exact precision_boundary_rejects_float_width_mismatch
  · cases site <;> exact precision_boundary_rejects_non_precision_actual
  · exact intN_width_mismatch st 0
  · exact floatN_width_mismatch st 0
  · exact intN_non_intN_mismatch st
  · exact intN_unifies_with_self st 0 .i32 .signed
  · exact floatN_unifies_with_self st 0 .f32

/-- Rows with IntN/FloatN fields unify with themselves. -/
theorem precision_row_unification (st : UnifyState) (fuel : Nat) (iLabel fLabel : Label) :
    let r := Row.closed (.cons iLabel (.intN .i32 .signed) (.cons fLabel (.floatN .f32) .nil))
    unify st (fuel + 1) (.row r) (.row r) = .ok st := by
  intro r
  simpa using (unifyReflexive' st fuel (.row r))

/-- IntN has no free type or row variables. -/
theorem intN_has_no_free_vars (w : IntWidth) (sgn : Signedness) :
    freeTypeVars (.intN w sgn) = [] ∧ freeRowVars (.intN w sgn) = [] := by
  simp [freeTypeVars, freeRowVars]

/-- FloatN has no free type or row variables. -/
theorem floatN_has_no_free_vars (w : FloatWidth) :
    freeTypeVars (.floatN w) = [] ∧ freeRowVars (.floatN w) = [] := by
  simp [freeTypeVars, freeRowVars]
