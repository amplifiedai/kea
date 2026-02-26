/- 
  Kea.Properties.ForallParity - Explicit `forall` constructor parity slice.

  Current scope: simplified quantified constructor (`forall vars. body`) is
  modeled in `Ty`, propagated through substitution/unification, and covered by
  constructor-local parity lemmas.
-/

import Kea.Properties.UnifyReflexive

private theorem applySubst_int (s : Subst) : ∀ fuel, applySubst s fuel .int = .int
  | 0 => rfl
  | _ + 1 => rfl

private theorem applySubst_bool (s : Subst) : ∀ fuel, applySubst s fuel .bool = .bool
  | 0 => rfl
  | _ + 1 => rfl

/-- Constructor-level canonical equivalence for quantified types.
    Binder names and vacuous binder-list length are ignored; only body shape matters. -/
def forallCanonicalEq : Ty → Ty → Prop
  | .forall _ body1, .forall _ body2 => body1 = body2
  | _, _ => False

/-- Canonical equivalence is reflexive on `forall` forms. -/
theorem forallCanonicalEq_refl (vars : List String) (body : Ty) :
    forallCanonicalEq (.forall vars body) (.forall vars body) := by
  simp [forallCanonicalEq]

/-- Constructor-level canonical equivalence is symmetric. -/
theorem forallCanonicalEq_symm
    (vars1 vars2 : List String) (body1 body2 : Ty)
    (h : forallCanonicalEq (.forall vars1 body1) (.forall vars2 body2)) :
    forallCanonicalEq (.forall vars2 body2) (.forall vars1 body1) := by
  simp [forallCanonicalEq] at h ⊢
  simp [h]

/-- Constructor-level canonical equivalence is transitive. -/
theorem forallCanonicalEq_trans
    (vars1 vars2 vars3 : List String) (body1 body2 body3 : Ty)
    (h12 : forallCanonicalEq (.forall vars1 body1) (.forall vars2 body2))
    (h23 : forallCanonicalEq (.forall vars2 body2) (.forall vars3 body3)) :
    forallCanonicalEq (.forall vars1 body1) (.forall vars3 body3) := by
  simp [forallCanonicalEq] at h12 h23 ⊢
  simp [h12, h23]

/-- One substitution step over `forall` rewrites body type only. -/
theorem forall_subst_step
    (s : Subst) (fuel : Nat) (vars : List String) (body : Ty) :
    applySubst s (fuel + 1) (.forall vars body) =
      .forall vars (applySubst s fuel body) := by
  simp [applySubst]

/-- With normalized `forall` shapes and failed BEq short-circuit, unification
    reduces to quantified-body unification. -/
theorem forall_unify_reduces_to_body_unify_of_normalized_foralls
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 vars1' vars2' : List String) (body1 body2 body1' body2' : Ty)
    (hleft :
      applySubst st.subst fuel (.forall vars1 body1) = .forall vars1' body1')
    (hright :
      applySubst st.subst fuel (.forall vars2 body2) = .forall vars2' body2')
    (hbeq :
      (applySubst st.subst fuel (.forall vars1 body1) ==
        applySubst st.subst fuel (.forall vars2 body2)) = false) :
    unify st (fuel + 1) (.forall vars1 body1) (.forall vars2 body2) =
      unify st fuel body1' body2' := by
  have hbeq' : (Ty.forall vars1' body1' == Ty.forall vars2' body2') = false := by
    simpa [hleft, hright] using hbeq
  simp [unify, applySubstCompat, hleft, hright, hbeq']

/-- Under normalized `forall` forms, body unification success lifts to
    `forall` unification success. -/
theorem forall_unify_accepts_of_normalized_body_ok_any
    (st st' : UnifyState) (fuel : Nat)
    (vars1 vars2 vars1' vars2' : List String) (body1 body2 body1' body2' : Ty)
    (hleft :
      applySubst st.subst fuel (.forall vars1 body1) = .forall vars1' body1')
    (hright :
      applySubst st.subst fuel (.forall vars2 body2) = .forall vars2' body2')
    (hbeq :
      (applySubst st.subst fuel (.forall vars1 body1) ==
        applySubst st.subst fuel (.forall vars2 body2)) = false)
    (hbody : unify st fuel body1' body2' = .ok st') :
    unify st (fuel + 1) (.forall vars1 body1) (.forall vars2 body2) = .ok st' := by
  rw [forall_unify_reduces_to_body_unify_of_normalized_foralls
    st fuel vars1 vars2 vars1' vars2' body1 body2 body1' body2' hleft hright hbeq]
  exact hbody

/-- Under normalized `forall` forms, body unification success lifts to
    `forall` unification success. -/
theorem forall_unify_accepts_of_normalized_body_ok
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 vars1' vars2' : List String) (body1 body2 body1' body2' : Ty)
    (hleft :
      applySubst st.subst fuel (.forall vars1 body1) = .forall vars1' body1')
    (hright :
      applySubst st.subst fuel (.forall vars2 body2) = .forall vars2' body2')
    (hbeq :
      (applySubst st.subst fuel (.forall vars1 body1) ==
        applySubst st.subst fuel (.forall vars2 body2)) = false)
    (hbody : unify st fuel body1' body2' = .ok st) :
    unify st (fuel + 1) (.forall vars1 body1) (.forall vars2 body2) = .ok st := by
  exact forall_unify_accepts_of_normalized_body_ok_any
    st st fuel vars1 vars2 vars1' vars2' body1 body2 body1' body2'
    hleft hright hbeq hbody

/-- Under normalized `forall` forms, body unification mismatch lifts to
    `forall` unification mismatch. -/
theorem forall_unify_rejects_of_normalized_body_err_any
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 vars1' vars2' : List String) (body1 body2 body1' body2' : Ty)
    (hleft :
      applySubst st.subst fuel (.forall vars1 body1) = .forall vars1' body1')
    (hright :
      applySubst st.subst fuel (.forall vars2 body2) = .forall vars2' body2')
    (hbeq :
      (applySubst st.subst fuel (.forall vars1 body1) ==
        applySubst st.subst fuel (.forall vars2 body2)) = false)
    (e : String)
    (hbody : unify st fuel body1' body2' = .err e) :
    unify st (fuel + 1) (.forall vars1 body1) (.forall vars2 body2) = .err e := by
  rw [forall_unify_reduces_to_body_unify_of_normalized_foralls
    st fuel vars1 vars2 vars1' vars2' body1 body2 body1' body2' hleft hright hbeq]
  exact hbody

/-- Under normalized `forall` forms, body unification mismatch lifts to
    `forall` unification mismatch. -/
theorem forall_unify_rejects_of_normalized_body_err
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 vars1' vars2' : List String) (body1 body2 body1' body2' : Ty)
    (hleft :
      applySubst st.subst fuel (.forall vars1 body1) = .forall vars1' body1')
    (hright :
      applySubst st.subst fuel (.forall vars2 body2) = .forall vars2' body2')
    (hbeq :
      (applySubst st.subst fuel (.forall vars1 body1) ==
        applySubst st.subst fuel (.forall vars2 body2)) = false)
    (hbody : unify st fuel body1' body2' = .err "type mismatch") :
    unify st (fuel + 1) (.forall vars1 body1) (.forall vars2 body2) = .err "type mismatch" := by
  exact forall_unify_rejects_of_normalized_body_err_any
    st fuel vars1 vars2 vars1' vars2' body1 body2 body1' body2'
    hleft hright hbeq "type mismatch" hbody

/-- `forall` unifies with itself. -/
theorem forall_unifies_with_self
    (st : UnifyState) (fuel : Nat) (vars : List String) (body : Ty) :
    unify st (fuel + 1) (.forall vars body) (.forall vars body) = .ok st := by
  simpa using (unifyReflexive' st fuel (.forall vars body))

/-- Quantified binder names are alpha-insensitive at constructor level. -/
theorem forall_alpha_equiv_unifies
    (st : UnifyState) (fuel : Nat) (vars1 vars2 : List String) (body : Ty) :
    unify st (fuel + 2) (.forall vars1 body) (.forall vars2 body) = .ok st := by
  have h_ref : ∀ t : Ty, unify st (fuel + 1) t t = .ok st := by
    intro t
    simpa using (unifyReflexive' st fuel t)
  simp [unify, applySubstCompat, applySubst, h_ref]

/-- Constructor-level unification result is invariant under binder renaming. -/
theorem forall_alpha_invariant_constructor
    (st : UnifyState) (fuel : Nat) (vars1 vars2 : List String) (body : Ty) :
    unify st (fuel + 2) (.forall vars1 body) (.forall vars2 body) =
      unify st (fuel + 2) (.forall vars1 body) (.forall vars1 body) := by
  rw [forall_alpha_equiv_unifies st fuel vars1 vars2 body,
    forall_alpha_equiv_unifies st fuel vars1 vars1 body]

/-- Canonically equivalent `forall` constructors unify successfully. -/
theorem forallCanonicalEq_unifies
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 : List String) (body1 body2 : Ty)
    (hcanon : forallCanonicalEq (.forall vars1 body1) (.forall vars2 body2)) :
    unify st (fuel + 2) (.forall vars1 body1) (.forall vars2 body2) = .ok st := by
  simp [forallCanonicalEq] at hcanon
  rcases hcanon with rfl
  exact forall_alpha_equiv_unifies st fuel vars1 vars2 body1

/-- Canonically equivalent `forall` constructors also unify in the symmetric
    direction. -/
theorem forallCanonicalEq_unifies_symm
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 : List String) (body1 body2 : Ty)
    (hcanon : forallCanonicalEq (.forall vars1 body1) (.forall vars2 body2)) :
    unify st (fuel + 2) (.forall vars2 body2) (.forall vars1 body1) = .ok st := by
  exact forallCanonicalEq_unifies st fuel vars2 vars1 body2 body1
    (forallCanonicalEq_symm vars1 vars2 body1 body2 hcanon)

/-- Canonical-equivalence transitivity lifts to unification success for the
    composed endpoints. -/
theorem forallCanonicalEq_unifies_trans
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 vars3 : List String) (body1 body2 body3 : Ty)
    (h12 : forallCanonicalEq (.forall vars1 body1) (.forall vars2 body2))
    (h23 : forallCanonicalEq (.forall vars2 body2) (.forall vars3 body3)) :
    unify st (fuel + 2) (.forall vars1 body1) (.forall vars3 body3) = .ok st := by
  exact forallCanonicalEq_unifies st fuel vars1 vars3 body1 body3
    (forallCanonicalEq_trans vars1 vars2 vars3 body1 body2 body3 h12 h23)

/-- Packaged canonical-equivalence closure slice for `forall`: transitive
    canonical relation and corresponding unification success in forward,
    symmetric, and transitive directions. -/
theorem forall_canonical_equivalence_slice
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 vars3 : List String) (body1 body2 body3 : Ty)
    (h12 : forallCanonicalEq (.forall vars1 body1) (.forall vars2 body2))
    (h23 : forallCanonicalEq (.forall vars2 body2) (.forall vars3 body3)) :
    forallCanonicalEq (.forall vars1 body1) (.forall vars3 body3)
    ∧
    unify st (fuel + 2) (.forall vars1 body1) (.forall vars2 body2) = .ok st
    ∧
    unify st (fuel + 2) (.forall vars2 body2) (.forall vars1 body1) = .ok st
    ∧
    unify st (fuel + 2) (.forall vars1 body1) (.forall vars3 body3) = .ok st := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact forallCanonicalEq_trans vars1 vars2 vars3 body1 body2 body3 h12 h23
  · exact forallCanonicalEq_unifies st fuel vars1 vars2 body1 body2 h12
  · exact forallCanonicalEq_unifies_symm st fuel vars1 vars2 body1 body2 h12
  · exact forallCanonicalEq_unifies_trans st fuel vars1 vars2 vars3 body1 body2 body3 h12 h23

/-- Alpha-equivalent binder renaming is accepted for `forall`. -/
theorem forall_alpha_renaming_accepts (st : UnifyState) :
    unify st 2
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["b"] (.function (.cons .int .nil) .int))
      = .ok st := by
  have h_neq :
      (Ty.forall ["a"] (.function (.cons .int .nil) .int) ==
        Ty.forall ["b"] (.function (.cons .int .nil) .int)) = false := by
    native_decide
  have h_body_eq :
      (Ty.function (.cons .int .nil) .int == Ty.function (.cons .int .nil) .int) = true := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq, h_body_eq]

/-- Vacuous extra binders are ignored in `forall` unification. -/
theorem forall_vacuous_binder_accepts (st : UnifyState) :
    unify st 2
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["a", "b"] (.function (.cons .int .nil) .int))
      = .ok st := by
  have h_neq :
      (Ty.forall ["a"] (.function (.cons .int .nil) .int) ==
        Ty.forall ["a", "b"] (.function (.cons .int .nil) .int)) = false := by
    native_decide
  have h_body_eq :
      (Ty.function (.cons .int .nil) .int == Ty.function (.cons .int .nil) .int) = true := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq, h_body_eq]

/-- Distinct quantified bodies reject `forall` unification. -/
theorem forall_body_mismatch (st : UnifyState) :
    unify st 2
      (.forall ["a"] .int)
      (.forall ["a"] .bool)
      = .err "type mismatch" := by
  have h_neq :
      (Ty.forall ["a"] .int == Ty.forall ["a"] .bool) = false := by
    native_decide
  have h_int_bool : (Ty.int == Ty.bool) = false := by
    native_decide
  simp [unify, applySubstCompat, applySubst, h_neq, h_int_bool]

/-- Packaged concrete surface witness for quantified compatibility:
    alpha-renamed binders and vacuous extra binders are accepted, while
    quantified body mismatch is rejected. -/
theorem forall_surface_boundary_slice (st : UnifyState) :
    (unify st 2
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["b"] (.function (.cons .int .nil) .int))
      = .ok st)
    ∧
    (unify st 2
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["a", "b"] (.function (.cons .int .nil) .int))
      = .ok st)
    ∧
    (unify st 2
      (.forall ["a"] .int)
      (.forall ["a"] .bool)
      = .err "type mismatch") := by
  refine ⟨?_, ?_, ?_⟩
  · exact forall_alpha_renaming_accepts st
  · exact forall_vacuous_binder_accepts st
  · exact forall_body_mismatch st

/-- Distinct quantified bodies reject `forall` unification at any outer
    successor+1 fuel. -/
theorem forall_body_mismatch_any_fuel
    (st : UnifyState) (fuel : Nat) (vars1 vars2 : List String) :
    unify st (fuel + 2)
      (.forall vars1 .int)
      (.forall vars2 .bool)
      = .err "type mismatch" := by
  have hleft :
      applySubst st.subst (fuel + 1) (.forall vars1 .int) =
        .forall vars1 .int := by
    simp [applySubst, applySubst_int st.subst fuel]
  have hright :
      applySubst st.subst (fuel + 1) (.forall vars2 .bool) =
        .forall vars2 .bool := by
    simp [applySubst, applySubst_bool st.subst fuel]
  have h_int_bool : (Ty.int == Ty.bool) = false := by
    native_decide
  have hbeq :
      (applySubst st.subst (fuel + 1) (.forall vars1 .int) ==
        applySubst st.subst (fuel + 1) (.forall vars2 .bool)) = false := by
    have hbeq' : (Ty.forall vars1 .int == Ty.forall vars2 .bool) = false := by
      simp [BEq.beq, beqTy]
    simpa [hleft, hright] using hbeq'
  have hbody : unify st (fuel + 1) .int .bool = .err "type mismatch" := by
    have h_int_subst : applySubst st.subst fuel .int = .int := applySubst_int st.subst fuel
    have h_bool_subst : applySubst st.subst fuel .bool = .bool := applySubst_bool st.subst fuel
    simp [unify, applySubstCompat, h_int_subst, h_bool_subst, h_int_bool]
  exact forall_unify_rejects_of_normalized_body_err
    st (fuel + 1) vars1 vars2 vars1 vars2 .int .bool .int .bool
    hleft hright hbeq hbody

/-- At any outer successor+1 fuel, normalized body unification errors propagate
    through `forall` unification unchanged. -/
theorem forall_body_error_propagates_any_fuel
    (st : UnifyState) (fuel : Nat)
    (vars1 vars2 : List String) (body1 body2 : Ty)
    (e : String)
    (hbeq :
      (Ty.forall vars1 (applySubst st.subst fuel body1) ==
        Ty.forall vars2 (applySubst st.subst fuel body2)) = false)
    (hbody :
      unify st (fuel + 1) (applySubst st.subst fuel body1) (applySubst st.subst fuel body2) = .err e) :
    unify st (fuel + 2)
      (.forall vars1 body1)
      (.forall vars2 body2)
      = .err e := by
  have hleft :
      applySubst st.subst (fuel + 1) (.forall vars1 body1) =
        .forall vars1 (applySubst st.subst fuel body1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.forall vars2 body2) =
        .forall vars2 (applySubst st.subst fuel body2) := by
    simp [applySubst]
  have hbeq' :
      (applySubst st.subst (fuel + 1) (.forall vars1 body1) ==
        applySubst st.subst (fuel + 1) (.forall vars2 body2)) = false := by
    simpa [hleft, hright] using hbeq
  exact forall_unify_rejects_of_normalized_body_err_any
    st (fuel + 1) vars1 vars2 vars1 vars2 body1 body2
    (applySubst st.subst fuel body1) (applySubst st.subst fuel body2)
    hleft hright hbeq' e hbody

/-- At any outer successor+1 fuel, normalized body unification success
    propagates through `forall` unification with the same resulting state. -/
theorem forall_body_success_propagates_any_fuel
    (st st' : UnifyState) (fuel : Nat)
    (vars1 vars2 : List String) (body1 body2 : Ty)
    (hbeq :
      (Ty.forall vars1 (applySubst st.subst fuel body1) ==
        Ty.forall vars2 (applySubst st.subst fuel body2)) = false)
    (hbody :
      unify st (fuel + 1) (applySubst st.subst fuel body1) (applySubst st.subst fuel body2) = .ok st') :
    unify st (fuel + 2)
      (.forall vars1 body1)
      (.forall vars2 body2)
      = .ok st' := by
  have hleft :
      applySubst st.subst (fuel + 1) (.forall vars1 body1) =
        .forall vars1 (applySubst st.subst fuel body1) := by
    simp [applySubst]
  have hright :
      applySubst st.subst (fuel + 1) (.forall vars2 body2) =
        .forall vars2 (applySubst st.subst fuel body2) := by
    simp [applySubst]
  have hbeq' :
      (applySubst st.subst (fuel + 1) (.forall vars1 body1) ==
        applySubst st.subst (fuel + 1) (.forall vars2 body2)) = false := by
    simpa [hleft, hright] using hbeq
  exact forall_unify_accepts_of_normalized_body_ok_any
    st st' (fuel + 1) vars1 vars2 vars1 vars2 body1 body2
    (applySubst st.subst fuel body1) (applySubst st.subst fuel body2)
    hleft hright hbeq' hbody

/-- `forall` free vars are exactly the free vars of its body. -/
theorem forall_free_vars (vars : List String) (body : Ty) :
    freeTypeVars (.forall vars body) = freeTypeVars body /\
      freeRowVars (.forall vars body) = freeRowVars body := by
  simp [freeTypeVars, freeRowVars]

/-- Packaged structural slice for quantified constructors: substitution-step,
    reflexive unification, and free-variable projection for `forall`. -/
theorem forall_structural_slice
    (s : Subst) (st : UnifyState) (fuel : Nat) (vars : List String) (body : Ty) :
    (applySubst s (fuel + 1) (.forall vars body) =
      .forall vars (applySubst s fuel body))
    ∧
    (unify st (fuel + 1) (.forall vars body) (.forall vars body) = .ok st)
    ∧
    (freeTypeVars (.forall vars body) = freeTypeVars body
      ∧ freeRowVars (.forall vars body) = freeRowVars body) := by
  refine ⟨?_, ?_, ?_⟩
  · exact forall_subst_step s fuel vars body
  · exact forall_unifies_with_self st fuel vars body
  · exact forall_free_vars vars body

/-- Boundary-sensitive sites where explicit `forall` contracts are enforced. -/
inductive ForallBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level boundary predicate for explicit `forall` contracts.
    Current policy is site-invariant and body-shape based:
    - expected `forall`, actual `forall` => body-shape equality required
    - expected `forall`, non-`forall` actual => reject
    - otherwise => allow (outside this boundary surface) -/
def forallBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .forall _ expectedBody, .forall _ actualBody => expectedBody == actualBody
  | .forall _ _, _ => false
  | _, _ => true

/-- Site-level wrapper for explicit `forall` boundary checks. -/
def forallBoundaryAllowsAtSite
    (_site : ForallBoundarySite) (expected actual : Ty) : Bool :=
  forallBoundaryAllows expected actual

/-- `forall` boundary policy is currently site-invariant. -/
theorem forall_boundary_policy_site_invariant
    (site1 site2 : ForallBoundarySite) (expected actual : Ty) :
    forallBoundaryAllowsAtSite site1 expected actual =
      forallBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Alpha-renamed binders satisfy the boundary policy (body shape unchanged). -/
theorem forall_boundary_allows_alpha_renaming :
    forallBoundaryAllows
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["b"] (.function (.cons .int .nil) .int))
      = true := by
  native_decide

/-- Vacuous extra binders satisfy the boundary policy (body shape unchanged). -/
theorem forall_boundary_allows_vacuous_binders :
    forallBoundaryAllows
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["a", "b"] (.function (.cons .int .nil) .int))
      = true := by
  native_decide

/-- Distinct quantified body shapes are rejected by the boundary policy. -/
theorem forall_boundary_rejects_body_mismatch :
    forallBoundaryAllows
      (.forall ["a"] .int)
      (.forall ["b"] .bool)
      = false := by
  native_decide

/-- Non-quantified actual values do not satisfy an expected `forall` boundary. -/
theorem forall_boundary_rejects_nonforall_actual :
    forallBoundaryAllows
      (.forall ["a"] .int)
      .int
      = false := by
  native_decide

/-- Concrete unifier witness: a quantified type and a non-quantified type do
    not unify. -/
theorem forall_nonforall_mismatch (st : UnifyState) :
    unify st 2
      (.forall ["a"] .int)
      .int
      = .err "type mismatch" := by
  have h_neq : (Ty.forall ["a"] .int == Ty.int) = false := by
    native_decide
  unfold unify
  simp [applySubstCompat, applySubst, h_neq]

/-- Packaged higher-rank surface boundary slice:
    site invariance + alpha/vacuous acceptance + quantified-body mismatch
    rejection, with closure to concrete unifier outcomes. -/
theorem forall_boundary_surface_slice (st : UnifyState)
    (site : ForallBoundarySite) :
    (forallBoundaryAllowsAtSite site
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["b"] (.function (.cons .int .nil) .int))
      = true)
    ∧
    (forallBoundaryAllowsAtSite site
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["a", "b"] (.function (.cons .int .nil) .int))
      = true)
    ∧
    (forallBoundaryAllowsAtSite site
      (.forall ["a"] .int)
      (.forall ["b"] .bool)
      = false)
    ∧
    (unify st 2
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["b"] (.function (.cons .int .nil) .int))
      = .ok st)
    ∧
    (unify st 2
      (.forall ["a"] (.function (.cons .int .nil) .int))
      (.forall ["a", "b"] (.function (.cons .int .nil) .int))
      = .ok st)
    ∧
    (unify st 2
      (.forall ["a"] .int)
      (.forall ["a"] .bool)
      = .err "type mismatch")
    ∧
    (unify st 2
      (.forall ["a"] .int)
      .int
      = .err "type mismatch") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact forall_boundary_allows_alpha_renaming
  · cases site <;> exact forall_boundary_allows_vacuous_binders
  · cases site <;> exact forall_boundary_rejects_body_mismatch
  · exact forall_alpha_renaming_accepts st
  · exact forall_vacuous_binder_accepts st
  · exact forall_body_mismatch st
  · exact forall_nonforall_mismatch st
