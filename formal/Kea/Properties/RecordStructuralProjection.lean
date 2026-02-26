/-
  Property: Named records structurally project.

  Corresponds to: prop_tests.rs `named_record_structural_projection` (:678)

  A named record `record User { name: String, age: Int }` should always
  unify with an anonymous record `#{ name: String, age: Int }` because
  nominal records project to their structural row in row-polymorphic positions.

  The original statement (universally quantified over fuel) is FALSE:
  unify at fuel=0 always returns "out of fuel". The corrected statement
  existentially quantifies fuel — there exists sufficient fuel for
  unification to succeed.
-/

import Kea.DataFrame
import Kea.Properties.SubstIdempotent
import Kea.Properties.DecomposeFields
import Kea.Properties.UnifyReflexive

-- =========================================================================
-- Helper: applySubst with empty substitution is identity
-- =========================================================================

/-- Applying the empty substitution to any type is a no-op. -/
private theorem applySubst_empty (fuel : Nat) (ty : Ty) :
    applySubst Subst.empty fuel ty = ty :=
  (applySubst_noop Subst.empty fuel).1 ty
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem applySubstRow_empty (fuel : Nat) (row : Row) :
    applySubstRow Subst.empty fuel row = row :=
  (applySubst_noop Subst.empty fuel).2.1 row
    (fun _ _ => rfl) (fun _ _ => rfl)

-- =========================================================================
-- Core lemma: unifyRows on identical rows with empty subst
-- =========================================================================

/-- unifyRows on a row with itself (empty substitution) succeeds and
    returns the state unchanged. Corollary of the general unifyRows_self_fixed. -/
private theorem unifyRows_self_empty (row : Row)
    (fuel : Nat) (h_fuel : fuel ≥ RowFields.length row.fields + 2) :
    unifyRows UnifyState.empty fuel row row = .ok UnifyState.empty :=
  unifyRows_self_fixed UnifyState.empty row fuel h_fuel
    (by rw [show UnifyState.empty.subst = Subst.empty from rfl]; exact applySubstRow_empty _ row)

-- =========================================================================
-- Main theorem
-- =========================================================================

/-- beqTy on different constructors (record vs anonRecord) is false. -/
private theorem beqTy_record_anonRecord (name : String) (row : Row) :
    beqTy (Ty.record name row) (Ty.anonRecord row) = false := by
  simp [beqTy]

/-- A named record unifies with an anonymous record having the same row. -/
theorem recordStructuralProjection (name : String) (row : Row) :
    ∃ fuel st', unify UnifyState.empty fuel (Ty.record name row) (Ty.anonRecord row) = .ok st' := by
  refine ⟨RowFields.length row.fields + 3, UnifyState.empty, ?_⟩
  -- Step-by-step reduction of unify
  unfold unify
  -- Reduce UnifyState.empty.subst to Subst.empty, then apply identity
  simp only [show UnifyState.empty.subst = Subst.empty from rfl, applySubst_empty]
  -- BEq check: beqTy (.record name row) (.anonRecord row) = false
  have h_neq : (Ty.record name row == Ty.anonRecord row) = false :=
    beqTy_record_anonRecord name row
  -- The if-then-else with Bool false reduces; then match on constructors
  simp only [h_neq]
  -- Match arm (.record _ r1, .anonRecord r2) fires
  exact unifyRows_self_empty row (RowFields.length row.fields + 2) (by omega)

/-- beqTy on different constructors (anonRecord vs record) is false. -/
private theorem beqTy_anonRecord_record (name : String) (row : Row) :
    beqTy (Ty.anonRecord row) (Ty.record name row) = false := by
  simp [beqTy]

/-- Unifier-level symmetry witness:
    an anonymous record also unifies with a named record having the same row.

    This is an inference-internal property, not a language-level assignability
    policy. Directional nominal boundaries must therefore be enforced above
    unification (let/call/return/ascription boundary checks). -/
theorem anonRecordUnifiesWithNamedRecord (name : String) (row : Row) :
    ∃ fuel st', unify UnifyState.empty fuel (Ty.anonRecord row) (Ty.record name row) = .ok st' := by
  refine ⟨RowFields.length row.fields + 3, UnifyState.empty, ?_⟩
  unfold unify
  simp only [show UnifyState.empty.subst = Subst.empty from rfl, applySubst_empty]
  have h_neq : (Ty.anonRecord row == Ty.record name row) = false :=
    beqTy_anonRecord_record name row
  simp only [h_neq]
  exact unifyRows_self_empty row (RowFields.length row.fields + 2) (by omega)

/-- Directional record nominal-boundary gate for implicit assignability checks.
    This models the brief's intended policy layer above unification:
    structural anonymous rows do not implicitly flow into named records. -/
def recordNominalBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .record _ _, .anonRecord _ => false
  | _, _ => true

/-- Named-record to structural projection remains implicitly allowed. -/
theorem record_boundary_allows_named_to_structural (name : String) (row : Row) :
    recordNominalBoundaryAllows (.anonRecord row) (.record name row) = true := by
  rfl

/-- Structural-to-nominal implicit flow is blocked by the boundary policy. -/
theorem record_boundary_rejects_structural_to_named (name : String) (row : Row) :
    recordNominalBoundaryAllows (.record name row) (.anonRecord row) = false := by
  rfl

/-- Boundary policy closure witness: even though the unifier is symmetric for
    record/anonRecord, the directional boundary gate rejects structural-to-
    nominal implicit flow. -/
theorem record_nominal_boundary_closes_unifier_symmetry (name : String) (row : Row) :
    (∃ fuel st', unify UnifyState.empty fuel (Ty.anonRecord row) (Ty.record name row) = .ok st') ∧
      recordNominalBoundaryAllows (.record name row) (.anonRecord row) = false := by
  exact ⟨anonRecordUnifiesWithNamedRecord name row, record_boundary_rejects_structural_to_named name row⟩

/-- Boundary-sensitive type-check sites for implicit assignability. -/
inductive RecordBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level boundary check model.
    Current policy is site-invariant for record nominal boundaries. -/
def recordBoundaryAllowsAtSite
    (_site : RecordBoundarySite) (expected actual : Ty) : Bool :=
  recordNominalBoundaryAllows expected actual

/-- Record nominal-boundary policy is currently site-invariant:
    all boundary-sensitive sites use the same predicate. -/
theorem record_boundary_policy_site_invariant
    (site1 site2 : RecordBoundarySite) (expected actual : Ty) :
    recordBoundaryAllowsAtSite site1 expected actual =
      recordBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Structural-to-nominal implicit flow is rejected uniformly across all
    boundary-sensitive sites (`let`/call/return/ascription). -/
theorem record_boundary_rejects_structural_to_named_all_sites
    (site : RecordBoundarySite) (name : String) (row : Row) :
    recordBoundaryAllowsAtSite site (.record name row) (.anonRecord row) = false := by
  cases site <;> rfl

/-- Named-to-structural projection remains implicitly allowed uniformly across
    all boundary-sensitive sites (`let`/call/return/ascription). -/
theorem record_boundary_allows_named_to_structural_all_sites
    (site : RecordBoundarySite) (name : String) (row : Row) :
    recordBoundaryAllowsAtSite site (.anonRecord row) (.record name row) = true := by
  cases site <;> rfl

/-- Packaged directional boundary-policy slice at any boundary-sensitive site:
    named-to-structural projection is allowed, while structural-to-nominal
    implicit flow is rejected. -/
theorem record_boundary_directional_policy_all_sites
    (site : RecordBoundarySite) (name : String) (row : Row) :
    recordBoundaryAllowsAtSite site (.anonRecord row) (.record name row) = true
    ∧
    recordBoundaryAllowsAtSite site (.record name row) (.anonRecord row) = false := by
  refine ⟨?_, ?_⟩
  · exact record_boundary_allows_named_to_structural_all_sites site name row
  · exact record_boundary_rejects_structural_to_named_all_sites site name row

/-- Site-level closure witness for nominal boundary policy above symmetric
    record/anonRecord unification: both unifier directions succeed, but only
    named-to-structural flow is allowed by boundary policy at the site. -/
theorem record_nominal_boundary_closes_unifier_symmetry_all_sites
    (site : RecordBoundarySite) (name : String) (row : Row) :
    (∃ fuel st', unify UnifyState.empty fuel (Ty.record name row) (Ty.anonRecord row) = .ok st')
    ∧
    (∃ fuel st', unify UnifyState.empty fuel (Ty.anonRecord row) (Ty.record name row) = .ok st')
    ∧
    recordBoundaryAllowsAtSite site (.anonRecord row) (.record name row) = true
    ∧
    recordBoundaryAllowsAtSite site (.record name row) (.anonRecord row) = false := by
  refine ⟨recordStructuralProjection name row, anonRecordUnifiesWithNamedRecord name row, ?_, ?_⟩
  · exact record_boundary_allows_named_to_structural_all_sites site name row
  · exact record_boundary_rejects_structural_to_named_all_sites site name row
