/-
  Kea.Properties.TemporalLeafParity — Temporal leaf constructor parity.

  Maps to Rust proptests:
    - `date_is_substitution_leaf`
    - `datetime_is_substitution_leaf`
    - `date_unifies_with_self`
    - `datetime_unifies_with_self`
    - `date_does_not_unify_with_datetime`
    - `temporal_row_unification`

  These theorems certify Date/DateTime as true substitution/unification leaves.
-/

import Kea.Properties.UnifyReflexive

/-- Date is a substitution leaf. -/
theorem date_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel .date = .date := by
  cases fuel <;> simp [applySubst]

/-- DateTime is a substitution leaf. -/
theorem datetime_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel .dateTime = .dateTime := by
  cases fuel <;> simp [applySubst]

/-- Date inside Option remains stable under substitution. -/
theorem option_date_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel (.option .date) = .option .date := by
  cases fuel with
  | zero => rfl
  | succ n =>
    simp [applySubst, date_is_substitution_leaf s n]

/-- DateTime inside List remains stable under substitution. -/
theorem list_datetime_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel (.list .dateTime) = .list .dateTime := by
  cases fuel with
  | zero => rfl
  | succ n =>
    simp [applySubst, datetime_is_substitution_leaf s n]

/-- Date unifies with itself. -/
theorem date_unifies_with_self (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .date .date = .ok st := by
  simpa using (unifyReflexive' st fuel .date)

/-- DateTime unifies with itself. -/
theorem datetime_unifies_with_self (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .dateTime .dateTime = .ok st := by
  simpa using (unifyReflexive' st fuel .dateTime)

/-- Date and DateTime are distinct and do not unify. -/
theorem date_does_not_unify_with_datetime (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .date .dateTime = .err "type mismatch" := by
  have hneq : (Ty.date == Ty.dateTime) = false := by
    show beqTy Ty.date Ty.dateTime = false
    simp [beqTy]
  unfold unify
  simp [applySubstCompat, date_is_substitution_leaf, datetime_is_substitution_leaf, hneq]

/-- Html is a substitution leaf. -/
theorem html_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel .html = .html := by
  cases fuel <;> simp [applySubst]

/-- Markdown is a substitution leaf. -/
theorem markdown_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel .markdown = .markdown := by
  cases fuel <;> simp [applySubst]

/-- Atom is a substitution leaf. -/
theorem atom_is_substitution_leaf (s : Subst) (fuel : Nat) :
    applySubst s fuel .atom = .atom := by
  cases fuel <;> simp [applySubst]

/-- Html unifies with itself. -/
theorem html_unifies_with_self (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .html .html = .ok st := by
  simpa using (unifyReflexive' st fuel .html)

/-- Markdown unifies with itself. -/
theorem markdown_unifies_with_self (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .markdown .markdown = .ok st := by
  simpa using (unifyReflexive' st fuel .markdown)

/-- Atom unifies with itself. -/
theorem atom_unifies_with_self (st : UnifyState) (fuel : Nat) :
    unify st (fuel + 1) .atom .atom = .ok st := by
  simpa using (unifyReflexive' st fuel .atom)

/-- Html and Markdown are distinct and do not unify. -/
theorem html_does_not_unify_with_markdown (st : UnifyState) :
    unify st 1 .html .markdown = .err "type mismatch" := by
  have hneq : (Ty.html == Ty.markdown) = false := by
    show beqTy Ty.html Ty.markdown = false
    simp [beqTy]
  unfold unify
  simp [applySubstCompat, applySubst, hneq]

/-- Atom and Html are distinct and do not unify. -/
theorem atom_does_not_unify_with_html (st : UnifyState) :
    unify st 1 .atom .html = .err "type mismatch" := by
  have hneq : (Ty.atom == Ty.html) = false := by
    show beqTy Ty.atom Ty.html = false
    simp [beqTy]
  unfold unify
  simp [applySubstCompat, applySubst, hneq]

/-- Html and String are distinct and do not unify. -/
theorem html_does_not_unify_with_string (st : UnifyState) :
    unify st 1 .html .string = .err "type mismatch" := by
  have hneq : (Ty.html == Ty.string) = false := by
    show beqTy Ty.html Ty.string = false
    simp [beqTy]
  unfold unify
  simp [applySubstCompat, applySubst, hneq]

/-- Boundary-sensitive sites where low-risk leaf constructor checks are enforced. -/
inductive LeafBoundarySite : Type where
  | letAnnotation
  | callArgument
  | returnAnnotation
  | ascription

/-- Site-level low-risk leaf boundary policy (`Html`/`Markdown`/`Atom`/`Date`/`DateTime`).
    Current scope:
    - expected low-risk leaf constructors require exact constructor match
    - otherwise allowed (outside this boundary surface) -/
def leafBoundaryAllows (expected actual : Ty) : Bool :=
  match expected, actual with
  | .html, .html => true
  | .html, _ => false
  | .markdown, .markdown => true
  | .markdown, _ => false
  | .atom, .atom => true
  | .atom, _ => false
  | .date, .date => true
  | .date, _ => false
  | .dateTime, .dateTime => true
  | .dateTime, _ => false
  | _, _ => true

/-- Site-level wrapper for low-risk leaf boundary checks. -/
def leafBoundaryAllowsAtSite
    (_site : LeafBoundarySite) (expected actual : Ty) : Bool :=
  leafBoundaryAllows expected actual

/-- Low-risk leaf boundary policy is currently site-invariant. -/
theorem leaf_boundary_policy_site_invariant
    (site1 site2 : LeafBoundarySite) (expected actual : Ty) :
    leafBoundaryAllowsAtSite site1 expected actual =
      leafBoundaryAllowsAtSite site2 expected actual := by
  cases site1 <;> cases site2 <;> rfl

/-- Html/Markdown mismatch is rejected by boundary policy. -/
theorem leaf_boundary_rejects_html_markdown_mismatch :
    leafBoundaryAllows .html .markdown = false := by
  native_decide

/-- Atom/Html mismatch is rejected by boundary policy. -/
theorem leaf_boundary_rejects_atom_html_mismatch :
    leafBoundaryAllows .atom .html = false := by
  native_decide

/-- Date/DateTime mismatch is rejected by boundary policy. -/
theorem leaf_boundary_rejects_date_datetime_mismatch :
    leafBoundaryAllows .date .dateTime = false := by
  native_decide

/-- Non-leaf actuals are rejected when a low-risk leaf constructor is expected. -/
theorem leaf_boundary_rejects_non_leaf_actual :
    leafBoundaryAllows .html .string = false := by
  native_decide

/-- Packaged low-risk leaf boundary surface slice:
    site invariance + constructor mismatch/non-leaf rejection, with closure to
    concrete mismatch/reflexive unifier witnesses. -/
theorem leaf_boundary_surface_slice
    (st : UnifyState) (site : LeafBoundarySite) :
    (leafBoundaryAllowsAtSite site .html .markdown = false)
    ∧
    (leafBoundaryAllowsAtSite site .atom .html = false)
    ∧
    (leafBoundaryAllowsAtSite site .date .dateTime = false)
    ∧
    (leafBoundaryAllowsAtSite site .html .string = false)
    ∧
    (unify st 1 .html .markdown = .err "type mismatch")
    ∧
    (unify st 1 .atom .html = .err "type mismatch")
    ∧
    (unify st 1 .date .dateTime = .err "type mismatch")
    ∧
    (unify st 1 .html .string = .err "type mismatch")
    ∧
    (unify st 1 .html .html = .ok st)
    ∧
    (unify st 1 .atom .atom = .ok st)
    ∧
    (unify st 1 .date .date = .ok st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases site <;> exact leaf_boundary_rejects_html_markdown_mismatch
  · cases site <;> exact leaf_boundary_rejects_atom_html_mismatch
  · cases site <;> exact leaf_boundary_rejects_date_datetime_mismatch
  · cases site <;> exact leaf_boundary_rejects_non_leaf_actual
  · exact html_does_not_unify_with_markdown st
  · exact atom_does_not_unify_with_html st
  · exact date_does_not_unify_with_datetime st 0
  · exact html_does_not_unify_with_string st
  · exact html_unifies_with_self st 0
  · exact atom_unifies_with_self st 0
  · exact date_unifies_with_self st 0

/-- Temporal rows with matching Date/DateTime fields unify with themselves. -/
theorem temporal_row_unification (st : UnifyState) (fuel : Nat) (dateLabel dtLabel : Label) :
    let r := Row.closed (.cons dateLabel .date (.cons dtLabel .dateTime .nil))
    unify st (fuel + 1) (.row r) (.row r) = .ok st := by
  intro r
  simpa using (unifyReflexive' st fuel (.row r))

/-- Date has no free type or row variables. -/
theorem date_has_no_free_vars :
    freeTypeVars .date = [] ∧ freeRowVars .date = [] := by
  simp [freeTypeVars, freeRowVars]

/-- DateTime has no free type or row variables. -/
theorem datetime_has_no_free_vars :
    freeTypeVars .dateTime = [] ∧ freeRowVars .dateTime = [] := by
  simp [freeTypeVars, freeRowVars]
