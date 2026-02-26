/-
  Kea.Properties.LacksBlocksDuplicate — Lacks constraints prevent duplicates.

  Maps to Rust proptest:
    - `lacks_constraint_blocks_duplicate` (prop_tests.rs:482)

  Property: If a row variable has a lacks constraint for label L,
  unifying it with a row containing L produces an error.

  Precondition: rv must be unbound in the substitution. The Rust proptest
  creates a fresh unifier (no existing bindings), making this implicit.
  Without this, rv could resolve to a row already containing l, and
  unification would compare two closed rows — potentially succeeding.
-/

import Kea.Unify

-- =========================================================================
-- Helper lemmas
-- =========================================================================

/-- applySubstRowFields on nil always returns nil. -/
private theorem applySubstRowFields_nil (s : Subst) (fuel : Nat) :
    applySubstRowFields s fuel .nil = .nil := by
  cases fuel <;> rfl

/-- applySubstRow preserves empty open row when rv is unbound. -/
private theorem applySubstRow_emptyOpen_unbound (s : Subst) (fuel : Nat)
    (rv : RowVarId) (h : s.rowMap rv = none) :
    applySubstRow s fuel (.mk .nil (some rv)) = .mk .nil (some rv) := by
  cases fuel with
  | zero => rfl
  | succ n => simp [applySubstRow, applySubstRowFields_nil, h]

/-- applySubstRowFields preserves single-field structure (same label). -/
private theorem applySubstRowFields_cons_nil (s : Subst) (fuel : Nat) (l : Label) (ty : Ty) :
    ∃ ty', applySubstRowFields s fuel (.cons l ty .nil) = .cons l ty' .nil := by
  cases fuel with
  | zero => exact ⟨ty, rfl⟩
  | succ n => exact ⟨applySubst s n ty, by simp [applySubstRowFields, applySubstRowFields_nil]⟩

-- =========================================================================
-- Main theorem
-- =========================================================================

/-- If rv lacks label l, unifying an empty open row with rv against
    a closed row containing l produces an error.

    Precondition: rv is unbound in the substitution (the Rust proptest
    uses a fresh unifier, making this implicit). -/
theorem lacksBlocksDuplicate (st : UnifyState) (fuel : Nat)
    (rv : RowVarId) (l : Label) (ty : Ty)
    (h_unbound : st.subst.rowMap rv = none) :
    Lacks.lacksLabel st.lacks rv l = true →
    ∃ e, unifyRows st (fuel + 1) (Row.emptyOpen rv)
           (Row.closed (.cons l ty .nil)) = .err e := by
  intro h_lacks
  simp only [Row.emptyOpen, Row.closed]
  cases fuel with
  | zero =>
    -- Inner fuel = 0: unifyCommonFields returns "out of fuel"
    simp [unifyRows, applySubstRow, decomposeFields, unifyCommonFields]
  | succ n =>
    -- Inner fuel > 0: full path through to lacksViolation
    obtain ⟨ty', hty'⟩ := applySubstRowFields_cons_nil st.subst n l ty
    refine ⟨"lacks constraint violation", ?_⟩
    -- Step 1: Unfold unifyRows, rewrite r1' using h_unbound
    simp only [unifyRows]
    have h_open :
        applySubstRowCompat st.subst (n + 1) (.mk .nil (some rv)) = .mk .nil (some rv) := by
      simpa [applySubstRowCompat] using applySubstRow_emptyOpen_unbound st.subst (n + 1) rv h_unbound
    rw [h_open]
    -- Step 2: Reduce applySubstRow on r2, simplify struct accessors
    simp only [applySubstRowCompat, applySubstRow, hty', Row.fields, Row.rest]
    -- Step 3: Reduce decomposeFields → decomposeFieldsGo → result,
    -- then unifyCommonFields, lacksViolation
    simp [decomposeFields, decomposeFieldsGo, unifyCommonFields,
          RowFields.length, lacksViolation, h_lacks]
