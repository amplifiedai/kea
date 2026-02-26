/-
  Kea.Properties.RowFieldsSorted — Row field ordering preservation.

  Maps to Rust proptests:
    - `row_fields_sorted_closed` (prop_tests.rs:265)
    - `row_fields_sorted_open` (prop_tests.rs:277)
    - `apply_row_preserves_sort` (prop_tests.rs:290)

  Property: Row operations preserve the sorted invariant on field labels.

  The general row-level theorem `applyRowPreservesSort` is FALSE for bound
  row variables (see counterexample below). The field-level theorem
  `applySubstRowFields_preserves_sorted` IS true — substitution changes
  types but not labels. The Rust proptest succeeds because it only tests
  substitutions produced by Rémy unification, which maintain an additional
  invariant (resolved row fields are disjoint from and greater than the
  original fields).
-/

import Kea.Substitution

-- =========================================================================
-- Helper lemmas for applySubstRowFields structural properties
-- =========================================================================

-- applySubstRowFields on nil is nil for any fuel.
private theorem applySubstRowFields_nil (s : Subst) (fuel : Nat) :
    applySubstRowFields s fuel .nil = .nil := by
  match fuel with
  | 0 => rfl
  | _ + 1 => unfold applySubstRowFields; rfl

-- applySubstRowFields on cons preserves the head label (for any fuel).
-- This is the key structural lemma: substitution changes types but not labels.
private theorem applySubstRowFields_head (s : Subst) (fuel : Nat)
    (l : Label) (ty : Ty) (rest : RowFields) :
    ∃ ty' rest', applySubstRowFields s fuel (.cons l ty rest) = .cons l ty' rest' := by
  match fuel with
  | 0 => exact ⟨ty, rest, rfl⟩
  | fuel + 1 =>
    exact ⟨applySubst s fuel ty, applySubstRowFields s fuel rest,
      by simp only [applySubstRowFields]⟩

-- =========================================================================
-- Main theorem: substitution preserves sorted order (field level)
-- =========================================================================

/-- Applying type substitution to sorted fields preserves sort order.
    Labels are unchanged by applySubstRowFields — only types change.

    Proof strategy: for the cons-cons case, use applySubstRowFields_head to
    expose the head label of the inner substituted term, making Sorted
    reducible on the result. -/
theorem applySubstRowFields_preserves_sorted (s : Subst) (fuel : Nat) (rf : RowFields) :
    RowFields.Sorted rf → RowFields.Sorted (applySubstRowFields s fuel rf) := by
  match fuel with
  | 0 => exact id  -- fuel 0 is identity
  | fuel + 1 =>
    match rf with
    | .nil => intro _; simp only [applySubstRowFields]; trivial
    | .cons l ty .nil =>
      intro _
      simp only [applySubstRowFields]
      rw [applySubstRowFields_nil]
      simp only [RowFields.Sorted]
    | .cons l₁ _ (.cons l₂ ty₂ tl) =>
      intro h
      simp only [RowFields.Sorted] at h
      obtain ⟨hlt, hrest⟩ := h
      simp only [applySubstRowFields]
      -- Goal: Sorted (.cons l₁ _ (applySubstRowFields s fuel (.cons l₂ ty₂ tl)))
      -- Expose the head label of the inner term so Sorted can reduce
      obtain ⟨ty₂', rest', h_eq⟩ := applySubstRowFields_head s fuel l₂ ty₂ tl
      rw [h_eq]
      -- Goal: Sorted (.cons l₁ _ (.cons l₂ ty₂' rest'))
      simp only [RowFields.Sorted]
      exact ⟨hlt, by rw [← h_eq]; exact applySubstRowFields_preserves_sorted s fuel (.cons l₂ ty₂ tl) hrest⟩

-- =========================================================================
-- Row-level sort preservation: provable cases
-- =========================================================================

/-- Applying a substitution to a closed row preserves field sort order. -/
theorem applyRowPreservesSort_closed (s : Subst) (fuel : Nat) (fields : RowFields) :
    RowFields.Sorted fields →
    RowFields.Sorted (applySubstRow s fuel (Row.mk fields none)).fields := by
  match fuel with
  | 0 => exact id
  | fuel + 1 =>
    intro h
    simp only [applySubstRow]
    exact applySubstRowFields_preserves_sorted s fuel fields h

/-- Applying a substitution to an open row with unbound variable preserves sort order. -/
theorem applyRowPreservesSort_unbound (s : Subst) (fuel : Nat) (fields : RowFields)
    (var : RowVarId) (h_unbound : s.rowMap var = none) :
    RowFields.Sorted fields →
    RowFields.Sorted (applySubstRow s (fuel + 1) (Row.mk fields (some var))).fields := by
  intro h
  simp only [applySubstRow, h_unbound]
  exact applySubstRowFields_preserves_sorted s fuel fields h

-- =========================================================================
-- Counterexample: general applyRowPreservesSort is FALSE
-- =========================================================================

-- A substitution that maps row var 0 to closed row #{ a: String }.
-- Used by the counterexample below.
private def counterexSubst : Subst where
  typeMap := fun _ => none
  rowMap := fun w => if w == 0 then some (Row.closed (.cons "a" .string .nil)) else none

-- Key computation: the substitution produces unsorted fields.
private theorem counterex_computation :
    (applySubstRow counterexSubst 2 (Row.mk (.cons "b" .int .nil) (some 0))).fields =
    .cons "b" .int (.cons "a" .string .nil) := by
  rfl

/-- The general `applyRowPreservesSort` (for all substitutions) is FALSE.

    Counterexample: row = #{ b: Int | rv₀ }, substitution binds rv₀ → #{ a: String }.
    Input fields ["b"] are sorted. After substitution, fields become ["b", "a"] — NOT
    sorted because "b" > "a".

    The Rust proptest `apply_row_preserves_sort` passes because it only tests with
    substitutions produced by Rémy unification, which maintains the invariant that
    resolved row variable fields have labels strictly greater than the original fields
    (since Rémy decomposition partitions by label ordering). -/
theorem applyRowPreservesSort_counterexample :
    ∃ (s : Subst) (r : Row),
      RowFields.Sorted r.fields ∧
      ¬ RowFields.Sorted (applySubstRow s 2 r).fields := by
  refine ⟨counterexSubst, Row.mk (.cons "b" .int .nil) (some 0), by unfold RowFields.Sorted; trivial, ?_⟩
  rw [counterex_computation]
  simp only [RowFields.Sorted]
  intro ⟨h, _⟩
  exact absurd h (by decide)
