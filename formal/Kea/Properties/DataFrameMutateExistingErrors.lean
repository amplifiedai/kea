/-
  Property: DataFrame mutate on existing column always errors.

  Corresponds to: prop_tests.rs `dataframe_mutate_existing_column_always_errors` (:763)

  If a DataFrame already has column `:c`, then `mutate(df, :c, T)` must
  produce an error — you must use `update` instead. This prevents
  accidental duplicate columns.
-/

import Kea.DataFrame

-- =========================================================================
-- Key lemma: substitution preserves field labels
-- =========================================================================

/-- applySubstRowFields preserves the first label, so `has` still finds it.
    This is the core insight: substitution transforms types within fields
    but never changes labels. -/
theorem applySubstRowFields_has_first (s : Subst) (fuel : Nat)
    (column : Label) (ty : Ty) (rest : RowFields) :
    (applySubstRowFields s fuel (.cons column ty rest)).has column = true := by
  match fuel with
  | 0 => simp [applySubstRowFields, RowFields.has]
  | _ + 1 => simp [applySubstRowFields, RowFields.has]

-- =========================================================================
-- Bridge lemma: resolvedHasColumn always fires for our input shape
-- =========================================================================

/-- For any substitution and fuel, checking a DataFrame with column at the head
    of its row fields always returns true via resolvedHasColumn. -/
theorem resolvedHasColumn_true (s : Subst) (fuel : Nat)
    (column : Label) (existingTy : Ty) (otherFields : RowFields) :
    resolvedHasColumn s fuel
      (Ty.dataframe (Ty.anonRecord (Row.mk (.cons column existingTy otherFields) none)))
      column = true := by
  match fuel with
  | 0 =>
    simp [resolvedHasColumn, applySubst, RowFields.has]
  | 1 =>
    simp [resolvedHasColumn, applySubst, RowFields.has]
  | 2 =>
    simp [resolvedHasColumn, applySubst, applySubstRow, RowFields.has]
  | fuel + 3 =>
    simp only [resolvedHasColumn, applySubst, applySubstRow]
    exact applySubstRowFields_has_first s fuel column existingTy otherFields

-- =========================================================================
-- Main theorem
-- =========================================================================

/-- Mutating with a column that already exists always errors. -/
theorem dataframeMutateExistingErrors
    (column : Label) (existingTy valueTy : Ty) (otherFields : RowFields)
    (fuel : Nat) (st : UnifyState)
    : let inputRow := Row.closed (.cons column existingTy otherFields)
      let inputTy := Ty.dataframe (Ty.anonRecord inputRow)
      match dfMutate st fuel inputTy column valueTy with
      | (.err _, _) => True
      | (.ok _, _) => False
    := by
  simp only [Row.closed]
  dsimp only [dfMutate, UnifyState.freshRowVar, Row.emptyOpen]
  -- Generalize the unify call to get an explicit variable
  generalize unify _ fuel _ _ = ur
  -- Case split on unify result
  cases ur with
  | err e => trivial
  | ok st'' =>
    -- Reduce the redundant `match UnifyResult.ok st'' with ...`
    dsimp only []
    -- Now resolvedHasColumn is a named function call — simp can match it
    simp only [resolvedHasColumn_true, ite_true]
