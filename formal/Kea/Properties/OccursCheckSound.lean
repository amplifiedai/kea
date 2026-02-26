/-
  Kea.Properties.OccursCheckSound — Occurs check soundness.

  Maps to Rust proptest:
    - `occurs_check_always_fires` (prop_tests.rs:477)

  Property: If variable v occurs in the resolved form of type t, and t is not
  simply Var(v), then bindTypeVar v t fails.

  Note: The Lean theorem uses `occursIn v (applySubst ...)` — the substituted
  form — because that is what `bindTypeVar` actually checks. The Rust proptest
  uses a fresh unifier (empty substitution) where raw and substituted forms
  coincide. The original statement using `occursIn v ty` (raw) is false for
  non-empty substitutions that eliminate v from ty.
-/

import Kea.Unify

/-- If v occurs in the substituted form of ty and ty ≠ Var(v) (BEq),
    then bindTypeVar produces an error. This is the occurs check:
    binding v to a type containing v would create an infinite type. -/
theorem occursCheckSound (st : UnifyState) (fuel : Nat) (v : TypeVarId) (ty : Ty) :
    (ty == .var v) = false →
    occursIn v (applySubst st.subst fuel ty) = true →
    ∃ e, bindTypeVar st v ty fuel = .err e := by
  intro hneq hoccurs
  simp only [bindTypeVar, hneq, hoccurs, ↓reduceIte]
  exact ⟨_, rfl⟩
