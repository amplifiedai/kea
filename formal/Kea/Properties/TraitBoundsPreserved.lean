/-
  Property: Trait bounds survive generalize → instantiate round-trip.

  Corresponds to Rust proptest `trait_bounds_survive_generalize_instantiate`
  in rill-infer/src/prop_tests.rs:818.

  MCP validation (2026-02-10): Confirmed via MCP that:
  - `fn total(x) where x: Summable { x }` generalizes to `(a) -> a` with hidden bounds
  - `total(42)` succeeds (Int implements Summable)
  - `total("hello")` errors ("String does not implement trait Summable")
  - Bounds survive through `let alias = process` (double generalize/instantiate)
  - Multiple bounds checked independently with separate diagnostics
-/

import Kea.Generalize
import Kea.DataFrame
import Kea.Properties.SubstIdempotent

-- Helper: empty substitution is identity on types.
private theorem applySubst_empty (fuel : Nat) (ty : Ty) :
    applySubst Subst.empty fuel ty = ty :=
  (applySubst_noop Subst.empty fuel).1 ty (fun _ _ => rfl) (fun _ _ => rfl)

/-- Trait bounds on quantified type vars survive generalize → instantiate.

    Corresponds to: `trait_bounds_survive_generalize_instantiate` (:818) -/
theorem traitBoundsSurviveInstantiate
    (tv : TypeVarId) (traitName : String)
    (fuel : Nat) (hfuel : fuel ≥ 1)
    : let ty := Ty.function (.cons (.var tv) .nil) (.var tv)
      let env := TypeEnv.empty
      let s := Subst.empty
      let lc := Lacks.empty
      let tb : TraitBounds := [(tv, traitName)]
      let scheme := generalize ty env s lc tb fuel
      let (_, st') := instantiate scheme UnifyState.empty
      st'.traitBounds.length > 0
    := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  -- Restate without let bindings
  show (instantiate
    (generalize (Ty.function (.cons (.var tv) .nil) (.var tv))
      TypeEnv.empty Subst.empty Lacks.empty [(tv, traitName)] (n + 1))
    UnifyState.empty).2.traitBounds.length > 0
  -- Reduce generalize: unfold + full simp to handle list operations with symbolic tv
  unfold generalize
  simp [applySubst_empty, TypeEnv.empty, TypeEnv.freeTypeVarsEnv, TypeEnv.freeRowVarsEnv,
        freeTypeVars, freeTypeVarsTyList, freeRowVars, freeRowVarsTyList,
        Lacks.empty, Lacks.getLabels,
        List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop,
        List.any, List.reverse, List.reverseAux]
  -- Reduce instantiate
  unfold instantiate
  simp [TypeScheme.isMono, UnifyState.empty, UnifyState.freshTypeVar,
        UnifyState.freshRowVar, renameType, renameTyList,
        VarMapping.lookupType, Lacks.empty]
