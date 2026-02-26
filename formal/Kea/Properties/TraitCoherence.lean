/-
  Property: Trait coherence always rejects duplicate impls.

  Corresponds to: prop_tests.rs `trait_coherence_always_rejects_duplicate` (:699)

  Registering the same (trait, type) pair twice always errors — this is
  the coherence property that prevents ambiguous method dispatch.
-/

import Kea.DataFrame

/-- Registering the same (trait, type) pair twice always fails. -/
theorem traitCoherenceRejectsDuplicate (traitName typeName : String) :
    let reg := TraitRegistry.empty
    match reg.registerImpl traitName typeName with
    | some reg' => reg'.registerImpl traitName typeName = none
    | none => False := by
  simp [TraitRegistry.empty, TraitRegistry.registerImpl, TraitRegistry.hasImpl, List.any]
