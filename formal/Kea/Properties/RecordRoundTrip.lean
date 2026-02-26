/-
  Property: RecordRegistry round-trip.

  Corresponds to: prop_tests.rs `record_registry_round_trip` (:650)

  If we register a record with name N and row R, then `toType N` returns
  `Ty.record N R` — the row fields match the definition (same names, count).
-/

import Kea.DataFrame

/-- Registering then looking up a record always yields `record N R`. -/
theorem recordRegistryRoundTrip (name : String) (row : Row) :
    let reg := RecordRegistry.empty.register name row
    reg.toType name = some (Ty.record name row) := by
  simp [RecordRegistry.register, RecordRegistry.toType, RecordRegistry.lookup,
        RecordRegistry.empty]
