/-
  Kea.LacksConstraints — Lacks constraint model.

  Mirrors: rill-types/src/lib.rs:614-658 (LacksConstraints)

  Tracks which labels each row variable must lack.
  When a row is extended with label `l`, the row variable must lack `l`.
  This prevents duplicate labels (KERNEL §2.2).
-/

import Kea.Ty

/-- Lacks constraints: maps row variables to sets of labels they must lack. -/
structure Lacks where
  /-- Association list of (row var, labels it must lack). -/
  constraints : List (RowVarId × List Label)
  deriving Repr

namespace Lacks

/-- Empty lacks constraints. -/
def empty : Lacks := ⟨[]⟩

/-- Get all labels that a row variable must lack. -/
def getLabels (l : Lacks) (rv : RowVarId) : List Label :=
  match l.constraints.find? (fun (v, _) => v == rv) with
  | some (_, labels) => labels
  | none => []

/-- Check whether row variable `rv` is known to lack `label`. -/
def lacksLabel (l : Lacks) (rv : RowVarId) : Label → Bool :=
  fun label => (l.getLabels rv).elem label

/-- Add a lacks constraint: `rv` must lack `label`. -/
def addLacks (l : Lacks) (rv : RowVarId) (label : Label) : Lacks :=
  let existing := l.getLabels rv
  if existing.elem label then l  -- already present
  else
    let constraints' := l.constraints.filter (fun (v, _) => v != rv)
    ⟨(rv, label :: existing) :: constraints'⟩

/-- Check whether extending `rv` with `label` would violate constraints.
    Returns `true` if the extension is allowed. -/
def canExtend (l : Lacks) (rv : RowVarId) (label : Label) : Bool :=
  !(l.lacksLabel rv label)

/-- Transfer all lacks constraints from `fromVar` to `toVar`.
    Used when unification binds one row variable to another. -/
def transfer (l : Lacks) (fromVar toVar : RowVarId) : Lacks :=
  let fromLabels := l.getLabels fromVar
  let toLabels := l.getLabels toVar
  let merged := fromLabels ++ toLabels |>.eraseDups
  let constraints' := l.constraints.filter (fun (v, _) => v != fromVar && v != toVar)
  if merged.isEmpty then ⟨constraints'⟩
  else ⟨(toVar, merged) :: constraints'⟩

end Lacks
