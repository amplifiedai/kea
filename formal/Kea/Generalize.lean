/-
  Kea.Generalize — Generalization and instantiation for let-polymorphism.

  Mirrors: rill-infer/src/typeck.rs:571-664
    - generalize: quantify vars free in type but not in env
    - instantiate: fresh vars + lacks transfer
    - rename_type: variable renaming

  This is the core of let-polymorphism: `let id = |x| x` gets generalized
  to `∀ a. a → a` because `a` is free in the type but not in the environment.
-/

import Kea.Ty
import Kea.Substitution
import Kea.FreeVars
import Kea.LacksConstraints
import Kea.Unify

-- =========================================================================
-- Type environment (simplified for formalization)
-- =========================================================================

/-- A type environment: maps names to type schemes.
    Simplified from the Rust TypeEnv which has a stack of scopes. -/
structure TypeEnv where
  bindings : List (String × TypeScheme)

namespace TypeEnv

/-- Empty environment. -/
def empty : TypeEnv := ⟨[]⟩

/-- Add a binding. -/
def bind (env : TypeEnv) (name : String) (scheme : TypeScheme) : TypeEnv :=
  ⟨(name, scheme) :: env.bindings⟩

/-- Collect free type variables from the environment (after applying subst). -/
def freeTypeVarsEnv (env : TypeEnv) (s : Subst) (fuel : Nat) : List TypeVarId :=
  env.bindings.flatMap fun (_, scheme) =>
    let resolved := applySubst s fuel scheme.ty
    let bodyVars := freeTypeVars resolved
    bodyVars.filter (fun v => !scheme.typeVars.elem v)

/-- Collect free row variables from the environment (after applying subst). -/
def freeRowVarsEnv (env : TypeEnv) (s : Subst) (fuel : Nat) : List RowVarId :=
  env.bindings.flatMap fun (_, scheme) =>
    let resolved := applySubst s fuel scheme.ty
    let bodyVars := freeRowVars resolved
    bodyVars.filter (fun v => !scheme.rowVars.elem v)

end TypeEnv

-- =========================================================================
-- Rename type/row variables
-- =========================================================================

/-- Mapping from old variable IDs to new variable IDs. -/
structure VarMapping where
  typeMap : List (TypeVarId × TypeVarId)
  rowMap  : List (RowVarId × RowVarId)

namespace VarMapping

def lookupType (m : VarMapping) (v : TypeVarId) : Option TypeVarId :=
  match m.typeMap.find? (fun (old, _) => old == v) with
  | some (_, new_v) => some new_v
  | none => none

def lookupRow (m : VarMapping) (v : RowVarId) : Option RowVarId :=
  match m.rowMap.find? (fun (old, _) => old == v) with
  | some (_, new_v) => some new_v
  | none => none

end VarMapping

mutual
  /-- Replace type/row variables according to a mapping.
      Mirrors Rust `rename_type`. -/
  def renameType (ty : Ty) (m : VarMapping) : Ty :=
    match ty with
    | .var v =>
      match m.lookupType v with
      | some new_v => .var new_v
      | none => .var v
    | .int => .int
    | .intN w sgn => .intN w sgn
    | .float => .float
    | .floatN w => .floatN w
    | .decimal p sc => .decimal p sc
    | .bool => .bool
    | .string => .string
    | .html => .html
    | .markdown => .markdown
    | .atom => .atom
    | .date => .date
    | .dateTime => .dateTime
    | .unit => .unit
    | .list inner => .list (renameType inner m)
    | .map k v => .map (renameType k m) (renameType v m)
    | .set inner => .set (renameType inner m)
    | .option inner => .option (renameType inner m)
    | .result ok err => .result (renameType ok m) (renameType err m)
    | .existential bounds assoc => .existential bounds (renameTyList assoc m)
    | .fixedSizeList inner d => .fixedSizeList (renameType inner m) d
    | .tensor inner shape => .tensor (renameType inner m) shape
    | .sum name args => .sum name (renameTyList args m)
    | .opaque name params => .opaque name (renameTyList params m)
    | .record name r => .record name (renameRow r m)
    | .anonRecord r => .anonRecord (renameRow r m)
    | .dataframe inner => .dataframe (renameType inner m)
    | .dynamic => .dynamic
    | .groupedFrame inner keys => .groupedFrame (renameType inner m) keys
    | .tagged inner tags => .tagged (renameType inner m) tags
    | .column inner => .column (renameType inner m)
    | .stream inner => .stream (renameType inner m)
    | .task inner => .task (renameType inner m)
    | .actor inner => .actor (renameType inner m)
    | .arc inner => .arc (renameType inner m)
    | .function params ret => .function (renameTyList params m) (renameType ret m)
    | .forall vars body => .forall vars (renameType body m)
    | .app ctor args => .app (renameType ctor m) (renameTyList args m)
    | .constructor name fixedArgs arity => .constructor name (renameTyList fixedArgs m) arity
    | .row r => .row (renameRow r m)
    | .tuple elems => .tuple (renameTyList elems m)

  /-- Rename row variables in a row. -/
  def renameRow (r : Row) (m : VarMapping) : Row :=
    match r with
    | .mk fields rest =>
      let fields' := renameRowFields fields m
      let rest' := match rest with
        | none => none
        | some rv =>
          match m.lookupRow rv with
          | some new_rv => some new_rv
          | none => some rv
      .mk fields' rest'

  /-- Rename variables in a type list. -/
  def renameTyList (tl : TyList) (m : VarMapping) : TyList :=
    match tl with
    | .nil => .nil
    | .cons t rest => .cons (renameType t m) (renameTyList rest m)

  /-- Rename variables in row fields. -/
  def renameRowFields (rf : RowFields) (m : VarMapping) : RowFields :=
    match rf with
    | .nil => .nil
    | .cons l ty rest => .cons l (renameType ty m) (renameRowFields rest m)
end

-- =========================================================================
-- Generalize
-- =========================================================================

/-- Generalize a type into a type scheme by quantifying over variables
    that are free in the type but not in the environment.

    Mirrors Rust `generalize` in typeck.rs:456-490.
    Now also preserves trait bounds for quantified type vars. -/
def generalize (ty : Ty) (env : TypeEnv) (s : Subst) (lc : Lacks)
    (traitBounds : TraitBounds) (fuel : Nat)
    : TypeScheme :=
  let resolvedTy := applySubst s fuel ty
  let envTypeVars := TypeEnv.freeTypeVarsEnv env s fuel
  let envRowVars := TypeEnv.freeRowVarsEnv env s fuel
  let tyTypeVars := freeTypeVars resolvedTy
  let tyRowVars := freeRowVars resolvedTy
  -- Variables free in type but not in environment
  let genTypeVars := tyTypeVars.filter (fun v => !envTypeVars.elem v) |>.eraseDups
  let genRowVars := tyRowVars.filter (fun v => !envRowVars.elem v) |>.eraseDups
  -- Preserve lacks constraints for quantified row vars
  let schemeLacks := genRowVars.filterMap fun rv =>
    let labels := Lacks.getLabels lc rv
    if labels.isEmpty then none else some (rv, labels)
  -- Preserve trait bounds for quantified type vars
  let schemeBounds := genTypeVars.filterMap fun tv =>
    let traits := traitBounds.filter (fun (v, _) => v == tv) |>.map (fun (_, t) => t)
    if traits.isEmpty then none else some (tv, traits)
  { typeVars := genTypeVars, rowVars := genRowVars,
    lacks := schemeLacks, bounds := schemeBounds, ty := resolvedTy }

-- =========================================================================
-- Instantiate
-- =========================================================================

/-- Instantiate a type scheme with fresh variables.
    Returns the instantiated type and updated unification state.

    Transfers both lacks constraints and trait bounds to fresh variables.
    Mirrors Rust `instantiate` in typeck.rs:522-549. -/
def instantiate (scheme : TypeScheme) (st : UnifyState) : Ty × UnifyState :=
  if scheme.isMono then (scheme.ty, st)
  else
    -- Create fresh type variables
    let (typeMapping, st') := scheme.typeVars.foldl
      (fun (acc, st) tv =>
        let (fresh, st') := st.freshTypeVar
        ((tv, fresh) :: acc, st'))
      ([], st)
    -- Create fresh row variables
    let (rowMapping, st'') := scheme.rowVars.foldl
      (fun (acc, st) rv =>
        let (fresh, st') := st.freshRowVar
        ((rv, fresh) :: acc, st'))
      ([], st')
    -- Transfer lacks constraints to fresh row variables
    let lacks' := scheme.lacks.foldl
      (fun acc (oldRv, labels) =>
        match rowMapping.find? (fun (old, _) => old == oldRv) with
        | some (_, newRv) =>
          labels.foldl (fun acc' l => Lacks.addLacks acc' newRv l) acc
        | none => acc)
      st''.lacks
    -- Transfer trait bounds to fresh type variables
    let traitBounds' := scheme.bounds.foldl
      (fun acc (oldTv, traits) =>
        match typeMapping.find? (fun (old, _) => old == oldTv) with
        | some (_, newTv) =>
          traits.foldl (fun acc' t => (newTv, t) :: acc') acc
        | none => acc)
      st''.traitBounds
    -- Apply the mapping
    let mapping : VarMapping := { typeMap := typeMapping, rowMap := rowMapping }
    let renamedTy := renameType scheme.ty mapping
    (renamedTy, { st'' with lacks := lacks', traitBounds := traitBounds' })
