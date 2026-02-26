/-
  Kea.Ty — Core type definitions for the Kea type system formalization.

  Mirrors: rill-types/src/lib.rs (Type enum, RowType, TypeVarId, RowVarId, Label)

  Design decisions:
  - TypeVarId and RowVarId are Nat (not opaque wrappers) for proof convenience
  - Label is String (matches Rust's Label(String))
  - Ty and Row are mutual inductives
  - Only types that participate in unification are included
  - Phase 2 additions: Record (nominal) and DataFrame (schema-parameterized)
  - Extended constructors (runtime wrappers, nominal forms, constructor-app forms)
    are included as the formal surface expands; language-level metatheory for
    some of these remains milestone-scoped in FORMAL.md.
  - Column(T) wraps ColumnExpr types; participates in unification
-/

-- Abbreviations must be outside namespace for mutual block to reference them.
abbrev TypeVarId := Nat
abbrev RowVarId := Nat
abbrev DimVarId := Nat
abbrev EffectVarId := Nat
abbrev Label := String

/-- Kind of a type variable. -/
inductive Kind : Type where
  | star
  | eff
  deriving DecidableEq, BEq

/-- Dimension expressions used by precision/shape constructors. -/
inductive Dim : Type where
  | const : Nat → Dim
  | var : DimVarId → Dim
  deriving DecidableEq

instance : BEq Dim where
  beq
    | .const a, .const b => a == b
    | .var a, .var b => a == b
    | _, _ => false

/-- Bit-width for precision integer types. -/
inductive IntWidth : Type where
  | i8
  | i16
  | i32
  | i64
  deriving DecidableEq

/-- Signedness marker for precision integer types. -/
inductive Signedness : Type where
  | signed
  | unsigned
  deriving DecidableEq

/-- Bit-width for precision floating-point types. -/
inductive FloatWidth : Type where
  | f16
  | f32
  | f64
  deriving DecidableEq

instance : BEq IntWidth where
  beq
    | .i8, .i8 => true
    | .i16, .i16 => true
    | .i32, .i32 => true
    | .i64, .i64 => true
    | _, _ => false

instance : BEq Signedness where
  beq
    | .signed, .signed => true
    | .unsigned, .unsigned => true
    | _, _ => false

instance : BEq FloatWidth where
  beq
    | .f16, .f16 => true
    | .f32, .f32 => true
    | .f64, .f64 => true
    | _, _ => false

mutual
  inductive Ty : Type where
    -- Primitives (lib.rs:49-54)
    | int    : Ty
    | intN   : IntWidth → Signedness → Ty
    | float  : Ty
    | floatN : FloatWidth → Ty
    | decimal : Dim → Dim → Ty
    | bool   : Ty
    | string : Ty
    | html   : Ty
    | markdown : Ty
    | atom   : Ty
    | date   : Ty
    | dateTime : Ty
    | unit   : Ty
    -- Compound types (lib.rs:57-62)
    | list    : Ty → Ty
    | map     : Ty → Ty → Ty
    | set     : Ty → Ty
    | option  : Ty → Ty
    | result  : Ty → Ty → Ty
    | existential : List String → TyList → Ty
    | fixedSizeList : Ty → Dim → Ty
    | tensor : Ty → List Dim → Ty
    | sum : String → TyList → Ty
    | opaque : String → TyList → Ty
    -- Nominal record (lib.rs:67): `record User { name: String, age: Int }`
    | record : String → Row → Ty
    -- Structural record (lib.rs:69): `#{ name: "alice" }`
    | anonRecord : Row → Ty
    -- DataFrame (lib.rs:73): `DataFrame(R)` parameterized by schema type
    | dataframe : Ty → Ty
    -- Runtime-erased type boundary (lib.rs:202): `Dynamic`
    | dynamic : Ty
    -- Grouped-frame intermediate (lib.rs:206): `GroupedFrame{ row, keys }`
    | groupedFrame : Ty → List Label → Ty
    -- Compile-time tagged type metadata (lib.rs:212): `Tagged{ inner, tags }`
    | tagged : Ty → List (String × Int) → Ty
    -- Column expression type boundary (lib.rs:75): wraps element type
    | column : Ty → Ty
    -- Stream (lib.rs:95): lazy typed stream of values
    | stream : Ty → Ty
    -- Runtime wrappers (lib.rs:208-219)
    | task : Ty → Ty
    | actor : Ty → Ty
    | arc : Ty → Ty
    -- Functions (lib.rs:93)
    | function : TyList → Ty → Ty
    -- Effect-explicit function form aligned with `kea-types::FunctionType`.
    | functionEff : TyList → EffectRow → Ty → Ty
    -- Explicit quantified type annotation (Rust `Type::Forall`)
    | forall : List String → Ty → Ty
    -- Internal constructor-application terms (lib.rs:244-252)
    | app : Ty → TyList → Ty
    | constructor : String → TyList → Nat → Ty
    -- Inference variables (lib.rs:97)
    | var : TypeVarId → Ty
    -- Row as a type (lib.rs:100)
    | row : Row → Ty
    -- Tuples (lib.rs:60)
    | tuple : TyList → Ty

  /--
  A row type: fields plus an optional tail variable.

  Maps to `RowType` in `rill-types/src/lib.rs:132-138`.
  Fields are kept sorted by label for canonical representation (KERNEL §2.2).
  -/
  inductive Row : Type where
    | mk : RowFields → Option RowVarId → Row

  /-- List of types (avoids nested inductive with List). -/
  inductive TyList : Type where
    | nil  : TyList
    | cons : Ty → TyList → TyList

  /-- List of row fields (avoids nested inductive with List). -/
  inductive RowFields : Type where
    | nil  : RowFields
    | cons : Label → Ty → RowFields → RowFields

  /-- Effect rows reuse row structure (record/effect rows share the same machinery). -/
  inductive EffectRow : Type where
    | mk : Row → EffectRow
end

-- =========================================================================
-- BEq instances for mutual types
-- =========================================================================

mutual
  instance : BEq Ty where
    beq := beqTy

  instance : BEq Row where
    beq := beqRow

  instance : BEq EffectRow where
    beq := beqEffectRow

  instance : BEq TyList where
    beq := beqTyList

  instance : BEq RowFields where
    beq := beqRowFields

  def beqTy : Ty → Ty → Bool
    | .int, .int => true
    | .intN w1 s1, .intN w2 s2 => w1 == w2 && s1 == s2
    | .float, .float => true
    | .floatN w1, .floatN w2 => w1 == w2
    | .decimal p1 s1, .decimal p2 s2 => p1 == p2 && s1 == s2
    | .bool, .bool => true
    | .string, .string => true
    | .html, .html => true
    | .markdown, .markdown => true
    | .atom, .atom => true
    | .date, .date => true
    | .dateTime, .dateTime => true
    | .unit, .unit => true
    | .list a, .list b => beqTy a b
    | .map k1 v1, .map k2 v2 => beqTy k1 k2 && beqTy v1 v2
    | .set a, .set b => beqTy a b
    | .option a, .option b => beqTy a b
    | .result a1 b1, .result a2 b2 => beqTy a1 a2 && beqTy b1 b2
    | .existential b1 a1, .existential b2 a2 => b1 == b2 && beqTyList a1 a2
    | .fixedSizeList e1 d1, .fixedSizeList e2 d2 => beqTy e1 e2 && d1 == d2
    | .tensor e1 sh1, .tensor e2 sh2 => beqTy e1 e2 && sh1 == sh2
    | .sum n1 args1, .sum n2 args2 => n1 == n2 && beqTyList args1 args2
    | .opaque n1 params1, .opaque n2 params2 => n1 == n2 && beqTyList params1 params2
    | .record n1 r1, .record n2 r2 => n1 == n2 && beqRow r1 r2
    | .anonRecord r1, .anonRecord r2 => beqRow r1 r2
    | .dataframe s1, .dataframe s2 => beqTy s1 s2
    | .dynamic, .dynamic => true
    | .groupedFrame r1 k1, .groupedFrame r2 k2 => beqTy r1 r2 && k1 == k2
    | .tagged i1 tags1, .tagged i2 tags2 => beqTy i1 i2 && tags1 == tags2
    | .column a, .column b => beqTy a b
    | .stream a, .stream b => beqTy a b
    | .task a, .task b => beqTy a b
    | .actor a, .actor b => beqTy a b
    | .arc a, .arc b => beqTy a b
    | .function p1 r1, .function p2 r2 => beqTyList p1 p2 && beqTy r1 r2
    | .functionEff p1 e1 r1, .functionEff p2 e2 r2 =>
      beqTyList p1 p2 && beqEffectRow e1 e2 && beqTy r1 r2
    | .forall vars1 body1, .forall vars2 body2 => vars1 == vars2 && beqTy body1 body2
    | .app f1 args1, .app f2 args2 => beqTy f1 f2 && beqTyList args1 args2
    | .constructor n1 fixed1 arity1, .constructor n2 fixed2 arity2 =>
      n1 == n2 && beqTyList fixed1 fixed2 && arity1 == arity2
    | .var v1, .var v2 => v1 == v2
    | .row r1, .row r2 => beqRow r1 r2
    | .tuple e1, .tuple e2 => beqTyList e1 e2
    | _, _ => false

  def beqRow : Row → Row → Bool
    | .mk f1 r1, .mk f2 r2 => beqRowFields f1 f2 && r1 == r2

  def beqEffectRow : EffectRow → EffectRow → Bool
    | .mk r1, .mk r2 => beqRow r1 r2

  def beqTyList : TyList → TyList → Bool
    | .nil, .nil => true
    | .cons a as_, .cons b bs => beqTy a b && beqTyList as_ bs
    | _, _ => false

  def beqRowFields : RowFields → RowFields → Bool
    | .nil, .nil => true
    | .cons l1 t1 r1, .cons l2 t2 r2 => l1 == l2 && beqTy t1 t2 && beqRowFields r1 r2
    | _, _ => false
end

-- =========================================================================
-- Row accessors
-- =========================================================================

namespace Row

/-- Extract the fields of a row. -/
def fields : Row → RowFields
  | .mk fs _ => fs

/-- Extract the optional tail variable. -/
def rest : Row → Option RowVarId
  | .mk _ r => r

/-- Create a closed row from fields. -/
def closed (fields : RowFields) : Row :=
  .mk fields none

/-- Create an open row with fields and a tail variable. -/
def mkOpen (fields : RowFields) (rest : RowVarId) : Row :=
  .mk fields (some rest)

/-- Create an empty open row (just a row variable). -/
def emptyOpen (rest : RowVarId) : Row :=
  .mk .nil (some rest)

/-- Create an empty closed row. -/
def emptyClosed : Row :=
  .mk .nil none

/-- Is the row closed (no tail variable)? -/
def isClosed (r : Row) : Bool :=
  r.rest.isNone

/-- Is the row open (has a tail variable)? -/
def isOpen (r : Row) : Bool :=
  r.rest.isSome

end Row

-- =========================================================================
-- Effect rows
-- =========================================================================

namespace EffectRow

/-- Underlying row of an effect row. -/
def row : EffectRow → Row
  | .mk r => r

/-- Closed empty effect row (`[]`). -/
def pure : EffectRow := .mk (.mk .nil none)

/-- Closed effect row with explicit fields. -/
def closed (fields : RowFields) : EffectRow := .mk (.mk fields none)

/-- Open effect row with explicit fields and tail variable. -/
def mkOpen (fields : RowFields) (rest : RowVarId) : EffectRow := .mk (.mk fields (some rest))

/-- Is this effect row pure? -/
def isPure (e : EffectRow) : Bool :=
  match e with
  | .mk (.mk .nil none) => true
  | _ => false

end EffectRow

-- =========================================================================
-- RowFields operations
-- =========================================================================

namespace RowFields

/-- Look up a field by label. -/
def get (rf : RowFields) (label : Label) : Option Ty :=
  match rf with
  | .nil => none
  | .cons l ty rest =>
    if l == label then some ty else rest.get label

/-- Check whether the fields contain a label. -/
def has (rf : RowFields) (label : Label) : Bool :=
  match rf with
  | .nil => false
  | .cons l _ rest => l == label || rest.has label

/-- All labels in the fields. -/
def labels (rf : RowFields) : List Label :=
  match rf with
  | .nil => []
  | .cons l _ rest => l :: rest.labels

/-- Number of fields. -/
def length (rf : RowFields) : Nat :=
  match rf with
  | .nil => 0
  | .cons _ _ rest => 1 + rest.length

/-- Convert to a list of label-type pairs. -/
def toList (rf : RowFields) : List (Label × Ty) :=
  match rf with
  | .nil => []
  | .cons l ty rest => (l, ty) :: rest.toList

/-- Fields are sorted by label. -/
def Sorted : RowFields → Prop
  | .nil => True
  | .cons _ _ .nil => True
  | .cons l₁ _ rest@(.cons l₂ _ _) => l₁ < l₂ ∧ rest.Sorted

/-- Append two field lists (does not maintain sort order). -/
def append (a b : RowFields) : RowFields :=
  match a with
  | .nil => b
  | .cons l ty rest => .cons l ty (rest.append b)

end RowFields

-- =========================================================================
-- TyList operations
-- =========================================================================

namespace TyList

/-- Convert to a standard List. -/
def toList (tl : TyList) : List Ty :=
  match tl with
  | .nil => []
  | .cons t rest => t :: rest.toList

/-- Convert from a standard List. -/
def fromList (l : List Ty) : TyList :=
  match l with
  | [] => .nil
  | t :: rest => .cons t (fromList rest)

/-- Length. -/
def length (tl : TyList) : Nat :=
  match tl with
  | .nil => 0
  | .cons _ rest => 1 + rest.length

end TyList

-- =========================================================================
-- TypeScheme
-- =========================================================================

/--
A type scheme: `∀ αs ρs. T` with lacks constraints and trait bounds.

Maps to `TypeScheme` in `rill-types/src/lib.rs:304-311`.
Arises from let-generalization.
-/
structure TypeScheme where
  /-- Quantified type variables. -/
  typeVars : List TypeVarId
  /-- Quantified row variables. -/
  rowVars : List RowVarId
  /-- Lacks constraints: which labels each quantified row var must lack. -/
  lacks : List (RowVarId × List Label)
  /-- Trait bounds on quantified type vars (e.g., `T: Additive`).
      Maps to `bounds: BTreeMap<TypeVarId, BTreeSet<String>>` in Rust. -/
  bounds : List (TypeVarId × List String)
  /-- Kind assignments for quantified type variables (defaults to `Kind.star`). -/
  kinds : List (TypeVarId × Kind)
  /-- The underlying type. -/
  ty : Ty

namespace TypeScheme

/-- A monomorphic scheme (no quantified variables). -/
def mono (ty : Ty) : TypeScheme :=
  { typeVars := [], rowVars := [], lacks := [], bounds := [], kinds := [], ty }

/-- Is the scheme monomorphic? -/
def isMono (s : TypeScheme) : Bool :=
  s.typeVars.isEmpty && s.rowVars.isEmpty

/-- Look up trait bounds for a type variable. -/
def getBounds (s : TypeScheme) (tv : TypeVarId) : List String :=
  match s.bounds.find? (fun (v, _) => v == tv) with
  | some (_, traits) => traits
  | none => []

end TypeScheme
