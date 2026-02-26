# Brief: Advanced Type Features

**Status:** design
**Priority:** v1-critical
**Depends on:** 0f-memory-model (Unique/borrow must be settled)
**Blocks:** 0h-stdlib-errors, Phase 1 (self-hosting requires full type system)

## Motivation

GADTs (for typed actor protocols), associated types, supertraits,
and the `Eff` kind are the type system features that make Kea's
abstractions work. GADTs enable typed actor message protocols where
the response type is encoded in the message constructor. The `Eff`
kind enables effect-parameterised types (KERNEL §5.14, §6.6).
These are the type theory pieces — the stdlib, deriving, and error
messages are split into a separate brief (0h) since they're
engineering work that can be parallelized.

**No HKTs.** Kea's kind system has `*` and `Eff`, not `* -> *`.
Effects replace the primary motivation for HKTs — IO, State, Error,
Reader are all effects, not monadic types. Handler composition
replaces monadic composition. The remaining use case (generic
programming over containers: `Functor`, `Traversable`) is served
by concrete inherent methods (`List.map`, `Option.map`), which is
what Rust does. The stdlib doesn't need `Functor` to self-host,
and Kea doesn't need `* -> *` to express anything in its core
abstractions. GADTs, effect rows, and associated types are all
kind `*` or `Eff`. HKTs are an additive feature — if a library
author makes a compelling case, they can be added later without
breaking anything. rill-infer's HKT machinery remains available
as reference.

## What transfers from Rill

**rill-infer** (46,268 LOC):
- Trait system: rill has trait definitions, implementations,
  coherence checking (orphan rule), and basic supertraits.
  This transfers and extends.
- Type variable handling: rill's unifier handles polymorphic
  type variables. Extends to GADT refinement variables.
- Property tests: rill's 4,554 LOC of property tests cover
  row unification and inference invariants. Extend for GADTs.
- Test infrastructure: rill's 18,068 LOC of typeck tests
  provide patterns for testing complex type features.

**rill-types** (3,310 LOC, already cannibalised in 0b):
- Kind system exists but only for `*`. Extend for `Eff` kind
  and GADT return type indices.

**rill-eval** (structural reference):
- Trait evidence system (2,860 LOC): how rill resolves trait
  implementations at runtime. Informs how Kea compiles trait
  dispatch.
- Stdlib implementations: patterns for Map, Set, String,
  file IO, JSON, testing utilities.

## What's new

### 1. GADTs (KERNEL §3.3, §4.4)

Constructors with specialised return types:

```kea
enum Expr T
  IntLit(value: Int)                              : Expr Int
  BoolLit(value: Bool)                            : Expr Bool
  Add(left: Expr Int, right: Expr Int)            : Expr Int
  If(cond: Expr Bool, then: Expr T, else: Expr T) : Expr T
```

Pattern matching on GADT constructors introduces type equality
constraints that refine variables within the match arm. This
is branch-local — refinement doesn't extend past the arm.

Implementation:
- Parser: constructor return type annotations (from 0a)
- Type checker: when matching a GADT constructor, unify the
  scrutinee type with the constructor's return type. This
  produces equalities on type variables. Apply these equalities
  within the match arm only.
- Key difficulty: GADT refinement interacts with type inference.
  The standard approach is "outside-in" checking — GADT match
  arms are checked against an expected type, not inferred. This
  means GADTs require type annotations on match expressions or
  enclosing functions in some cases.

**Critical for actors:** The `CounterMsg T` protocol GADT is
the mechanism for typed ask/tell. Getting GADT refinement right
is essential for the actor story.

### 2. Eff Kind (KERNEL §6.6)

The kind system has two kinds: `*` (types) and `Eff` (effect rows).
No `* -> *`. No higher-kinded type parameters.

```kea
struct Server E        -- E : Eff (inferred from effect position)
  handler: Request -[E]> Response
```

Implementation:
- Extend the kind system from `*` to `*` + `Eff`
- Kind inference: parameters used in effect position (`-[E]>`)
  are inferred to have kind `Eff`
- Kind checking: verify type parameters are used consistently
  (can't use a `*` parameter in effect position or vice versa)
- Report clear errors on kind mismatches

### 3. Associated Types (KERNEL §6.5)

```kea
trait Iterator
  type Item
  fn next(_ self: Self) -> Option (Self.Item, Self)
```

Associated types are critical for the collection trait story.
Without HKTs, `Foldable` uses an associated type for the element:

```kea
trait Foldable
  type Item
  fn fold(_ self: Self, _ init: B, _ f: (B, Self.Item) -> B) -> B
```

`List Int` implements `Foldable` with `type Item = Int`. Default
methods (`sum`, `any`, `all`, `find`) call `fold`. This is
Elixir's Enum protocol — traits on concrete types, associated
types for the element, no HKTs needed.

Implementation:
- Type checker: associated types are resolved when the
  implementing type is known
- When the type is polymorphic (`T: Iterator`), `T.Item` is
  an abstract type — equality only resolved when `T` is
  instantiated
- Rill has some associated type support — check what transfers

### 4. Supertraits (KERNEL §6.7)

```kea
trait Ord where Self: Eq
  fn compare(_ self: Self, _ other: Self) -> Ordering
```

Implementation:
- When checking `T: Ord`, also verify `T: Eq`
- Supertrait methods are available when the subtrait is in scope
- Rill has this — should transfer from rill-infer

### 5. Deriving (KERNEL §6.9)

Moved to 0h-stdlib-errors brief. Deriving is implementation
machinery that depends on the type features above being stable.

## Implementation Plan

### Step 1: GADTs

- Extend enum type representation for GADT constructors
- Pattern matching: unify scrutinee with constructor return type
- Refinement: apply equalities within match arm scope
- Test: Expr GADT from KERNEL §3.3 works. CounterMsg from §19.4
  works. Refinement is correctly scoped.

### Step 2: Eff kind

- Extend kind system: `*` + `Eff` (no `* -> *`)
- Kind inference: parameters in effect position infer `Eff`
- Kind checking: consistent usage of type vs effect parameters
- Verify: effect-parameterised types (`Server E`, `Step E A`)
  kind-check correctly with `E : Eff`
- Test: Actor trait with associated types works. Kind errors
  are comprehensible. Effect row params infer `Eff` kind.

### Step 3: Associated types and supertraits

- Associated type resolution in the type checker
- Supertrait verification
- Both should be partially available from rill — check what
  transfers and extend

### Step 4: Deriving, stdlib, error messages

See 0h-stdlib-errors brief. Can begin in parallel once GADTs
and the Eff kind are stable.

## Testing

- GADTs: refinement works, is branch-local, complex nested
  patterns work
- Kind system: `Eff` kind inferred, effect-parameterised types
  kind-check, kind errors are clear
- Associated types: resolve correctly for concrete and
  polymorphic types
- Supertraits: supertrait methods available, missing supertrait
  impl is clear error
- Deriving, stdlib, error messages: see 0h-stdlib-errors brief

## Definition of Done

- GADTs work (including typed actor protocols with CounterMsg)
- Kind system supports `Eff` kind for effect-parameterised types
- Associated types resolve correctly
- Supertraits checked and available
- The type system supports the abstractions needed for
  self-hosting (0h handles the rest)
- `mise run check` passes

## Open Questions

- How do we handle GADT + effect interaction? (A GADT match
  arm that refines a type variable — does this affect the
  effect row? Probably not — effect variables (`Eff` kind)
  and type variables (`*` kind) are independent. But needs
  verification.)
- Which traits should be derivable in v0? (Moved to 0h.)
- Should Map/Set use HAMT from the start? (Moved to 0h.)
