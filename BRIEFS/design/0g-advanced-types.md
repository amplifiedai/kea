# Brief: Advanced Type Features

**Status:** design
**Priority:** v1-critical
**Depends on:** 0f-memory-model (Unique/borrow must be settled)
**Blocks:** 0h-stdlib-errors, Phase 1 (self-hosting requires full type system)

## Motivation

GADTs (for typed actor protocols), HKTs (for Functor/Monad/Traversable),
associated types, and supertraits are the type system features that make
Kea's abstractions work. GADTs enable typed actor message protocols where
the response type is encoded in the message constructor. HKTs enable
Functor/Monad/Traversable across container types. These are the type
theory pieces — the stdlib, deriving, and error messages are split into
a separate brief (0h) since they're engineering work that can be
parallelized.

## What transfers from Rill

**rill-infer** (46,268 LOC):
- Trait system: rill has trait definitions, implementations,
  coherence checking (orphan rule), and basic supertraits.
  This transfers and extends.
- Type variable handling: rill's unifier handles polymorphic
  type variables. Extend for higher-kinded variables.
- Property tests: rill's 4,554 LOC of property tests cover
  row unification and inference invariants. Extend for GADTs
  and HKTs.
- Test infrastructure: rill's 18,068 LOC of typeck tests
  provide patterns for testing complex type features.

**rill-types** (3,310 LOC, already cannibalised in 0b):
- Kind system exists but only for `*`. Extend for `* -> *`
  (HKTs) and GADT return type indices.

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

### 2. HKTs (KERNEL §6.6)

Type parameters with higher kinds:

```kea
trait Functor F
  fn map(_ self: F A, _ f: A -> B) -> F B
```

`F` has kind `* -> *`. Kind inference determines this from usage.

Implementation:
- Extend the kind system from `*` to `* -> *`, `* -> * -> *`,
  etc. (or use kind variables with inference)
- Kind checking: verify type applications are well-kinded
- Kind inference: infer kinds from trait definitions and
  implementations
- Cranelift: HKTs are erased at runtime. They affect dispatch
  (which Functor impl to use) but not representation.

**No explicit kind annotations in v0** (KERNEL §6.6). Kinds
are inferred. This is simpler to implement and friendlier to
use, but may produce confusing errors when kind inference fails.
Invest in error messages.

### 3. Associated Types (KERNEL §6.5)

```kea
trait Iterator
  type Item
  fn next(_ self: Self) -> Option (Self.Item, Self)
```

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

### Step 2: HKTs

- Extend kind system (`*`, `* -> *`, kind variables)
- Kind inference on trait definitions
- Kind checking on trait implementations and type applications
- Prelude traits: Functor, Applicative, Monad, Traversable
- Test: `List as Functor` works. `Option as Monad` works.
  Kind errors are comprehensible.

### Step 3: Associated types and supertraits

- Associated type resolution in the type checker
- Supertrait verification
- Both should be partially available from rill — check what
  transfers and extend

### Step 4: Deriving, stdlib, error messages

See 0h-stdlib-errors brief. Can begin in parallel once GADTs
and HKTs are stable.

## Testing

- GADTs: refinement works, is branch-local, complex nested
  patterns work
- HKTs: Functor/Monad/Traversable work, kind errors are clear
- Associated types: resolve correctly for concrete and
  polymorphic types
- Supertraits: supertrait methods available, missing supertrait
  impl is clear error
- Deriving, stdlib, error messages: see 0h-stdlib-errors brief

## Definition of Done

- GADTs work (including typed actor protocols with CounterMsg)
- HKTs work (Functor, Applicative, Monad, Traversable)
- Associated types resolve correctly
- Supertraits checked and available
- The type system supports the abstractions needed for
  self-hosting (0h handles the rest)
- `mise run check` passes

## Open Questions

- Should kind annotations be available even if not required?
  (KERNEL says no for v0. But they could help with error
  messages. Proposal: no syntax for them, but show inferred
  kinds in error messages and `:type` output.)
- How do we handle GADT + effect interaction? (A GADT match
  arm that refines a type variable — does this affect the
  effect row? Probably not — effect variables and type
  variables are independent. But needs verification.)
- Which traits should be derivable in v0? (Moved to 0h.)
- Should Map/Set use HAMT from the start? (Moved to 0h.)
