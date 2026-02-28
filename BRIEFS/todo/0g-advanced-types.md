# Brief: Advanced Type Features

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0d-codegen-pure (needs working codegen), 0c-effect-handlers (needs effect rows for Eff kind)
**Blocks:** Phase 1 (self-hosting requires full type system + stdlib tier 3)
**Also read before implementing:**
- [effects-platform-vision](../design/effects-platform-vision.md) — Eff kind is load-bearing for effect-parameterised types (Server E, Step E A). GADTs enable typed actor protocols.
- [lean-formalization](lean-formalization.md) — GADT refinement soundness and Eff kind consistency are formalization targets.
- [practical-language-gaps](practical-language-gaps.md) — Gap 4 (early-exit ergonomics) and Gap 5 (tuple-case optimization) land in 0g. Assess whether `Fail` for non-error early exit is ergonomic enough during Tier 3 stdlib writing.

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

```kea
@derive(Show, Eq)
struct Point
  x: Float
  y: Float
```

Compiler-generated trait implementations. Tightly coupled to the
trait system and associated types — must land in the same phase.

Implementation:
- For each derivable trait, a codegen recipe that produces an
  impl block from the struct/enum definition
- Start with: Show, Eq, Ord, Encode, Decode
- Each derived impl must type-check (it's generated code, not magic)

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

### Step 4: Deriving

Implement @derive for Show, Eq, Ord, Encode, Decode on structs and
enums. This is implementation machinery that depends on steps 1-3
(GADTs, Eff kind, associated types, supertraits) being stable.

### Step 5: Stdlib Tier 3 — Abstractions

When 0g lands, the stdlib gains trait hierarchies, @derive recipes,
and the abstractions that make the stdlib ergonomic. See
[stdlib-bootstrap](../todo/stdlib-bootstrap.md).

```
stdlib/
  foldable.kea     -- Foldable trait + associated Item type
  iterator.kea     -- Iterator trait + lazy iteration
  derive/show.kea  -- @derive(Show) recipe
  derive/eq.kea    -- @derive(Eq) recipe
  derive/ord.kea   -- @derive(Ord) recipe
  codec.kea        -- Encode/Decode traits
  json.kea         -- JSON via Encode/Decode
  sorted_map.kea   -- SortedMap (Ord supertrait constraint)
  sorted_set.kea   -- SortedSet
  format.kea       -- String formatting, pretty-printing
```

**~800-1000 lines.** Supertraits enable `Ord : Eq`. @derive(Show,
Eq, Ord) works on structs and enums. This tier completes the
self-hosting stdlib — the compiler has collections, IO, error
handling, traits, serialization, and formatting.

## Cross-Cutting: Error Message Quality

**Every type feature in 0g ships with its error messages designed, not
deferred to 0h.** Error messages are a first-class feature (CLAUDE.md).
Deferring them means retrofitting, which always produces worse results.

**Study Rill's diagnostic architecture first.** The rill codebase at
`/Users/chris/Projects/rill` has a battle-tested error message system
that transfers directly:

- **`rill-diag/src/lib.rs`** (342 LOC) — `Diagnostic` struct decoupled
  from rendering. Closed `Category` enum with stable error codes
  (E0001-E00XX). Builder pattern: `Diagnostic::error(cat, msg).at(loc).with_help(fix)`.
- **`BRIEFS/design/error-system.md`** (2,500 LOC) — comprehensive
  design for how to build a complex type system with good errors
  simultaneously. Constraint provenance: every type/effect constraint
  carries its source location and human-readable reason through
  unification. When unification fails, the error explains *why* the
  constraint exists, not just *what* failed.
- **`docs/PEDAGOGY.md`** — error message guidelines. Domain language,
  not type theory. Actionable suggestions with concrete code. Theory
  terms only in `note:` sections for library authors.
- **Rendering pipeline** — same `Diagnostic` renders via ariadne (CLI),
  JSON (MCP), LSP. Decoupled from error creation.

The constraint provenance pattern is especially critical for effects:
an effect constraint may travel through three function calls before
surfacing as "unhandled effect." Without provenance, the error says
"unhandled Log." With provenance: "unhandled Log — entered via
`logger.info()` on line 12, which calls `Log.write` at logger.kea:42."

kea-diag already has Rill's full pattern (closed `Category` enum,
stable codes, builder, decoupled rendering). The 0g agent needs to
add new categories for effect and advanced type errors:

- `UnhandledEffect` (E0043) — effect in body not in signature
- `UnnecessaryHandler` (E0044) — handler covers effect not performed
- `KindMismatch` (E00XX) — `*` vs `Eff` kind confusion
- `GadtRefinementFailure` (E00XX) — GADT arm body violates refinement
- `MissingSupertraitImpl` (E00XX) — implements Ord but not Eq
- `DeriveFailure` (E00XX) — @derive on field that lacks the trait

Each category gets a stable code, description, example fix, and
snapshot test — same pattern as existing categories in kea-diag.

For each feature, the implementing agent must deliver:

- **GADTs:** GADT refinement failure explains which constructor
  introduced which type equality, and why the arm body doesn't
  satisfy it. No exposed unification variables.
- **Eff kind:** Kind mismatch between `*` and `Eff` explains "this
  parameter is used as a type here but as an effect row there" with
  source locations for both uses.
- **Associated types:** When `T.Item` can't resolve because `T`'s
  implementing type is unknown, explain what trait bound is missing
  and where to add it.
- **Supertraits:** Missing supertrait impl says "Point implements Ord
  but not Eq; Ord requires Eq" — not "trait bound not satisfied."
- **Deriving:** @derive failure on a field that doesn't implement the
  trait explains which field, which trait, and suggests a manual impl.

Row-diff errors (structural missing/extra for records and effects)
should work for all new type features. Effect provenance (tracing
where each effect enters the row) must work for Eff-kinded parameters.

**Effect errors are both the biggest risk and biggest opportunity.**
Effects are Kea's novel core — users will be learning them for the
first time. Every effect error must teach, not just report:

- When an effect is unhandled, show *where* it entered the effect row
  (which call introduced it) and *how* to handle it (concrete code).
- When a handler covers an effect not performed, say so — don't
  silently accept dead handlers.
- When effect rows don't unify, show the structural diff: "your
  function performs [IO, Log, Fail E] but the caller expects [IO]
  — unhandled: Log, Fail E."
- When an Eff-kinded parameter is used where `*` is expected (or
  vice versa), explain in concrete terms: "Server expects an effect
  row here (like [IO, Log]), not a type (like Int)."

These errors are Kea's chance to make effects feel approachable
instead of academic. Get them right in 0g, not as 0h polish.

Snapshot test every error category. See 0h brief for the full error
message design language and examples.

## Testing

- GADTs: refinement works, is branch-local, complex nested
  patterns work
- Kind system: `Eff` kind inferred, effect-parameterised types
  kind-check, kind errors are clear
- Associated types: resolve correctly for concrete and
  polymorphic types
- Supertraits: supertrait methods available, missing supertrait
  impl is clear error
- Deriving: @derive(Show, Eq, Ord) works on structs and enums
- Stdlib Tier 3: Foldable/Iterator enable collection abstractions
- **Error messages: snapshot tests for every error category above**

## Definition of Done

- GADTs work (including typed actor protocols with CounterMsg)
- Kind system supports `Eff` kind for effect-parameterised types
- Associated types resolve correctly
- Supertraits checked and available
- @derive works for Show, Eq, Ord, Encode, Decode
- Stdlib Tier 3 complete (Foldable, Iterator, JSON, sorted collections)
- Stdlib sufficient for compiler self-hosting
- **Error messages: every new type feature has snapshot-tested diagnostics**
- **No unification variables exposed in any error message**
- `mise run check-full` passes

## Open Questions

- How do we handle GADT + effect interaction? (A GADT match
  arm that refines a type variable — does this affect the
  effect row? Probably not — effect variables (`Eff` kind)
  and type variables (`*` kind) are independent. But needs
  verification.)
- Which traits should be derivable in v0? (Proposal: Show, Eq,
  Ord, Encode, Decode. Everything else requires manual implementation.)
- Should Map/Set use HAMT from the start? (Proposal: HAMT. It's
  the specified representation in KERNEL §1.2.)
