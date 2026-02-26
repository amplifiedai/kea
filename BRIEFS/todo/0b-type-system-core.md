# Brief: Type System Core

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0a-lexer-parser (needs AST definitions)
**Blocks:** 0c-effect-handlers, 0d-codegen-pure, everything downstream

## Motivation

The type system is Kea's backbone. HM inference with Rémy row
polymorphism for both records and effects, the trait system, and
UMS resolution all need to work before anything else can build
on top. This is the highest-leverage cannibalisation target —
rill-infer is 46K lines of battle-tested inference engine with
extensive property tests.

## What transfers from Rill

**rill-types** (3,310 LOC):
- `Type` enum, `RowType`, `TypeVarId`, `RowVarId` — direct transfer
- `Substitution` type and operations — direct transfer
- `Kind` system — direct transfer, extend with `Eff` kind
- Remove: `DataFrameType`, `ColumnType`, `SqlType`, `ActorType`,
  `DimensionType`, `AggregateType`
- Add: `EffectRow` (new row kind using same `RowType` machinery),
  `HandlerType`, `UniqueType`, effect set representation

**rill-infer** (46,268 LOC):
- `lib.rs` (4,098 LOC): Unifier, provenance tracking, variable
  allocation — direct transfer. This is the Rémy row unification
  engine. It works for records; extending it to effects means
  adding a second row kind that uses the same algorithm.
- `typeck.rs` (19,016 LOC): Expression-level HM inference with
  let-generalisation — structural transfer. Large parts copy
  directly (literal checking, binary ops, let bindings, lambda
  inference, pattern matching). Parts that need rewriting: module
  resolution (struct-everything instead of bare functions), method
  dispatch (UMS instead of pipes), effect tracking.
- `exhaustive.rs` (357 LOC): Exhaustiveness checking — direct
  transfer.
- `trace.rs` (175 LOC): Compiler tracing — direct transfer.
- `prop_tests.rs` (4,554 LOC): Property tests — transfer and
  extend for effect rows. These are gold. They catch bugs that
  unit tests don't.
- `typeck_tests.rs` (18,068 LOC): Unit tests — use as reference
  for test patterns. Rewrite test cases for Kea syntax.

**rill-diag** (341 LOC):
- Should already exist from 0a. Diagnostic categories may need
  extending for effect-related errors.

## What's new (not in Rill)

1. **Effect rows.** Same Rémy unification algorithm, new row kind.
   An effect row `[IO, Fail E | e]` is structurally identical to
   a record row `{ io: IO, fail: Fail E | r }` from the
   unifier's perspective. The key insight: we don't need a new
   unification algorithm, we need to apply the existing one to
   a new domain.

2. **Effect annotations in function types.** `->` is the pure
   arrow (empty effect row). `-[e]>` is the effectful arrow.
   Function types carry an effect row alongside parameter and
   return types.

3. **Struct-everything scoping.** Name resolution must handle:
   - Inherent methods (defined inside struct block)
   - Singleton module functions (struct with no fields)
   - Nested types (`Parent.Child`)
   - `Type as Trait` implementation blocks
   - Prelude traits (Appendix C) always in scope

4. **UMS resolution** (CALL-SYNTAX.md):
   - `expr.method(args)` → inherent first, then trait search
   - `expr.Qual::method(args)` → qualified dispatch
   - `$` receiver placement
   - Field vs method: no parens = field, parens = method

5. **Labeled and positional parameters** (KERNEL §10.2):
   - `_` prefix marks positional params
   - Labeled params are passed by name at call site
   - Receiver fills first `_` param (or `$` position)

## Implementation Plan

### Step 1: kea-types crate

Copy rill-types wholesale. Then:
- Rename rill → kea everywhere
- Remove DataFrame/SQL/Actor/Dimension/Aggregate types
- Add `EffectRow` variant (or extend existing `RowType` with a
  row kind discriminator)
- Add `HandlerType` for handler expressions
- Add effect set representation on `FunctionType`
- Keep `Substitution`, `TypeVarId`, `RowVarId`, `Kind` as-is
- Verify: `cargo test -p kea-types` passes after cleanup

### Step 2: kea-infer crate — unification core

Copy rill-infer's `lib.rs` (unifier, provenance, variable
allocation). Then:
- Rename rill → kea
- Remove rill-specific constraint kinds
- Extend unification to handle effect rows (same algorithm,
  new row kind)
- Port property tests from `prop_tests.rs`, extend with
  effect row properties:
  - Effect row union is commutative
  - Effect row union is idempotent
  - Adding then handling an effect round-trips
  - Lacks constraints propagate correctly for effects

### Step 3: kea-infer crate — type checking

Copy rill-infer's `typeck.rs` structure. This is the biggest
adaptation:
- Literal, binary op, let-binding inference → mostly direct copy
- Lambda inference → add effect row to function type
- Pattern matching → copy exhaustiveness from rill
- **Rewrite:** Name resolution for struct-everything
  - Look up inherent methods in struct scope
  - Look up trait methods from in-scope traits
  - Handle `Type.function()` prefix calls
  - Handle `expr.method()` dot calls (UMS)
  - Handle `expr.Qual::method()` qualified dispatch
- **Rewrite:** Method resolution per CALL-SYNTAX.md
- **New:** Effect inference — bottom-up union of effect sets
- **New:** Effect annotation checking — explicit annotation must
  be at least as broad as inferred
- **New:** Labeled parameter matching at call sites

### Step 4: Tests

- Port rill-infer's property tests, extend for effects
- Write snapshot tests for type inference on Kea source:
  - Pure functions: inferred as `->`
  - Functions calling IO operations: inferred as `-[IO]>`
  - Effect-polymorphic higher-order functions: `e` variable flows
  - Row-polymorphic record functions: `{ name: String | r }`
  - UMS resolution: dot calls desugar correctly
  - Error cases: ambiguous dispatch, missing method, missing
    trait implementation
- Diagnostic snapshot tests: error messages for type errors must
  be human-readable, reference source locations, and never show
  raw type variable IDs

## Testing

- `cargo test -p kea-types -p kea-infer` passes
- Property tests for row unification (records and effects)
- Snapshot tests for inferred types on ~30 representative programs
- Snapshot tests for error diagnostics on ~15 error cases
- Effect inference: functions performing effects get correct
  effect rows
- UMS: dot calls resolve correctly per CALL-SYNTAX.md

## Definition of Done

- Can type-check pure Kea programs with structs, enums, pattern
  matching, row-polymorphic records, traits, and UMS
- Effect annotations parse and are checked against inferred effects
- Effect rows unify using the same algorithm as record rows
- Property tests cover row unification invariants for both kinds
- Error messages are human-readable with source locations
- `mise run check` passes

## Open Questions

- Should effect inference be integrated into the main HM pass or
  run as a separate post-pass? (Proposal: integrated — effect
  variables are just row variables, they participate in the same
  unification. This is the Koka approach and it works because
  rows are rows.)
- How do we handle the `Fail E` uniqueness constraint ("at most
  one Fail in an effect set")? (Proposal: a special lacks-like
  constraint on the effect row variable. Or: defer this to 0c
  and allow multiple Fail effects initially.)
