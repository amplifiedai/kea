# Brief: Stdlib, Deriving, and Error Messages

**Status:** design
**Priority:** v1-critical
**Depends on:** 0g-advanced-types (needs GADTs, Eff kind stable)
**Blocks:** Phase 1 (self-hosting requires full stdlib)

## Motivation

Split from 0g because this is engineering work, not type theory.
Deriving, stdlib modules, and error messages can be parallelized
across multiple agents once the type features from 0g are stable.
The type theory in 0g needs careful sequential design; this brief
is a parallelizable surface area.

## What transfers from Rill

**rill-eval** (structural reference):
- Trait evidence system (2,860 LOC): informs how derived impls
  are dispatched at runtime
- Stdlib implementations: Map, Set, String, file IO, JSON,
  testing utilities — behavioral specs for what compiled
  versions need to do
- Collection implementations: HAMT-based Map/Set patterns

**rill-diag** (341 LOC, already cannibalised in 0a):
- Diagnostic infrastructure extends for new error categories
- Span-based error reporting patterns transfer directly

## Decisions

- **Collection traits on concrete types. No HKT traits.**
  `Foldable`, `Enumerable`, `Filterable`, `Iterator` are regular
  traits (kind `*`) on concrete types — `List Int as Foldable`,
  not `List as Functor`. This is Elixir's Enum protocol: any type
  implementing `Foldable` gets `fold`, `sum`, `find` via trait
  dispatch.

  `map` is an inherent method (`List.map`, `Option.map`) because
  it returns the same container type — that's a container-specific
  operation, not a generic fold.

  There are no `Functor`/`Applicative`/`Monad`/`Traversable`
  traits. Effects replace the monadic composition that motivates
  HKTs in Haskell.

## Implementation Plan

### Step 1: Deriving (KERNEL §6.9)

```kea
@derive(Show, Eq)
struct Point
  x: Float
  y: Float
```

Compiler-generated trait implementations:
- For each derivable trait, a codegen recipe that produces an
  impl block from the struct/enum definition
- Start with: Show, Eq, Ord, Codec
- Each derived impl must type-check (it's generated code, not
  magic)

### Step 2: Full stdlib for self-hosting

The Kea compiler in Kea needs:
- **Collections:** Map (HAMT), Set (HAMT), SortedMap, SortedSet
- **String interning:** for identifier deduplication
- **File IO:** read/write source files (via IO effect)
- **CLI:** argument parsing for `kea build`, `kea run`
- **JSON:** for MCP protocol, config files
- **Formatting:** string formatting, pretty-printing for
  diagnostics

Reference: rill-eval's stdlib modules provide behavioral specs
for all of these. The implementations will be different (compiled
vs interpreted) but the APIs inform design.

This is highly parallelizable — each stdlib module is independent.

### Step 3: Error message investment

KERNEL ethos: "error messages are a feature." This phase invests
heavily:
- Row polymorphism errors must not show raw type variables
  — explain in terms of "this function expects a record with
  field X, but you passed one without it"
- Effect errors must explain which effect is unhandled and
  suggest adding a handler
- GADT errors must explain refinement failures
- Kind errors must explain `*` vs `Eff` mismatches in plain language
- Ambiguous dispatch errors must suggest qualified syntax
  (CALL-SYNTAX.md diagnostic section)

Adapt rill-diag's diagnostic patterns. Rill has good error
infrastructure — extend it for Kea's novel type features.

## Testing

- Deriving: generated impls are correct, derive on enum works
- Stdlib: comprehensive tests for Map, Set, String, IO, JSON
- Error messages: snapshot tests for every error category

## Definition of Done

- @derive works for Show, Eq, Ord, Codec
- Stdlib sufficient for compiler self-hosting
- Error messages are human-readable for all type features
- `mise run check` passes

## Open Questions

- Which traits should be derivable in v0? (Proposal: Show, Eq,
  Ord, Codec. Everything else requires manual implementation.)
- Should Map/Set use HAMT from the start or a simpler tree?
  (Proposal: HAMT. It's the specified representation in
  KERNEL §1.2, and there are good Rust HAMT implementations
  to reference.)
- How much error message polish is enough for v1? (Proposal:
  every error must have a clear explanation and at least one
  suggestion. Fancy formatting and color can come later.)
