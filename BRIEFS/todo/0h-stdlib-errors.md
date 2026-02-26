# Brief: Stdlib, Deriving, and Error Messages

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0g-advanced-types (needs GADTs, Eff kind stable for deriving and collection traits), 0e-runtime-effects (IO granularity decision shapes stdlib module boundaries)
**Blocks:** Phase 1 (self-hosting requires full stdlib)
**Also read before implementing:**
- [effects-platform-vision](../design/effects-platform-vision.md) — stdlib IS the effect vocabulary. IO decomposition directly shapes stdlib module boundaries.
- [testing](testing.md) — `assert` uses Fail, `check` uses Test effect. Test stdlib is the first consumer of the dual-effect assertion model.
- [tooling-dx](../design/tooling-dx.md) — `kea doc` must be effect-aware. Stdlib is the reference for how documentation presents effect signatures.

## Motivation

The stdlib is where Kea's effects-first design becomes tangible. In most
languages, stdlib is a bag of functions. In Kea, **stdlib is the effect
vocabulary** — the set of named capabilities that every program composes
from. `File.read` doesn't return `Result<String, IoError>`, it performs
`IO`. `Map.get` doesn't return `Option T`, it can perform `Fail KeyNotFound`.
`Random.int` performs `Rand`. Every stdlib function's type signature
tells you exactly what capabilities it requires, and every handler tells
you exactly what policy governs those capabilities.

This is also where error messages become a genuine differentiator.
Kea has something no other language has for error reporting: **row diffs**.
When a type doesn't match, we know *structurally* what's missing and
what's extra. When an effect row is too weak, we know exactly which
capability is unhandled. This makes errors that explain problems in
terms users understand, not type theory they don't.

Split from 0g because this is engineering work, not type theory.
Deriving, stdlib modules, and error messages can be parallelised
across multiple agents once the type features from 0g are stable.

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

- **Stdlib functions perform effects, not return Results.**
  The Fail/Result duality (KERNEL §5.8) means the stdlib API
  surface uses effects for operations that genuinely fail:

  ```kea
  -- IO operations: effects-first (failure is inherent)
  fn read_file(path: String) -[IO, Fail IoError]> String

  -- caller decides policy via handlers:
  let content = catch read_file("config.toml")  -- Result String IoError
  -- or let it propagate:
  let content = read_file("config.toml")        -- Fail IoError in caller's row
  ```

  But **pure lookups stay pure**. Don't force Fail into common
  data structure operations:

  ```kea
  -- Map: pure lookups return Option, effectful variant is opt-in
  fn get(self: Map K V, key: K) -> Option V           -- default, pure
  fn get_or_fail(self: Map K V, key: K) -[Fail KeyNotFound]> V  -- opt-in

  -- same pattern for List, Set, etc.
  fn first(self: List T) -> Option T                   -- pure
  fn first_or_fail(self: List T) -[Fail Empty]> T      -- opt-in
  ```

  The principle: effects for I/O and operations that *inherently*
  fail (file not found, network error). Option for data structure
  lookups where absence is a normal result, not an error. The
  programmer opts into Fail when they want propagation.

  This is not `Result` vs exceptions. It's structural: the effect
  row tracks capabilities, `catch` converts to `Result` at any
  boundary, `?` converts back. The programmer chooses the style
  per call site, not per library.

- **IO decomposition (see 0e entry gate).** If the IO granularity
  decision is Option A (decomposed), stdlib modules align to effects:

  | Module | Primary effect | Scope |
  |--------|---------------|-------|
  | `kea-io` | `IO` | File, stdout/stderr |
  | `kea-net` | `Net` | HTTP, TCP, DNS |
  | `kea-time` | `Clock` | System time, monotonic |
  | `kea-rand` | `Rand` | Random number generation |
  | `kea-log` | `Log` | Structured logging |

  Each stdlib module *is* its effect. Import the module, get the
  capability. Handle the effect, define the policy.

  **Fallback if 0e chooses monolithic IO (Option B):** stdlib ships
  a single `kea-io` module with one `IO` effect. The module structure
  still separates concerns internally (file ops, net ops, time ops)
  so that decomposition into separate effects later is a refactor,
  not a rewrite. API signatures use `IO` where they'd use `Net`/`Clock`/`Rand`.

## Implementation Plan

This brief is large. It lands in three checkpoints, each independently
shippable and testable.

### Checkpoint 1: Deriving (KERNEL §6.9)

```kea
@derive(Show, Eq)
struct Point
  x: Float
  y: Float
```

Compiler-generated trait implementations:
- For each derivable trait, a codegen recipe that produces an
  impl block from the struct/enum definition
- Start with: Show, Eq, Ord, Encode, Decode
- Each derived impl must type-check (it's generated code, not
  magic)

**Checkpoint 1 gate:** `@derive(Show, Eq)` works on structs and enums.
Derived impls type-check. `mise run check-full` passes.

### Checkpoint 2: Core stdlib for self-hosting

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

**Checkpoint 2 gate:** Map, String, File IO, JSON all work. Compiler
can read a `.kea` file, parse it, and write output. `mise run check-full` passes.

### Checkpoint 3: Error message investment

KERNEL ethos: "error messages are a feature." PEDAGOGY.md governs
the design. This phase invests heavily.

**What Kea's type system gives us that others don't:**

Row diffs. When a record row or effect row doesn't match, we have
structural information about what's missing and what's extra.
This unlocks error messages that are genuinely better:

**Record row errors — structural diff:**
```
error[E0042]: record missing required field

  12 │  let p = make_point(config)
     │                     ^^^^^^
     │  this record has fields: { name: String, x: Float }
     │  but `make_point` requires: { x: Float, y: Float }
     │
     │  missing: y (Float)
     │  extra:   name (String)
     │
     │  help: add field `y` to the record
```

**Effect row errors — capability diff:**
```
error[E0043]: unhandled effect

   8 │  fn process(data: String) -> Result Data ParseError
     │                            ^^
     │  this function is declared pure (no effects)
     │  but the body performs these effects:
     │
     │    IO       ← File.read on line 12
     │    Fail E   ← Toml.parse on line 14
     │
     │  help: either add effects to the signature:
     │    fn process(data: String) -[IO, Fail ParseError]> Data
     │  or handle them in the body:
     │    let content = catch File.read(path)
```

**Effect provenance — trace where each effect comes from:**
```
error[E0043]: unhandled effect `Net`

  15 │  fn fetch_config() -[IO]> Config
     │                     ^^^^
     │  declared effects: [IO]
     │  but body also requires: [Net]
     │
     │  Net enters the effect row via:
     │    line 16: Http.get(url)          ← performs Net
     │    Http.get is defined at http.kea:42
     │
     │  help: add Net to the effect signature:
     │    fn fetch_config() -[IO, Net]> Config
```

**Handler scope errors — explain what's covered:**
```
error[E0044]: effect handled but not performed

   8 │  handle pure_function()
   9 │    Log.log(msg) -> resume(())
     │    ^^^
     │  this handler covers `Log`, but `pure_function`
     │  doesn't perform `Log` — the handler is unnecessary
     │
     │  help: remove the Log handler, or check if you meant
     │  to call a different function
```

**Fail/catch type errors — explain the duality:**
```
error[E0045]: catch type mismatch

  12 │  let result: Result String Int = catch read_file(path)
     │              ^^^^^^^^^^^^^^^^^
     │  catch converts Fail to Result, but:
     │    read_file fails with: IoError
     │    you expected:         Int
     │
     │  help: either change the type annotation:
     │    let result: Result String IoError = catch read_file(path)
     │  or convert the error:
     │    let result: Result String Int = catch read_file(path).map_err(|e| e.code)
```

Key principles (from PEDAGOGY.md):
- Every error has a stable code (E0001, E0002, ...)
- Never expose type variables, row algebra, unification internals
- Always show provenance: where did this type/effect come from?
- Always suggest a fix with concrete code
- Effect errors explain in capability terms ("accesses the file system")
  not theory terms ("IO effect in the effect row")

Adapt rill-diag's diagnostic patterns. Rill has good error
infrastructure — extend it for Kea's novel type features.

## Testing

- Deriving: generated impls are correct, derive on enum works
- Stdlib: comprehensive tests for Map, Set, String, IO, JSON
- Error messages: **snapshot tests for every error category**
  (this is load-bearing — error messages are a feature, regressions
  are bugs)
- Effect provenance: test that error messages trace effects back
  to the originating call site, not just "effect X is unhandled"

## Definition of Done

- @derive works for Show, Eq, Ord, Encode, Decode
- Stdlib sufficient for compiler self-hosting
- Error messages are human-readable for all type features
- Row diff errors show structural missing/extra for both records
  and effects
- Effect errors include provenance (which call introduced each effect)
- **Diagnostics gate:** snapshot test coverage for every error category
  (record row mismatch, effect row mismatch, effect provenance,
  handler scope, Fail/catch, kind mismatch, ambiguous dispatch).
  Each error code has at least one snapshot test. Stable codes
  assigned (E0001-E00XX).
- `mise run check` passes

## Open Questions

- Which traits should be derivable in v0? (Proposal: Show, Eq,
  Ord, Encode, Decode. Everything else requires manual implementation.)
- Should Map/Set use HAMT from the start or a simpler tree?
  (Proposal: HAMT. It's the specified representation in
  KERNEL §1.2, and there are good Rust HAMT implementations
  to reference.)
- How much error message polish is enough for v1? (Proposal:
  every error must have a clear explanation and at least one
  suggestion. Fancy formatting and color can come later.)
- Effect provenance tracking: should the constraint system carry
  a provenance chain from day one, or is it a later optimisation?
  (Proposal: day one. Retrofitting provenance into the constraint
  system is much harder than building it in. This is the same
  argument as IO decomposition.)
