# Brief: Error Message Quality

**Status:** ready
**Priority:** v1
**Depends on:** 0g-advanced-types (needs full type system for all error categories)
**Blocks:** *(nothing — runs in parallel, not on critical path)*
**Also read before implementing:**
- [effects-platform-vision](../design/effects-platform-vision.md) — effect provenance in diagnostics
- [testing](testing.md) — snapshot test infrastructure for error messages
- [tooling-dx](../design/tooling-dx.md) — `kea doc` must be effect-aware

## Motivation

KERNEL ethos: "error messages are a feature." PEDAGOGY.md governs
the design. This phase invests heavily in diagnostic quality.

Kea has something no other language has for error reporting: **row diffs**.
When a type doesn't match, we know *structurally* what's missing and
what's extra. When an effect row is too weak, we know exactly which
capability is unhandled. This makes errors that explain problems in
terms users understand, not type theory they don't.

**This is no longer on the critical path to self-hosting.** @derive
moved to 0g. Stdlib is incremental (see stdlib-bootstrap brief).
This brief is pure error message investment — important for the
language's success but not blocking Phase 1.

## What transfers from Rill

**rill-diag** (341 LOC, already cannibalised in 0a):
- Diagnostic infrastructure extends for new error categories
- Span-based error reporting patterns transfer directly

## Implementation Plan

### Row-diff error messages

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

### Effect provenance

Trace where each effect comes from:
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

### Stable error codes

Assign stable codes (E0001-E00XX) to all error categories. Each
error code gets at least one snapshot test.

### Handler scope and Fail/catch errors

```
error[E0044]: effect handled but not performed

   8 │  handle pure_function()
   9 │    Log.log(msg) -> resume(())
     │    ^^^
     │  this handler covers `Log`, but `pure_function`
     │  doesn't perform `Log` — the handler is unnecessary
```

```
error[E0045]: catch type mismatch

  12 │  let result: Result String Int = catch read_file(path)
     │              ^^^^^^^^^^^^^^^^^
     │  catch converts Fail to Result, but:
     │    read_file fails with: IoError
     │    you expected:         Int
```

## Key Principles (from PEDAGOGY.md)

- Never expose type variables, row algebra, unification internals
- Always show provenance: where did this type/effect come from?
- Always suggest a fix with concrete code
- Effect errors explain in capability terms ("accesses the file system")
  not theory terms ("IO effect in the effect row")

## Testing

**Snapshot tests for every error category.** Error messages are a
feature — regressions are bugs.

- Record row mismatch (missing/extra fields)
- Effect row mismatch (unhandled/unnecessary effects)
- Effect provenance (trace to originating call site)
- Handler scope (unused handler, wrong effect)
- Fail/catch type mismatch
- Kind mismatch
- Ambiguous dispatch

## Definition of Done

- Row diff errors show structural missing/extra for both records
  and effects
- Effect errors include provenance (which call introduced each effect)
- Stable error codes assigned (E0001-E00XX)
- Snapshot test coverage for every error category
- `mise run check-full` passes
