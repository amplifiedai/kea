# Brief: Phase 1d — Compiler Improvements in Kea

**Status:** ready
**Priority:** v1
**Depends on:** phase-1bc (compiler is self-hosted)
**Blocks:** Phase 2 (native backend benefits from these foundations)
**Also read:**
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — the architectural thesis
- [Self-hosting perf](../design/self-hosting-perf.md) — performance targets
- [0h Error message quality](../todo/0h-stdlib-errors.md) — error message work

## Motivation

The self-hosted compiler is correct (1b/1c proved that). Now make it
*good*. The compiler is a Kea program — use the language's own features
to make it fast, incremental, and helpful.

These improvements are independently valuable and independently
deliverable. Each one can ship as its own commit without blocking
the others. The order below is by impact.

## 1. Incremental Compilation via Query Effect

**Impact:** sub-100ms rebuilds on single-file edits (from seconds).

Salsa-style demand-driven incremental computation, expressed as
an effect:

```kea
effect Query
  fn input(key: FileId) -> Source
  fn memo(key: QueryKey) -> QueryResult

fn typecheck(file: FileId) -[Query, Diagnose]> Types
  let src = Query.input(file)
  let ast = Query.memo(ParseQuery(file))
  let types = Query.memo(InferQuery(ast))
  types
```

Content-addressed hashing on immutable IR nodes gives early cutoff:
if a whitespace-only edit doesn't change the AST hash, all
downstream passes skip. rust-analyzer's Salsa does this with manual
annotations. In Kea, the `Query` effect *is* the annotation.

### Implementation

- Define the `Query` effect in the compiler's internal stdlib
- `Query.input` reads a source file and tracks it as a dependency
- `Query.memo` checks a content-addressed cache before computing
- The handler stores `Map QueryKey (Hash, QueryResult)`
- On rebuild: invalidate inputs that changed, recompute only
  affected queries
- Early cutoff: if recomputed query produces the same hash as
  cached, don't invalidate downstream

### Validation

- Benchmark: compile a 10K-line project, edit one file, measure
  rebuild time
- Target: sub-100ms for single-file edits, sub-1s for cross-module
  changes
- Correctness: incremental and clean builds must produce identical
  output

## 2. Parallel Compilation

**Impact:** 2-4x speedup on multi-core machines for large projects.

Pure passes parallelise automatically:

```kea
-- Phase 1: parse all files in parallel
let asts = Par.map(files, |path|
  parse(read_file(path))
)

-- Phase 3: type check modules in dependency order
-- modules in the same topo level compile in parallel
let typed = order.levels.flat_map(|level|
  Par.map(level, |module| infer(module))
)

-- Phase 5: optimise all functions (PURE)
let optimized = Par.map(mir.functions, optimize)

-- Phase 6: codegen all functions in parallel
let code = Par.map(optimized, codegen_func)
```

The effect system proves which passes are pure. Unique types prove
the data doesn't alias. `Par.map` is type-checked safe.

### Implementation

- Use existing `Spawn` effect for task creation
- Parse phase: embarrassingly parallel (per file)
- Type check: parallel per topological level (modules in the same
  level have no dependencies on each other)
- Optimise: embarrassingly parallel per function (passes are pure)
- Codegen: embarrassingly parallel per function

### Validation

- Benchmark: compile a multi-module project on 1, 2, 4, 8 cores
- Target: 2-4x speedup on 4+ cores
- Correctness: parallel and sequential compilation produce identical
  output

## 3. Arena-Scoped Phases

**Impact:** 2-5x allocation throughput for parse/lower phases.

```kea
fn compile_file(src: String) -> Bytes
  with Arena.scoped(4096)
    let ast = parse(src)
    let hir = lower(ast)
    -- arena freed here, all AST/HIR nodes gone at once
  let mir = lower_to_mir(hir)
  let optimized = optimize(mir)
  codegen(optimized)
```

Bump allocation for phases that produce temporary IR. Parse creates
hundreds of thousands of AST nodes, all discarded after lowering.
Arena gives bulk deallocation + cache locality.

### Implementation

- `Alloc` effect from 0f/0e, with arena handler
- Wrap parse + HIR lowering in arena scope
- Unique T inside arena = zero RC + bump alloc (strongest path)
- Deep-copy at arena boundary for values that escape

### Validation

- Benchmark: measure allocation throughput and cache hit rate
  with and without arenas
- Target: 2-5x improvement on parse-heavy workloads
- Correctness: values that escape arena are correctly deep-copied

## 4. Error Message Investment

**Impact:** user experience — error messages become a feature.

With the compiler in Kea, diagnostics use effects natively:

```kea
effect Diagnose
  fn error(msg: String, span: Span) -> Unit
  fn warning(msg: String, span: Span) -> Unit
  fn note(msg: String, span: Span) -> Unit
  fn help(suggestion: String, span: Span) -> Unit
```

### Specific improvements

**Row-diff errors:** show what fields/effects are missing vs present.

```
error[E0301]: Record type mismatch
  ┌─ src/main.kea:12:5
  │
  │   let user: { name: String, age: Int, email: String }
  │   process(user)
  │
  = expected: { name: String, age: Int, role: String }
  = got:      { name: String, age: Int, email: String }
  = missing field: `role: String`
  = extra field:   `email: String`
```

**Effect provenance:** trace where an effect requirement came from.

```
error[E0401]: Unhandled effect `Log`
  ┌─ src/main.kea:8:3
  │
  │   process_data(input)
  │   ^^^^^^^^^^^^^^^ requires `Log` effect
  │
  ┌─ src/lib.kea:15:1
  │
  │ fn process_data(x: Data) -[Log, Fail ProcessError]> Result
  │                            ^^^ `Log` declared here
  │
  = help: add a `Log` handler: `with Log.to_stdout`
```

**Stable error codes:** E0001-style, documented, searchable. Every
error message gets a code. `kea explain E0301` prints the full
explanation with examples.

**Snapshot tests:** every error message format is snapshot-tested.
Regressions in error quality are caught by CI.

### Implementation

- Define error code registry (E0001-E9999, categorised)
- Implement row-diff display for record and effect row mismatches
- Add effect provenance tracking to type inference (trace where
  effects originate)
- Write `kea explain <code>` subcommand
- Snapshot-test every error message format
- Quality audit: review every diagnostic, improve wording

### Validation

- Every error code has a snapshot test
- `kea explain <code>` works for every error code
- User study: show error messages to someone unfamiliar with Kea,
  check if they can diagnose the issue from the message alone

## Definition of Done

- [ ] Incremental: sub-100ms single-file rebuilds on 10K-line project
- [ ] Incremental: clean and incremental builds produce identical output
- [ ] Parallel: 2-4x speedup on 4+ cores (measured)
- [ ] Parallel: sequential and parallel produce identical output
- [ ] Arenas: 2-5x allocation throughput on parse phase (measured)
- [ ] Errors: stable error codes for all diagnostics
- [ ] Errors: row-diff display for record and effect mismatches
- [ ] Errors: effect provenance in all effect-related errors
- [ ] Errors: `kea explain <code>` for every error code
- [ ] Errors: every error format snapshot-tested

## Risks

**Query effect complexity.** Incremental compilation is hard —
Salsa took years to stabilise. Start simple: file-level
granularity, not expression-level. Finer granularity can come later.

**Parallel correctness.** Data races in the compilation pipeline
would be catastrophic. The effect system prevents this *if* pass
signatures are accurate. Verify that no pass secretly mutates
shared state.

**Arena escape analysis.** Values that escape an arena scope must
be deep-copied. Missing a copy = use-after-free. The `Alloc` effect
boundary makes this explicit, but it's still a correctness risk.
Test heavily.

**Error message maintenance.** Snapshot tests for error messages
are brittle — any formatting change breaks them. Use fuzzy matching
for structure and exact matching for content. Accept that error
message tests will be the most frequently updated tests.
