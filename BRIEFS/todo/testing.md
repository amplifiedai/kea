# Brief: Testing

**Status:** ready
**Priority:** Phase 0d (test runner), extends through Phase 1
**Depends on:** 0d-codegen-pure (test compilation), 0c-effect-handlers (Fail, Test effect)
**Blocks:** stdlib quality, public release confidence
**Related:** [tooling-dx](tooling-dx.md) (test runner CLI), [packaging-ffi-comptime](packaging-ffi-comptime.md) (@derive Arbitrary)

## Motivation

Testing is where Kea's effect system pays for itself in daily
developer experience. Every other language treats testing as a
library concern — you pick a framework, learn its API, configure
its runner. Kea treats testing as a language concern: test blocks
are syntax, assertions are effects, isolation is handler-driven,
and parallelism is compiler-decided.

The goal is not "good testing support." The goal is that testing
in Kea is qualitatively better than testing in any other language
because the effect system gives the test runner information that
no other runner has.

## The Two Assertion Modes

### `assert` — precondition (Fail)

`assert` is not a test framework function. It's just `Fail`:

```kea
fn assert(_ cond: Bool) -[Fail AssertionError]> Unit
  if !cond
    fail AssertionError(...)
```

When an `assert` fails, the test stops. This is for preconditions
where the rest of the test is meaningless without this holding.
Standard `Fail` semantics — `catch` can recover, `?` can propagate.

### `check` — observation (Test effect)

```kea
effect Test
  fn check(_ result: Assertion) -> Unit
```

When a `check` fails, the test **continues**. The handler
accumulates the failure and resumes. This is Rill's Validated
pattern — applicative error accumulation — but implemented as an
effect handler instead of a typeclass. No `<*>` combinators, no
Applicative instance, no separate Validated type. Just an effect
operation that the handler resumes past.

```kea
test "user validation checks all fields"
  let user = { name: "", age: -1, email: "bad" }
  let result = User.validate(user)
  check result.errors.any(|e| e.field == "name")
  check result.errors.any(|e| e.field == "age")
  check result.errors.any(|e| e.field == "email")
  -- all three checks run, all three failures reported
```

This is the most common testing pain point solved: you run your
test, get one failure, fix it, run again, get the next failure,
fix it, run again. With `check`, you get all failures at once.

### Why two modes

`assert` = "if this doesn't hold, nothing else matters."
`check` = "note whether this holds; keep going."

Both are necessary. Both are effects. The runner handles both.

## Expression Capture

When a `check` or `assert` fails, the developer needs to know
**why**, not just **where**. Every other test framework solves
this with specialised assertion functions: `assertEqual(a, b)`,
`assertGreaterThan(a, b)`, `assertContains(list, item)`. Each
one has bespoke formatting for its failure message.

Kea solves this at the compiler level. In a `test` block, the
compiler rewrites assertion expressions to capture sub-expression
values:

```kea
check user.age >= 0
```

Compiles to something like:

```kea
Test.check(Assertion {
  expression: "user.age >= 0",
  passed: user.age >= 0,
  location: SourceLoc { ... },
  captures: [("user.age", show(user.age))],
})
```

The failure output:

```
FAIL: check user.age >= 0
  user.age = -5

  src/user_test.kea:42
```

This is a **compiler feature**, not comptime. It needs reliable
source spans, sub-expression capture, and integration with the
`Show` trait. Comptime extensibility comes later — the core
capture mechanism must be rock-solid in the compiler first.

### Structural diff for records

When `check x == y` fails and both sides are records, the compiler
knows the fields (row types). It can produce a field-by-field diff:

```
FAIL: check result == expected

  result vs expected:
    name  = "Alice"      "Alice"       (match)
    age   = 25           26            (mismatch)
    email = "a@b.com"    "a@b.com"     (match)

  src/order_test.kea:18
```

No custom `assertEqual` overload. No `toMatchObject`. The type
system gives you structural diff for free on any record type.

For enums, the diff shows the variant and payload. For lists,
it shows the index where they diverge. For nested structures,
it recurses.

## The Test Runner

### Test block syntax

```kea
test "descriptive name"
  -- test body
  assert precondition
  check observation_1
  check observation_2
```

Test blocks are first-class syntax. The compiler parses them,
type-checks them, and reports their effect signatures.

### Effect-driven parallelism

The compiler knows each test's effect row. This determines
parallelism strategy:

| Effect signature | Parallelism | Rationale |
|-----------------|-------------|-----------|
| `-> Unit` (pure) | Always parallel | No side effects, no contention |
| `-[Fail E]> Unit` | Always parallel | Only fails, no shared state |
| `-[Gen]> Unit` | Parallel per seed | Each run is independent |
| `-[IO]> Unit` | Partitioned | May touch filesystem/network |
| `-[Send, Spawn]> Unit` | Sequenced | Shared actor runtime |

**Conservative default:** Pure + Fail-only tests run in parallel
out of the box. Tests with IO or concurrency effects are sequenced
by default, opt-in to parallel via annotation or runner policy.

Effects tell you capability class, not shared resource contention.
Two IO tests that touch different files could safely run in
parallel — but the compiler can't know that. Start conservative,
add opt-in parallelism for IO tests with explicit partitioning
(e.g., by temp directory isolation).

### Test lifecycle

```
1. Discover all test blocks in target files
2. Type-check each test (effect row determines runner strategy)
3. Group tests by parallelism class
4. For each test:
   a. Install Test handler (check accumulation)
   b. Install catch handler (assert/Fail)
   c. Install effect handlers (IO mock, Gen, etc.)
   d. Run test body
   e. Collect Assertion results
   f. Record duration, effect metadata
5. Aggregate TestResults
6. Render (CLI human output or structured JSON)
```

### Filtering and tags

```
kea test                          -- run all tests
kea test --filter "validation"    -- substring match on test name
kea test --tag integration        -- run tagged tests
kea test --exclude-tag slow       -- exclude tagged tests
kea test src/auth/                -- run tests in directory
```

Tags are annotations on test blocks:

```kea
@tag("integration", "slow")
test "full database round trip"
  ...
```

## Property Testing

Property testing is an effect, not a library:

```kea
effect Gen
  fn int(_ range: Range Int) -> Int
  fn float(_ range: Range Float) -> Float
  fn string(_ max_length: Int) -> String
  fn bool() -> Bool
  fn one_of(_ items: List T) -> T
  fn list_of(_ gen: () -[Gen]> T, _ max_length: Int) -> List T
  fn arbitrary() -> T where T: Arbitrary
```

A property test is a test with `Gen` in its effect row:

```kea
test "sort is idempotent" -[Gen]>
  let xs = Gen.arbitrary() : List Int
  check xs.sort().sort() == xs.sort()

test "reverse reverse is identity" -[Gen]>
  let xs = Gen.arbitrary() : List Int
  check xs.reverse().reverse() == xs
```

The handler:
1. Generates values from a seed
2. Runs the test body (default: 100 iterations)
3. On failure: shrinks inputs to minimal failing case
4. Reports: failing input, shrunk input, seed, iteration count

### Determinism

**Seeds and shrink paths are first-class in the result.**

```
FAIL: test "sort is idempotent" (iteration 47, seed 0xA3F2...)
  Shrunk input: [3, 1, 3]

  check xs.sort().sort() == xs.sort()
    xs.sort().sort() = [1, 3, 3]
    xs.sort()        = [1, 3, 3]

  Replay: kea test --replay 0xA3F2...
```

`kea test --replay <seed>` reproduces any property test failure
deterministically. This is built-in from day one, not an
afterthought.

### @derive(Arbitrary)

`@derive(Arbitrary)` generates random instances for any struct
or enum:

```kea
@derive(Arbitrary)
struct User
  name: String
  age: Int
  email: String

-- Gen.arbitrary() now works for User
test "user serialization roundtrip" -[Gen]>
  let user = Gen.arbitrary() : User
  check User.decode(User.encode(user)) == Ok(user)
```

For enums, the generator picks a variant uniformly, then generates
payloads recursively. For recursive types, depth is bounded.

## Structured Results

The test runner produces structured data. The CLI renderer and
MCP consumer are handlers over the same type.

```kea
struct TestResult
  name: String
  status: TestStatus              -- Passed, Failed, Skipped
  assertions: List Assertion      -- ALL checks, passed and failed
  failure: Option AssertionError  -- from assert/Fail, if any
  duration: Duration
  effect_row: List String         -- effect signature (metadata)
  property: Option PropertyInfo   -- seed, iterations, shrink path

enum TestStatus
  Passed
  Failed
  Skipped(String)                 -- reason

struct Assertion
  expression: String
  passed: Bool
  location: SourceLoc
  captures: List (String, String)
  diff: Option Diff

struct PropertyInfo
  seed: Int
  iterations: Int
  shrunk_input: Option String     -- Show representation
```

### Output modes

**Human CLI** (default):
```
  user validation checks all fields ............ FAIL (2ms)

    FAIL: check result.errors.any(|e| e.field == "name")
      result.errors = [{ field: "age", msg: "must be positive" }]
      src/user_test.kea:5

    FAIL: check result.errors.any(|e| e.field == "email")
      result.errors = [{ field: "age", msg: "must be positive" }]
      src/user_test.kea:7

  sort is idempotent ........................... PASS (100 iterations, 45ms)
  reverse reverse is identity .................. PASS (100 iterations, 38ms)

  3 tests: 2 passed, 1 failed (85ms)
```

**Structured JSON** (for MCP/CI):
Same `TestResult` data, serialised via `Encode`. Agents can
programmatically inspect failures, captures, diffs, and property
seeds.

## Effect-Driven Test Isolation

Handler-based mocking. No mock framework, no DI container,
no monkeypatch.

```kea
test "config loader reads file"
  let mock_files = Map.from([
    ("/etc/app.toml", "port = 8080")
  ])
  let config = handle Config.load("/etc/app.toml")
    IO.read_file(path) ->
      resume mock_files.get(path).unwrap_or("")
  check config.port == 8080
```

The production code uses real IO. The test swaps the handler.
Same code, different effect interpretation. The compiler verifies
the handler matches the effect signature — you can't forget to
mock an effect your code uses.

### Snapshot testing

Snapshot assertions compare output against stored reference:

```kea
test "error message formatting"
  let err = TypeChecker.check("let x: Int = true")
  assert_snapshot err.render()
  -- compares against src/__snapshots__/error_message_formatting.snap
  -- creates snapshot on first run
  -- kea test --update-snapshots to accept changes
```

Snapshot update is a CLI flag, not an environment variable.

## What Transfers from Rill

- **Assertion collection pattern:** `eval_test_body_collect_assertions`
  continues past failures. Kea formalises this as the Test effect.
- **Test block syntax:** `testing { ... }` postfix blocks and
  standalone `TestDecl`. Kea uses `test "name"` blocks.
- **Validated type:** Applicative error accumulation. Kea replaces
  the type with the Test effect handler.
- **Tag filtering:** `--tag` / `--exclude-tag` transfers directly.
- **Property test support:** `is_property` flag and iteration count.
  Kea extends with Gen effect and seed replay.

## Decisions

- **Expression capture is a compiler feature.** Not comptime, not
  a macro. The compiler rewrites assertion expressions in test
  blocks to capture sub-expression values. This needs reliable
  source spans and Show integration. Comptime extensibility later.

- **Parallelism is conservative by default.** Pure + Fail-only
  tests parallel. IO and concurrency tests sequenced by default.
  Opt-in parallel with explicit partitioning for IO tests.

- **Seeds are persisted in results.** Every property test failure
  includes a seed for deterministic replay via `--replay`.

- **No separate test framework.** Tests are language syntax.
  Assertions are effects. The runner is `kea test`. No third-party
  test library needed for the core workflow.

- **Structured output is the primary output.** Human CLI rendering
  is a pretty-printer over `TestResult`. MCP/CI gets the same data
  as JSON. No separate "machine-readable output mode" flag — the
  structured data IS the output, rendering is a presentation choice.

## Precedents (honest accounting)

Individual pieces have prior art:
- **Expression capture:** Power Assert (Groovy, JS), Rust's
  `assert_eq!` (partial)
- **Error accumulation:** Validated (Haskell, Cats, Rill),
  soft assertions (TestNG, AssertJ)
- **Property testing:** QuickCheck (Haskell), Hypothesis (Python),
  proptest (Rust)
- **Effect-based mocking:** research papers on algebraic effects

The combination — effect-driven accumulation, compiler-level
expression capture, type-directed parallelism, handler-based
isolation, structured results — is novel. No single piece is
unprecedented; the integration is.

## Implementation Timeline

### Phase 0d (with codegen)
- `test` block parsing and compilation
- `assert` via Fail (already works from 0c)
- `Test` effect and `check` operation
- Test runner: discovery, execution, basic CLI output
- Expression capture (compiler-lowered)
- Structured `TestResult` type
- Tag filtering
- Parallel execution for pure tests

### Phase 0d+ (shortly after)
- Structural diff for records and enums
- Snapshot testing
- `--replay` for deterministic reproduction
- JSON output mode

### Phase 0h (with stdlib)
- `Gen` effect and property testing
- `@derive(Arbitrary)` for structs and enums
- Shrinking
- Seed persistence

### Phase 1
- Benchmark support (`kea test --bench`)
- Coverage instrumentation
- Test-aware LSP (run test at cursor, show inline results)

## Open Questions

- **Should `check` expressions outside test blocks be a compile
  error?** `check` in production code would accumulate silently
  with no handler — probably a bug. Proposal: `check` requires
  `Test` in the effect row, and `Test` is only handled by the
  test runner. Using `check` in non-test code is a type error
  unless you explicitly handle `Test`.

- **Should property test iteration count be configurable per test
  or only globally?** Rill allows per-test iteration count.
  Proposal: global default (100), per-test override via annotation
  `@iterations(1000)`.

- **How should `kea test` handle benchmarks?** Options: (a) built-in
  `bench "name"` blocks (like Go's `testing.B`), (b) separate
  `kea bench` command, (c) `@tag("bench")` + `--tag bench`.
  Proposal: built-in `bench` blocks with `kea test --bench` flag,
  similar to Go. Benchmarks are not run by default.

- **Should the test runner auto-inject handlers for unhandled
  effects?** If a test has `-[IO]>` but no handler installed,
  should the runner provide a default mock IO handler? Proposal:
  no. Explicit handlers only. Unhandled effects are a compile
  error (same as production code). The developer decides what
  the mock does.
