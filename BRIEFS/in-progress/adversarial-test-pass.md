# Brief: Adversarial Test Pass (0a–0e)

**Status:** active
**Priority:** v1-critical
**Depends on:** 0e (all phases under test must be implemented)
**Blocks:** nothing directly, but de-risks everything downstream

## Motivation

Phases 0a–0e were built at pace. The happy paths work and have
regression coverage. But adversarial inputs — malformed syntax,
type system edge cases, effect scoping violations, handler
misuse — are underrepresented. These are exactly the inputs real
users will produce, and exactly the inputs that expose unsound
codegen, panics in the compiler, or misleading error messages.

This brief is a focused test-writing effort. No implementation
changes unless a test reveals a bug (then fix it and add the
regression test).

## Approach

Write `.kea` test files and Rust unit tests. Each test targets a
specific sad path. Tests should be snapshot-tested where the output
is an error message (verify the message is helpful, not just that
it errors). Tests that should compile-and-run verify the output.

Organise by phase. Within each phase, organise by attack surface.

## Phase 0a: Syntax

### Indentation edge cases
- Mixed tabs and spaces in the same block
- Trailing whitespace after dedent
- Empty block body (e.g. `fn foo() -> Int` with nothing indented)
- Zero-width or unusual Unicode in identifiers
- Block nesting 10+ levels deep
- Expression that spans 5+ continuation lines
- Indentation after blank lines (does the layout engine recover?)
- CRLF vs LF line endings

### Malformed inputs
- Unclosed string literal (no terminating `"`)
- Unterminated string interpolation `"hello {`
- Nested interpolation `"hello {"world {x}"}"`
- String with only escape sequences `"\n\t\\"`
- Unexpected EOF in every position: mid-expression, mid-type
  annotation, mid-pattern, mid-handler clause
- Garbage after a valid top-level declaration
- Empty file
- File with only comments
- File with only whitespace

### Parser recovery
- Error in first declaration — does the parser find the second?
- Two consecutive syntax errors — are both reported?
- Error inside a `case` arm — does parsing continue for later arms?
- Mismatched parens/brackets at various nesting depths

### Keywords as identifiers
- Using `fn`, `let`, `case`, `handle`, `resume`, `fail`, `catch`,
  `effect`, `trait`, `enum`, `struct`, `with`, `for`, `while`,
  `true`, `false`, `not`, `and`, `or` as variable names
- Using keywords in field names, type names, module names

## Phase 0b: Type System

### Unification edge cases
- Infinite type: `let f = f` or `fn f(x) -> f(f(x))`
- Conflicting field types in record unification
- Row variable escaping its scope
- Deeply nested generic types (5+ levels of `Option Option Option ...`)
- Type annotation contradicts inferred type

### Trait coherence
- Duplicate `impl Show for Int` — should error
- Orphan impl: impl a foreign trait for a foreign type
- Ambiguous method: two traits with same method name, both in scope
- Trait method with wrong number of parameters
- Trait method with wrong return type
- Missing required methods in impl block (no default)
- Extra methods in impl block (not in trait)

### Error message quality
- Do unification errors ever show `?t42` or similar internal variables?
- Record field mismatch: does the error say which field?
- Function arity mismatch: does it say expected vs got?
- Type mismatch in deeply nested expression: does it point to the
  right span?

### Edge cases
- Mutually recursive types (struct ↔ enum) — recently fixed, stress test
- Type alias cycles: `type A = B; type B = A`
- Type alias to nonexistent type
- Generic function instantiated with wrong number of type args
- Unused type parameters (should this warn?)
- Shadowing a type name with a variable name

## Phase 0c: Effect Declarations and Typing

### Handler scoping
- Effect used outside any handler — should error with clear message
- Nested handlers for the same effect — inner should shadow outer
- Handler that handles an effect not in the body's effect row
- Handler with no clauses (empty handler block)
- Effect operation called with wrong number/type of arguments

### Resume linearity
- `resume` called twice in same handler clause — must error
- `resume` called in both branches of an `if` — must error (or is
  this okay? at-most-once means exactly one path resumes)
- `resume` not called at all (zero-resume) — only valid for
  Fail-like effects. Should warn or error for others?
- `resume` called outside a handler clause — must error
- `resume` used as a value (passed to a function, stored in a let)

### Effect row interactions
- Function with `-[IO, IO]>` — duplicate effect in row
- Function with `-[Fail String, Fail Int]>` — same effect,
  different type params
- Polymorphic effect tail: `fn f(g: () -[e]> Int) -[IO, e]> Int`
  — does `e` unify correctly?
- Handler removes one effect, leaves others — is the result row
  correct?
- Chaining functions with different effect rows — do they compose?

### Fail / catch / ? interactions
- `catch` with no `fail` in body — should work (catch is a no-op)
- `?` on a non-Fail expression — should error
- `fail` with wrong type for enclosing `catch` — type mismatch
- Nested `catch` — inner catch handles inner fail
- `fail` inside a handler clause — which Fail does it target?

## Phase 0d: Codegen

### Pattern matching
- Non-exhaustive `case` — missing a variant
- Overlapping patterns — first match wins, no warning needed but
  verify semantics
- Nested pattern matching: `case x` where x is `Some(Some(y))`
- Wildcard in various positions
- Pattern match on unit `()`
- Pattern match on boolean with only `true` arm

### Closure correctness
- Closure capturing a variable that's used after the closure
- Closure capturing a variable from 3+ scopes up
- Recursive closure (closure that calls itself via a let binding)
- Closure returned from a function — does the captured env survive?
- Multiple closures capturing the same variable

### RC edge cases
- Deeply nested structure (tree 100 levels deep) — does drop work
  without stack overflow?
- Functional update chain: `x~{a: 1}~{b: 2}~{c: 3}` — allocation count
- Large enum variant — does layout work correctly?
- Zero-field struct — does it allocate?

### Arithmetic / overflow
- Integer overflow (max int + 1)
- Division by zero
- Modulo by zero
- Negative modulo

## Phase 0e: Runtime Effects

### Handler nesting
- 10+ nested handlers — does it work?
- Same effect handled at 3 different nesting levels — correct
  dispatch?
- Handler inside a handler clause (handler in the resume path)
- Removing a handler and re-adding it at a different level

### Fail + other effects
- `fail` inside a `State` handler — state is rolled back? Or not?
  (Kea doesn't have transactional rollback — verify)
- `fail` inside a handler's `then` clause — propagates to outer?
- `catch` wrapping a handler — handler result is the catch result
- `?` inside a handler clause body

### Tail-resumptive classification
- Handler clause where resume is in tail position — should be
  classified as tail-resumptive
- Handler clause where resume is NOT in tail position (e.g.
  `let x = resume(v); x + 1`) — not tail-resumptive
- Handler clause that branches: resume in one branch, not the other
- Handler clause with resume inside a closure — not tail-resumptive

### State effect stress
- State with large state value (deeply nested struct)
- State.put followed immediately by State.get — round-trips?
- Multiple State effects with different type params in same scope

### IO correctness
- IO.stdout with empty string
- IO.stdout with very long string (10KB+)
- IO.read_file on nonexistent file — should fail cleanly, not panic

## Wicked Problems

These are cross-cutting stress tests that exercise multiple systems
simultaneously. They're designed to surface unsoundness, not just
missing error messages. Each one should either work correctly or
produce a clear, non-panicking error.

### Effect re-entrancy
- Handler for `Fail` that resumes with a value which itself
  triggers `Fail` — does the inner fail get caught by the same
  handler or propagate outward?
- Handler that performs an IO operation inside a resume path —
  does the IO effect resolve correctly through the handler stack?
- `State.put` inside a `State` handler clause — which State
  is being modified?

### Cross-boundary recursion
- Mutually recursive functions where one is effectful (`-[IO]>`)
  and the other is pure (`->`), calling each other. Does the
  effect row narrow correctly at each call site?
- Recursive function that installs a handler on each recursive
  call — handler depth grows with recursion depth. Stack behavior?
- Tail-recursive function inside a handler — does the tail call
  optimisation still fire, or does the handler frame prevent it?

### Handler + pattern matching interaction
- Pattern match on a value returned from `resume` — does the
  scrutinee's memory survive the handler continuation?
- Handler clause that pattern-matches its operation argument,
  then resumes conditionally — exhaustiveness checking across
  the handler/resume boundary
- `case` expression as the body of a handler's `then` clause

### Closure + handler interaction
- Closure that captures a variable bound inside a handler clause
  — does it outlive the handler scope?
- Closure created inside a handler body, returned from the handler,
  called after the handler exits — does it still work?
- Closure passed as an argument to `resume` — the closure captures
  variables from the handler clause scope

### Polymorphic effect stress
- Effect row variable that unifies through 3+ levels of generic
  function calls: `f` calls `g` calls `h`, each adding an effect
- Function that takes a callback with a polymorphic effect row,
  calls it inside a handler that partially satisfies the row
- Generic function where the effect row depends on a type parameter
  (e.g. `fn f(x: A) -[Fail A]> ...` — effect parameterised by
  the value type)

### Resource lifecycle
- `with conn <- Db.with_connection(config)` where the body fails
  — does cleanup run? (Once `with` is implemented)
- Handler that allocates in its clause, resumes, and the resumed
  code discards the result — is the allocation freed?
- Functional update inside a handler clause: `state~{field: resume(v)}`
  — does the update happen before or after the resume?

### Pathological inputs
- 1000-line `case` expression with 500 variants
- Function with 50 parameters
- Effect row with 20 effects
- 100 nested `let` bindings
- Deeply nested type: `Option Option Option ... Option Int` (20 levels)
- Program with 100 top-level functions, all mutually recursive
- String interpolation with 50 interpolated expressions

### Soundness canaries
- Construct a value of type `A`, try to use it as type `B` through
  any pathway (handler resumption, polymorphic instantiation,
  pattern match) — the type system must reject every attempt
- Effect that declares operation returning `A`, handler clause that
  resumes with `B` — must be a type error
- Construct a `Unique T`, pass it through a handler boundary, use
  it on both sides — must be rejected by move checker

## Process

This is a parallelisable brief. Multiple agents can work on
different phases simultaneously. Each phase section is independent.

For each test:
1. Write the `.kea` test file or Rust test
2. Run it — verify it produces the expected output/error
3. If it panics or produces a wrong/misleading result, fix the bug
4. Add the test to the regression suite
5. If the error message is bad, improve it

Snapshot test error messages where possible — error message quality
is a feature.

## Definition of Done

- [ ] Every bullet point above has at least one test
- [ ] No compiler panics on any adversarial input (errors are fine,
      panics are not)
- [ ] Error messages for common mistakes are helpful (point to the
      right span, suggest a fix where possible)
- [ ] All tests pass in CI (`mise run check-full`)
- [ ] Any bugs found are fixed with regression tests

## Progress

- 2026-03-01 04:26: Picked up brief, moved to `in-progress/`, and aligned INDEX status tracking (active + done updates).
- 2026-03-01 04:30: Landed first adversarial tranche in CLI integration tests: malformed interpolation (`{}` and unterminated `{`), Show-obligation diagnostic guard for interpolation, and resume misuse diagnostics (outside clause, multiple resumes, lambda capture). Also tightened parser diagnostics so empty interpolation reports `expected expression in string interpolation` instead of generic `expected expression`.
- 2026-03-01 10:31: Landed second adversarial tranche in CLI integration tests: resume-in-loop rejection, resume value type-mismatch diagnostics (`Int` vs `String`), and effect operation call arity diagnostics (`too many arguments: expected 0, got 1`). Verified with `mise run check` and `PKG=kea mise run test-pkg` (224/224 pass).
- 2026-03-01 10:34: Landed parser-recovery and malformed-input tranche: added parser unit coverage proving top-level recovery to later valid declarations after multiple invalid lines, plus CLI adversarial tests for unexpected EOF mid-expression and multi-diagnostic surfacing from malformed function bodies. Verified with `mise run check`, `PKG=kea-syntax mise run test-pkg` (393/393), and `PKG=kea mise run test-pkg` (226/226).
- 2026-03-01 10:35: Landed handler-scoping tranche in CLI integration tests: parser rejection for `handle` with no operation clauses and execution-path coverage that mismatched handler targets are no-ops preserving body effects. Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (228/228 pass).
- 2026-03-01 10:42: Landed syntax-edge tranche in CLI integration tests: CRLF line-ending acceptance, tab-indentation rejection (`tabs are not allowed in indentation`), and keyword-as-binding-name rejection (`expected pattern`). Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (231/231 pass).
- 2026-03-01 10:49: Landed rill-but-not-kea syntax sad-path tranche in CLI integration tests: `|>` rejection, `::` namespace rejection, legacy `#[derive(...)]` rejection, and legacy expression-block rejection for `frame/sql/html/markdown` with parser-level diagnostics asserted. Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (240/240 pass).
- 2026-03-01 10:57: Landed trait-coherence follow-up tranche: compiler now validates impl method sets at registration (`missing`/`extra` method diagnostics) and CLI adversarial tests cover both error paths (`impl ... is missing method(s): \`dec\`` and `has extra method(s) not in trait: \`dec\``). Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (242/242 pass).
- 2026-03-01 11:13: Landed trait-signature compatibility tranche in type checking (`add_impl_methods`): impl method signatures are now validated against instantiated trait method signatures (catching unused impl mismatches). Added CLI adversarial tests for return-type mismatch, parameter-type mismatch, and arity mismatch on impl methods. Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (245/245 pass).
- 2026-03-01 11:17: Landed closure/RC + handler/closure tranche in CLI integration tests: capture+post-use of heap values across closures, high-volume `Log.with_collected_logs` (200 events), and handler-returned closures capturing effect-provided values. Added two pinned sad-path regressions for current compiled-lowering gaps: nested lambda returning lambda in local bindings (`non-unit function returned without value`) and handler resume with closure for effect operations returning function values (`missing handler operation plan for effect \`Factory\``). Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (250/250 pass).
- 2026-03-01 11:20: Landed additional rill-not-kea syntax diagnostics tranche in CLI integration tests: `&&` rejection (`use 'and'`), `!` rejection (`use 'not'`), `nil` rejection (`use \`None\``), bare lambda rejection (`x -> ...`), and parenthesized lambda rejection (`(x) -> ...`). Re-verified with `mise run check` and `PKG=kea mise run test-pkg` (255/255 pass).
- 2026-03-01 11:23: Upgraded backend-originating diagnostics for the two pinned 0d/0e gaps to be user-facing: unsupported function-valued effect operations in compiled handler lowering now report "`Effect.Op` is not yet supported in compiled handler lowering", and missing non-Unit return values in lowered bodies now report that the shape is not yet supported in compiled lowering. Updated CLI adversarial assertions accordingly. Re-verified with `mise run check`, `PKG=kea mise run test-pkg` (255/255), `PKG=kea-mir mise run test-pkg` (76/76), and `PKG=kea-codegen mise run test-pkg` (71/71). (`mise run test-changed` still exits non-zero on `kea-bench` because it has no tests.)
- 2026-03-01 11:38: Closed the two pinned 0d/0e compiled-lowering gaps in implementation: MIR handler lowering now supports callback-based lowering for function-valued effect operations (including resume with closure), and lambda lowering now synthesizes nested function return types so local nested lambda-returning-lambda paths execute end-to-end. Converted both pinned tests to success-path execution assertions (`exit_code == 42`). Re-verified with `mise run check`, targeted `cargo test -p kea` for both restored tests, `PKG=kea-mir mise run test-pkg` (76/76), `PKG=kea-codegen mise run test-pkg` (71/71), and `PKG=kea mise run test-pkg` (255/255).
- 2026-03-01 11:40: Landed additional effect-op call adversarial coverage in CLI integration tests: missing required argument diagnostics (`missing required argument \`x\``) and wrong argument type diagnostics (`Int` vs `String`) for handled effect operations. Re-verified with `mise run check` and focused `cargo test -p kea effect_operation_call_with_ -- --nocapture` (3/3 pass).
- 2026-03-01 11:42: Landed mixed syntax/runtime adversarial additions: lexer-level unterminated string-literal rejection (`unterminated string literal`) and a same-effect three-level handler dispatch stress test proving nearest-scope shadowing semantics (`Reader` across inner/middle/outer handlers, exit code 222). Re-verified with `mise run check` plus focused `cargo test -p kea` runs for both new cases.
- 2026-03-01 12:03: Landed Fail/catch interaction tranche: nested catch behavior (inner catch handles inner fail, outer catch still observes later fail), catch-wrapping-handler execution path, and catch error-type annotation mismatch diagnostics (`type annotation mismatch: declared \`String\`, but value has type \`Int\``). Re-verified with `mise run check` and focused `cargo test -p kea catch_ -- --nocapture` (8/8 pass).
- 2026-03-01 12:05: Landed `?` misuse adversarial coverage: reject try-sugar on non-`Result` operands and reject `Result` error-type mismatches against ambient `Fail` effect (`Int` vs `String`), alongside existing success-path try tests. Re-verified with `mise run check` and focused `cargo test -p kea try_sugar -- --nocapture` (4/4 pass).
- 2026-03-01 12:05: Added pinned 0d/0e regression for handler-then + outer-catch lowering gap: `then -> fail ...` under outer `catch` currently hits backend unsupported-shape diagnostic (`non-Unit return type ... not yet supported in compiled lowering`). Locked as explicit sad-path test to prevent panic/regression until lowering support lands.
- 2026-03-01 12:06: Landed malformed-input coverage for empty/blank/comment-only files via CLI integration tests, asserting stable missing-entrypoint diagnostics for sources with no declarations/main. Re-verified with `mise run check` and focused `cargo test -p kea file_without_main -- --nocapture` (3/3 pass).
- 2026-03-01 12:07: Landed pathological-input coverage for deep binding and high-arity function shapes that currently execute safely in compiled mode (30-parameter function, 100 nested `let` bindings). Re-verified with `mise run check` plus focused `cargo test -p kea` runs for both new cases.
- 2026-03-01 12:07: Identified a new hard-failure delta during pathological testing: a 50-parameter function shape triggers a stack overflow (process abort) in compiled execution. Kept stable coverage at 30 parameters so CI remains non-aborting; 50-parameter overflow is now a documented follow-up bug to fix before claiming full pathological-input hardening.
- 2026-03-01 12:08: Landed handler callback-lowering tranche: validated multi-argument callback clause lowering end-to-end (`Math.add(a, b) -> resume ...`) and added an explicit sad-path regression for unsupported non-variable callback argument patterns (`requires simple variable argument patterns for callback lowering`). Re-verified with `mise run check` and focused `cargo test -p kea` runs for both new cases.
- 2026-03-01 12:26: Landed unexpected-EOF syntax coverage beyond mid-expression: missing return type after `->`, incomplete handler clause body after `->`, and incomplete `case` arm body after `->`. Re-verified with `mise run check` and focused `cargo test -p kea unexpected_eof_mid_ -- --nocapture` (4/4 pass).
- 2026-03-01 12:27: Landed malformed-input parser tranche: garbage trailing token after a valid top-level declaration (`unexpected character`) and mismatched parenthesis in expression parsing. Re-verified with `mise run check` plus focused `cargo test -p kea` runs for both new cases.
- 2026-03-01 12:28: Landed runtime IO stress coverage from the 0e adversarial list: `IO.stdout` with empty string and `IO.stdout` with very long payload (~10KB) both execute cleanly with exit code `0` (no panic/regression). Re-verified with `mise run check` and focused `cargo test -p kea` runs for both new cases.
- 2026-03-01 12:29: Landed handler-nesting sad-path coverage for clause classification: a handler clause containing a nested `handle` before `resume` now has explicit adversarial assertion for current compiled-lowering behavior (`must be tail-resumptive (\`resume ...\`) for compiled lowering`), ensuring this shape remains a clear diagnostic rather than panic/regression.
- 2026-03-01 12:40: Closed both pinned deltas. Implemented non-call `catch` lowering via synthesized thunk/call path in MIR, fixed fail-result ABI signature selection for value callees in codegen, and restored `handle ... then fail ...` wrapped by outer `catch` to success-path execution (`exit_code == 9`). Also fixed pathological 50-parameter overflow by moving compile/typecheck entrypoints onto a dedicated larger-stack worker thread and restored 50-parameter execution and compile-project regression coverage. Re-verified with `mise run check`, targeted `cargo test -p kea` for both regressions, `PKG=kea-mir mise run test-pkg` (76/76), `PKG=kea-codegen mise run test-pkg` (71/71), and `PKG=kea mise run test-pkg` (281/281).
- 2026-03-01 12:49: Landed 0b diagnostic/coherence expansion tranche in CLI integration tests: cyclic alias rejection, type-annotation arity mismatch, named-record field mismatch diagnostics with field context, row-polymorphic missing-field rejection, regular function call arity mismatch (`too many arguments`), and a canary asserting inference diagnostics do not leak internal solver variables (`?t`/`TypeVarId`). Re-verified with `mise run check`, focused `cargo test -p kea` for brittle assertions, and `PKG=kea mise run test-pkg` (287/287). Note: unbound alias targets currently behave as implicit type variables when used in annotations; explicit unknown-alias rejection remains a potential follow-up semantics decision.
- 2026-03-01 12:52: Landed 0e runtime stress tranche in CLI integration tests: deep same-effect handler nesting (10 Reader layers via chained handler/call structure, exit code `66`) and a `Fail`+`State` semantic canary proving no transactional rollback (`State.put(5)` before locally caught `Fail` remains observable, exit code `5`). Re-verified with `mise run check`, focused `cargo test -p kea` runs for both new cases, and `PKG=kea mise run test-pkg` (289/289). While drafting this, direct `catch fail 7` in that shape exposed an existing JIT symbol-resolution edge (`can't resolve symbol Fail.fail`), so the landed rollback canary uses `catch boom()`; direct-fail-in-catch lowering remains a separate follow-up.
- 2026-03-01 12:54: Landed 0c effect-row adversarial coverage for duplicate incompatible `Fail` entries (`-[Fail Int, Fail String]>`), asserting the effect-contract diagnostic remains explicit and user-facing (`multiple incompatible \`Fail\` entries`). Re-verified with `mise run check`, focused `cargo test -p kea duplicate_fail_effect_entries -- --nocapture`, and `PKG=kea mise run test-pkg` (290/290).
- **Next:** Continue 0d/0e adversarial expansion across remaining unchecked bullets, with emphasis on deeper handler/closure interaction and pathological scale cases.
