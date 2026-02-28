# Agent Note: Adversarial Test Pass

Read `BRIEFS/todo/adversarial-test-pass.md` for the full brief.
This note tells you what to pick up, what to skip, and how to work.

## What's in scope NOW

**Phases 0a, 0b, 0c, 0d, 0e are all implemented and testable.**
Most of the brief can be done right now. The exceptions are listed
below under "Skip for now."

## Priority order

Work through the phases in order. Each phase builds context for
the next. Within each phase, prioritise:

1. **Things that might panic the compiler** — these are the worst
   bugs. Malformed inputs, unexpected EOF, pathological sizes.
2. **Things that might be unsound** — wrong codegen, type safety
   violations, effect leaks. The soundness canaries section.
3. **Things with bad error messages** — these aren't bugs but they
   compound into a terrible user experience.

## Skip for now

These items depend on features that aren't implemented yet:

- **`with` syntax tests** (Resource lifecycle section: `with conn <- ...`)
  — `with` keyword isn't in the lexer yet. Skip all `with`-specific
  tests. Handler tests using direct `handle` blocks ARE in scope.
- **`Unique T` soundness canary** ("Construct a Unique T, pass through
  handler boundary, use on both sides") — Unique move checking is 0f
  work in progress. The move checker exists but is still being refined.
  Write the test, mark it `// TODO(0f)` if it doesn't behave correctly.
- **`for` loop tests** — `for` requires Iterator trait (0g). Skip.
- **String interpolation with 50 expressions** (Pathological inputs)
  — string interpolation just landed. Basic adversarial tests are fine
  but don't fight fresh bugs here — focus on the stable surface.

Everything else in the brief is fair game.

## How to write tests

### Error-path tests (compiler should reject)

Write as Rust integration tests in `crates/kea/src/main_tests.rs`
following existing patterns. The key patterns:

```rust
#[test]
fn reject_resume_outside_handler() {
    let src = r#"
fn main() -> Int
  resume(42)
"#;
    let result = compile_and_check(src);
    assert!(result.is_err());
    let err = result.unwrap_err();
    // Verify the error message is helpful:
    assert!(err.contains("resume"));
    // Snapshot if you want exact message stability:
    // insta::assert_snapshot!(err);
}
```

For snapshot-tested error messages, use `insta`. Run
`cargo insta review` to approve new snapshots.

### Compile-and-run tests (program should execute correctly)

```rust
#[test]
fn nested_handlers_same_effect() {
    let src = r#"
effect Ask
  fn ask() -> Int

fn main() -> Int
  handle
    handle
      Ask.ask()
    then
      Ask.ask(n) -> resume(10)
    then result ->
      result + Ask.ask()
  then
    Ask.ask(n) -> resume(20)
  then result ->
    result
"#;
    // Inner handler returns 10, outer adds 20 = 30
    assert_eq!(compile_and_run(src), Ok(30));
}
```

### .kea file tests

For larger programs, put them in `tests/adversarial/` as `.kea`
files. Create the directory if it doesn't exist. Name files
descriptively: `handler_nesting_10_deep.kea`, `infinite_type.kea`,
`duplicate_effect_in_row.kea`.

## Key things to probe

### Compiler panics (highest priority)

The #1 goal is: **the compiler never panics on any input.** Every
malformed input should produce an error diagnostic, not a Rust
panic/unwrap failure. Test by feeding garbage and edge cases to
`kea run` and `kea check`. If it panics, that's a bug — fix it.

Specifically probe:
- Unexpected EOF everywhere (mid-expression, mid-type, mid-handler)
- Empty bodies (empty fn, empty handler, empty case, empty match arm)
- Deeply nested anything (100 lets, 500-variant case, 20 type params)
- Every keyword used as an identifier

### Effect system soundness (highest value)

The effect system is the novel core and the most likely place for
unsoundness. Probe hard:
- Can you observe an effect operation's result without a handler
  in scope? (Should be impossible)
- Can you `resume` with the wrong type? (Type checker must reject)
- Do nested handlers for the same effect dispatch correctly?
  (Inner should shadow outer)
- Does `fail` inside a handler clause propagate correctly?
- Does the effect row narrow after a handler removes an effect?

### Error message quality (user-facing impact)

For every error you trigger, ask: "Would a new Kea user understand
this message?" If the error says `unification failed: ?t42 != Int`,
that's a bug — it should say something like `expected Int, got String`.

Snapshot-test the good error messages so they don't regress.

## Validation

After each phase section:
```
mise run check
PKG=kea mise run test-pkg
```

After completing all phases:
```
mise run check-full
```

## When you find a bug

1. Write the minimal reproduction as a test
2. Fix the bug
3. Verify the fix doesn't break existing tests
4. Add a progress entry to the brief with what you found and fixed
5. Keep going — don't stop to report unless you're genuinely stuck

The goal is to emerge with a much more robust compiler and a
comprehensive regression suite. Quantity of tests matters — aim
for 5+ tests per bullet point in the brief, not just one token
test per item.
