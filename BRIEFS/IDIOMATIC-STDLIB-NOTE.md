# Agent Note: Idiomatic Stdlib Pass

Read `BRIEFS/todo/idiomatic-stdlib-pass.md` for the full brief and
`docs/IDIOMS.md` for the idioms guide. This note tells you what to
do and why it matters.

## Why this matters

The stdlib is Kea's showcase. It's the first real Kea code anyone
reads. Every function signature, every doc comment, every pattern
choice teaches users how to write Kea. If the stdlib uses Result
monadic chaining, users will too. If the stdlib has sparse docs,
users won't know what good looks like.

Think of Go's stdlib, Elixir's Enum module, Rust's Iterator trait.
Those aren't just useful — they're exemplary. That's the bar.

## What to do

### 1. Fix `result.kea` FIRST

This is the most important change because it establishes the
Fail-over-Result idiom. The current `result.kea` teaches the wrong
patterns.

**Remove these functions — they encourage monadic Result chaining:**
- `map` — use `let x = res?; f(x)` instead
- `and_then` — use `let x = res?; g(x)` instead
- `map_err` — use `handle Fail.fail(e) -> fail(transform(e))`
- `unwrap` — this is literally `?`

**Keep these — they're legitimate data operations:**
- `unwrap_or` — "give me the value or a default"
- `is_ok` / `is_err` — checking without extracting
- `from_option` — type conversion

**Add a module-level doc comment explaining Result's role:**

```kea
--| Result is Fail's data representation.
--|
--| Use `-[Fail E]> T` in function signatures, not `-> Result(T, E)`.
--| Result appears when you need to *store* or *collect* outcomes,
--| not as a control flow mechanism.
--|
--| Store outcomes:
--|
--|   let results = items.map(|item| catch validate(item))
--|
--| Choose a default:
--|
--|   let config = Result.unwrap_or(catch load_config(), defaults)
--|
--| Convert back to Fail with `?`:
--|
--|   let value = some_result?
```

### 2. Audit every function signature

Go through every `.kea` file in `stdlib/`. For each function ask:
- Does it return `Result(T, E)` where `-[Fail E]> T` would be
  better? Fix it.
- Does it use `IO` as a catch-all where `Net`/`Clock`/`Rand` is
  more specific? Fix it.
- Is the subject the first parameter? (Enables UMS: `xs.map(f)`)

### 3. Doc comments — the real work

**Every public function needs a doc comment that meets this bar:**

```kea
--| Fold a list from the left, accumulating a result.
--|
--| Applies `f` to each element and the running accumulator,
--| starting from `init`. Returns the final accumulator value.
--|
--|   List.fold([1, 2, 3], 0, |acc, x| acc + x)   -- => 6
--|   List.fold([], 10, |acc, x| acc + x)           -- => 10
--|   List.fold([1, 2, 3], "", |s, x| "{s}{x}")    -- => "123"
fn fold(xs: List A, init: B, f: fn(B, A) -> B) -> B
```

**Checklist per function:**
- First line: one sentence, starts with a verb
- Explains what it does, not how (unless the how matters)
- Mentions edge cases: empty list, None, zero, negative values
- At least one example showing typical use
- At least one example showing the edge/empty/error case
- If it has effects: explains when/why it fails
- Examples use module-qualified calls (`List.fold`, not `fold`)
- Examples use `-- =>` for expected results

**Every module gets a module-level doc comment** at the top:

```kea
--| List provides operations on linked lists.
--|
--| Lists are the core recursive data structure in Kea. Use `Cons`
--| to prepend and pattern matching to deconstruct:
--|
--|   let xs = Cons(1, Cons(2, Cons(3, Nil)))
--|   case xs
--|     Cons(head, tail) -> head   -- => 1
--|     Nil -> 0
--|
--| For indexed access and cache-friendly iteration, use `Vector`
--| (available in Tier 2).
```

### 4. Naming consistency

Check these across ALL modules:

| Pattern | Convention | Example |
|---------|-----------|---------|
| Returns Bool | `is_` prefix | `is_empty`, `is_some` |
| Transforms a value | verb | `map`, `filter`, `reverse` |
| Extracts a value | descriptive | `unwrap_or`, `first`, `get` |
| Constructs from other type | `from_` prefix | `from_option` |
| Predicate parameter | name it `pred` | `filter(xs, pred)` |
| Transform parameter | name it `f` | `map(xs, f)` |
| Accumulator | `init` and `acc` | `fold(xs, init, |acc, x| ...)` |
| Subject | first parameter | `map(xs, f)` not `map(f, xs)` |

If any function deviates, fix it.

## Module order

Work through these in order. Commit per module.

1. `result.kea` — most important, sets the Fail-over-Result idiom
2. `option.kea` — close companion to Result
3. `list.kea` — most-used module, highest visibility
4. `int.kea` / `float.kea` — numeric utilities
5. `text.kea` — string operations
6. `order.kea` / `eq.kea` / `ord.kea` — comparison traits
7. `show.kea` — display trait
8. `prelude.kea` — re-exports, should be minimal
9. `io.kea` / `net.kea` / `clock.kea` / `rand.kea` — IO layer
10. `state.kea` / `log.kea` / `reader.kea` / `test.kea` — effect handlers

## What NOT to do

- Don't add new functions. This is a quality pass, not a feature pass.
- Don't refactor implementations unless the signature changes require it.
- Don't fight compiler bugs. If a signature change doesn't compile,
  note it as a TODO and move on to the next function.
- Don't skip the doc comments to move faster. The docs ARE the
  deliverable. The code changes are secondary.

## Validation

After each module:
```
mise run check
PKG=kea mise run test-pkg
```

After completing all modules:
```
mise run check-full
```
