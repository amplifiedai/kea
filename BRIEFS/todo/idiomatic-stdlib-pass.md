# Brief: Idiomatic Stdlib Pass

**Status:** ready
**Priority:** v1
**Depends on:** stdlib-bootstrap Tier 0 blockers resolved
**Blocks:** nothing directly, but establishes quality bar for all future stdlib

## Motivation

The stdlib was written at pace to validate the compiler. It works,
but it doesn't yet exemplify how Kea code should be written. The
stdlib is most users' first real Kea code — it teaches idioms by
example. Every function signature, every doc comment, every pattern
choice is a statement about how to write Kea.

This brief is a quality pass. Read `docs/IDIOMS.md` first — that
document defines what "idiomatic" means. Then apply it systematically
to every stdlib module.

## Scope

Every `.kea` file in `stdlib/`. Currently:

```
prelude.kea  option.kea  result.kea  list.kea  text.kea
int.kea      float.kea   order.kea   eq.kea    ord.kea
show.kea     io.kea      net.kea     clock.kea rand.kea  test.kea
```

## Pass 1: Signatures and return types

### Fail over Result

Audit every function that returns `Result(T, E)`. Most should
return `T` with `-[Fail E]>` instead. Result should only appear as:
- A field type in a struct
- An element type in a list (collecting outcomes)
- The return type of `catch` (explicit reification)

**`result.kea` specifically:**

Remove monadic combinators that encourage Result-chaining over
effect-based error handling:

| Function | Action | Rationale |
|----------|--------|-----------|
| `map` | **Remove** | Use `?` then call `f`. |
| `and_then` | **Remove** | Use `?` then call `f`. |
| `map_err` | **Remove** | Use `handle Fail.fail(e) -> fail(transform(e))`. |
| `unwrap` | **Remove** | This is literally `?`. |
| `unwrap_or` | **Keep** | Legitimate: "give me the value or a default." |
| `is_ok` | **Keep** | Checking without extracting. |
| `is_err` | **Keep** | Checking without extracting. |
| `from_option` | **Keep** | Type conversion, not control flow. |

Add a module-level doc comment explaining Result's role:

```kea
--| Result is Fail's data representation.
--|
--| Use `-[Fail E]> T` in function signatures, not `-> Result(T, E)`.
--| Result appears when you need to store or collect outcomes:
--|
--|   -- Collecting results from multiple operations:
--|   let results = items.map(|item| catch validate(item))
--|
--|   -- Choosing a default on failure:
--|   let config = Result.unwrap_or(catch load_config(), defaults)
--|
--| Use `?` to convert a Result back into a Fail:
--|
--|   let value = some_result?   -- fails if Err, continues if Ok
```

### Effect decomposition

Check that no function uses `IO` as a catch-all when a more
specific effect is appropriate. `IO` should only appear on
functions that actually do IO (file/stdout/stderr). Network
operations use `Net`. Clock operations use `Clock`. Random
operations use `Rand`.

## Pass 2: Documentation

**Every public function must have a `--|` doc comment.** Follow
the standard in `docs/IDIOMS.md` §8 and `stdlib-bootstrap.md`
§ Documentation and Testing Convention.

Quality checklist per function:
- [ ] First line: one sentence, starts with a verb
- [ ] Explains edge cases (empty list, None, zero, negative)
- [ ] At least one example showing typical use
- [ ] At least one example showing edge case / empty / error case
- [ ] Examples use module-qualified calls (`List.map`, not `map`)
- [ ] Examples use `-- =>` for expected results
- [ ] Effect signatures are explained ("fails with X when Y")

**Module-level doc comments.** Each module gets a `--|` block at
the top explaining its purpose and key patterns:

```kea
--| Option represents a value that may or may not be present.
--|
--| Use `Some(value)` for present values and `None` for absent ones.
--| Pattern match to extract:
--|
--|   case opt
--|     Some(x) -> use(x)
--|     None -> fallback()
--|
--| Use `?` to propagate None as a Fail:
--|
--|   let x = opt?   -- fails if None
```

## Pass 3: Naming and consistency

### Naming conventions
- Functions that return `Bool`: prefix with `is_` (`is_empty`,
  `is_some`, `is_negative`)
- Functions that transform: verb form (`map`, `filter`, `fold`,
  `reverse`, `sort`)
- Functions that extract: `unwrap_or`, `get`, `first`, `last`
- Functions that construct: use the type name or `from_*`
  (`from_option`, `from_list`)
- Predicates as parameters: name them `pred`, not `f` or `p`
- Transformations as parameters: name them `f`
- Accumulators: name them `init` and `acc`

### Parameter order
- Subject first: `fn map(xs: List A, f: A -> B)` not
  `fn map(f: A -> B, xs: List A)`
- This enables UMS: `xs.map(f)`
- Callbacks last (enables future `with` syntax)

### Consistency across modules
- If `Option` has `map`, `List` has `map`, they should have the
  same parameter order and naming
- If `Option` has `unwrap_or`, `Result` has `unwrap_or`, same
  pattern
- If `List` has `is_empty`, every collection has `is_empty`

## Pass 4: Test coverage

Each function should have at least one executable test. Until
`kea test` has doctest extraction, write companion test files
or inline Rust integration tests.

Test the doc comment examples — they should be copy-pasteable
and produce the documented result. When doctest extraction lands,
these become automated.

## Definition of Done

- [ ] No function returns `Result(T, E)` where `-[Fail E]> T` is
      appropriate
- [ ] `result.kea` monadic combinators removed, module doc explains
      Result's role as Fail's data representation
- [ ] Every public function has a `--|` doc comment meeting the
      quality checklist
- [ ] Every module has a module-level `--|` doc comment
- [ ] Naming is consistent across all modules
- [ ] Parameter order follows subject-first convention
- [ ] Effect signatures use specific capabilities (not catch-all IO)
- [ ] At least one test per public function
- [ ] All existing tests still pass (`mise run check-full`)

## Process

Work through modules alphabetically. For each module:
1. Read every function signature — fix return types and effects
2. Write/improve doc comments
3. Check naming consistency against the conventions above
4. Write missing tests
5. Run `mise run check` after each module

Commit per-module so progress is incremental and reviewable.
