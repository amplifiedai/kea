# Brief: `with` Syntax (Callback Flattening)

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0e (handler functions must work end-to-end)
**Blocks:** ergonomic handler composition, stdlib `with_*` patterns

## Motivation

Handler stacking is the primary way Kea programs compose effects at
application boundaries. Without `with`, every handler composition
requires nested closures — 3 handlers = 3 levels of indentation.
This is the #1 ergonomic gap in real Kea code right now.

`with` is pure syntactic sugar (KERNEL §10.6). It requires zero type
system or codegen changes. The desugared form uses existing function
call and closure machinery.

## Syntax (from KERNEL §10.6)

**Non-binding form** — handler takes `() -[effects]> T`:
```kea
with Logging.with_stdout
with Config.with_map(settings)
do_work()
```

Desugars to:
```kea
Logging.with_stdout(|| ->
  Config.with_map(settings, || ->
    do_work()))
```

**Binding form** — handler yields a value via `|param| ->`:
```kea
with conn <- Db.with_connection(config)
with file <- File.with_open(path)
process(conn, file)
```

Desugars to:
```kea
Db.with_connection(config, |conn| ->
  File.with_open(path, |file| ->
    process(conn, file)))
```

**Flat, not nested.** Multiple `with` statements at the same
indentation level nest from top to bottom. Same as `let` — no
rightward drift. Lint rule enforces contiguous `with` at block top.

## Implementation

### Step 1: `@with` on parameters

Add `annotations: Vec<Annotation>` field to `Param` in `kea-ast`.
Update the parser to accept `@with` before a parameter:

```kea
fn with_stdout(@with f: () -[Log, e]> T) -[IO, e]> T
```

The `@with` annotation marks the last parameter as the callback
target for `with` syntax. Functions without `@with` on their last
parameter cannot be used with `with` — this gives clear error
messages ("Pool.register is not marked @with") instead of confusing
type mismatches.

Parser change: in `parse_param()`, check for `@` before the param
and collect annotations, same pattern as declaration annotations.

### Step 2: `with` keyword in lexer

Add `With` to `TokenKind` in `crates/kea-syntax/src/lexer.rs`.
Add `"with"` to keyword recognition.

No conflicts — `with` is not currently a valid identifier in any
Kea program (it would shadow nothing).

### Step 3: `with` statement in parser

Add `with_statement()` to the parser. Two forms:

1. `with expr` — non-binding. `expr` is a function call missing
   its last argument.
2. `with pattern <- expr` — binding. Same, but the callback takes
   a parameter.

Detection: when parsing a block and the current token is `With`,
consume it and check for `<-` after the first expression to
distinguish binding from non-binding.

### Step 4: AST node

Add to `ExprKind`:

```rust
/// `with expr` or `with pattern <- expr` followed by rest of block.
With {
    /// The function call (missing its last @with argument).
    call: Box<Expr>,
    /// Binding pattern, if `with pattern <- expr` form.
    binding: Option<Pattern>,
    /// The rest of the block after this `with` statement.
    body: Box<Expr>,
},
```

The parser collects the rest of the block after a `with` and nests
it as the `body`. Multiple sequential `with` statements produce
nested `With` nodes.

### Step 5: Desugaring

Desugar `With` nodes before type checking (in HIR lowering or as
a parser post-pass). The transform is mechanical:

**Non-binding:** `With { call, binding: None, body }` becomes
`call` with an additional argument `|| -> body`.

**Binding:** `With { call, binding: Some(pat), body }` becomes
`call` with an additional argument `|pat| -> body`.

After desugaring, there are no `With` nodes — the type checker,
MIR, and codegen never see them. All existing inference and
diagnostics apply to the desugared form.

### Step 6: `@with` validation

During type checking (or as a post-desugar validation pass):
- When desugaring a `with`, verify the target function's last
  parameter has `@with` annotation.
- If not, emit: `error: cannot use 'with' — Foo.bar is not
  marked @with`
- Include help text pointing to the annotation requirement.

### Step 7: Lint rule

Warn when `with` appears after non-`with`/non-`let` statements
in a block. This is a lint, not an error — the grammar permits
`with` anywhere.

### Step 8: Stdlib `@with` annotations

Add `@with` to existing handler functions in stdlib:
- `State.with_state`
- `Logging.with_stdout` (when it exists)
- Any `with_*` pattern function

## Tests

```kea
-- Non-binding: with as handler scope
fn test_with_nonbinding()
  with State.with_state(0)
  State.put(42)
  assert(State.get() == 42)

-- Binding: with yielding a value
fn test_with_binding()
  with conn <- Db.with_connection(config)
  assert(conn.is_connected())

-- Multiple stacked with
fn test_with_stacked()
  with Logging.with_stdout
  with State.with_state(0)
  Log.info("starting")
  State.put(1)
  assert(State.get() == 1)

-- with after let (valid)
fn test_with_after_let()
  let config = load_config()
  with conn <- Db.with_connection(config)
  query(conn)

-- ERROR: function not marked @with
fn test_with_no_annotation()
  with List.map([1, 2, 3])  -- error: List.map is not marked @with
  0

-- ERROR: with on non-function
fn test_with_non_function()
  with 42  -- error: expected function call
  0
```

## Validation

```
mise run check-full
PKG=kea-syntax mise run test-pkg
PKG=kea mise run test-pkg
```

## Definition of Done

- [ ] `@with` annotation parses on function parameters
- [ ] `with` keyword lexes
- [ ] Non-binding `with expr` parses and desugars
- [ ] Binding `with pattern <- expr` parses and desugars
- [ ] `@with` validation emits clear error on misuse
- [ ] Multiple stacked `with` statements work
- [ ] `with` after `let` works (let bindings visible in with body)
- [ ] Lint warns on `with` after non-with/non-let statements
- [ ] Existing tests pass (no regressions)
