# Kea Kernel Specification — v4

This document defines the semantic invariants of the Kea programming
language. Every rule here must hold for a program to be correct. If the
implementation disagrees with this document, one of them is wrong.

This is not a tutorial, rationale document, or roadmap.

"Compile time" means: the point at which an expression is type-checked.
In the REPL, this is per-input-line. In batch compilation, this is
whole-module.

---

## 0. Notation

- `T`, `A`, `B` denote arbitrary types.
- `r` denotes a row variable.
- `E` denotes an error type.
- `e` denotes an effect row variable (kind `Eff`).
- `{ f1: T1, f2: T2 | r }` denotes an open row with known fields and
  row variable `r`.
- `{ f1: T1, f2: T2 }` denotes a closed row (no row variable).
- "Lacks `l`" on a row variable means the row variable must not contain
  label `l`.
- `-[e]>` denotes an effectful function arrow with effect set `e`.
- `->` denotes a pure function arrow (empty effect set).

**Example convention:** For brevity, examples in this document may
show `fn` declarations outside a struct block. In real code, all
functions must be inside a struct block (§2.8) or called as function
values (§10). Examples are shorthand for the enclosing struct context.

---

## 1. Values and Evaluation

### 1.1 Primitive Types

| Type     | Representation          | Description              |
|----------|-------------------------|--------------------------|
| `Int`    | 64-bit signed integer   | Default integer type     |
| `Float`  | 64-bit IEEE 754         | Floating-point values    |
| `Bool`   | `true` or `false`       | Boolean values           |
| `String` | Immutable UTF-8         | Text values              |
| `Char`   | Unicode scalar value    | Single character         |
| `Bytes`  | Immutable byte sequence | Raw bytes                |
| `Unit`   | Zero-size               | Unit type                |

### 1.1.1 Fixed-Width Numeric Types

| Type     | Representation             |
|----------|----------------------------|
| `Int8`   | 8-bit signed integer       |
| `Int16`  | 16-bit signed integer      |
| `Int32`  | 32-bit signed integer      |
| `Int64`  | 64-bit signed integer      |
| `UInt8`  | 8-bit unsigned integer     |
| `UInt16` | 16-bit unsigned integer    |
| `UInt32` | 32-bit unsigned integer    |
| `UInt64` | 64-bit unsigned integer    |
| `Float32`| 32-bit IEEE 754           |

`Int` is an alias for `Int64`. Integer literals default to `Int`.
Fixed-width types are used when precise representation matters:
binary formats, FFI, hash values, machine code emission.

**Conversions:** All narrowing conversions (e.g. `Int` to `Int8`)
are explicit via `From` / `try_from` and may fail. Widening
conversions (e.g. `Int8` to `Int`) are implicit. Signed-to-unsigned
conversions are always explicit.

### 1.1.2 Bitwise Operations

Bitwise operations are methods on all integer types:

| Method            | Description                 |
|-------------------|-----------------------------|
| `.bit_and(other)` | Bitwise AND                 |
| `.bit_or(other)`  | Bitwise OR                  |
| `.bit_xor(other)` | Bitwise XOR                 |
| `.bit_not()`      | Bitwise NOT (complement)    |
| `.shift_left(n)`  | Left shift by `n` bits      |
| `.shift_right(n)` | Arithmetic right shift      |
| `.shift_right_unsigned(n)` | Logical right shift |

Shift amounts are `Int`. Shifting by a negative amount or by
more than the bit width is a panic.

### 1.1.3 Arithmetic Overflow

Default arithmetic (`+`, `-`, `*`) on fixed-width integer types
**traps on overflow** in debug builds. In release builds, overflow
is unspecified (the compiler may trap, wrap, or optimize assuming
no overflow occurs). This matches the principle that silent
wrapping is a bug source.

For algorithms that intentionally need wrapping (hash functions,
checksums, RNGs), explicit wrapping methods are provided:

| Method                   | Description                  |
|--------------------------|------------------------------|
| `.wrapping_add(other)`   | Wrapping addition            |
| `.wrapping_sub(other)`   | Wrapping subtraction         |
| `.wrapping_mul(other)`   | Wrapping multiplication      |

These always wrap modulo 2^N regardless of build mode.

Saturating and checked variants may be added later.

### 1.1.4 Bit Counting

| Method              | Description                              |
|---------------------|------------------------------------------|
| `.popcount()`       | Number of set bits                       |
| `.leading_zeros()`  | Number of leading zero bits              |
| `.trailing_zeros()` | Number of trailing zero bits             |

Available on all integer types. These map directly to hardware
instructions (`popcnt`, `clz`, `ctz`) via Cranelift intrinsics.

### 1.2 Built-in Compound Types

| Type           | Description                                |
|----------------|--------------------------------------------|
| `Option T`     | `Some(value)` or `None`                    |
| `Result T E`   | `Ok(value)` or `Err(error)`                |
| `List T`       | Ordered, persistent                        |
| `Map K V`      | Unordered, persistent (HAMT). `K: Eq`      |
| `Set T`        | Unordered, persistent (HAMT). `T: Eq`      |
| `(A, B, ...)`  | Tuples (2+ elements)                       |

`List` has built-in literal syntax (§1.5). `Option` and `Result` are
built-in enums with special compiler support for `None`/`Some`/`Ok`/`Err`
constructors.

`Map` and `Set` are hash array mapped tries. Iteration order is not
guaranteed. For ordered access, use `SortedMap`/`SortedSet` from
the standard library, which wrap `Map`/`Set` and maintain a sort
invariant (similar to `Sorted(List(T))`).

### 1.3 No Nil

There is no null, nil, undefined, or similar bottom value. Absence is
expressed with `Option T`. Failure is expressed with `Result T E` or
the `Fail E` effect annotation (§5). There are no exceptions.

### 1.4 Evaluation Rules

- Expression-oriented: every construct produces a value.
- Eager evaluation: arguments are evaluated before function application.
- Call-by-value: function arguments are values, not thunks.
- No implicit coercions. `Int + Float` is a type error.

### 1.5 Literals

| Syntax              | Type          | Notes                       |
|---------------------|---------------|-----------------------------|
| `42`, `-7`          | `Int`         |                             |
| `0xFF`, `0xff`      | `Int`         | Hexadecimal prefix          |
| `0b1010`            | `Int`         | Binary prefix               |
| `0o77`              | `Int`         | Octal prefix                |
| `1_000_000`         | `Int`         | Underscore separators       |
| `3.14`, `-0.5`      | `Float`       | Must contain `.`            |
| `true`, `false`     | `Bool`        |                             |
| `"hello"`           | `String`      | Interpolation: `"{expr}"`   |
| `'a'`               | `Char`        |                             |
| `()`                | `Unit`        | Unit                        |
| `(a, b)`            | `(A, B)`      | Tuple (2+ elements)         |
| `[]`                | `List A`      | Empty list                  |
| `[1, 2, 3]`         | `List Int`    | List literal                |
| `#{ x: 1, y: 2 }`  | `{ x: Int, y: Int }` | Anonymous record      |

### 1.6 String Interpolation

`"Hello, {expr}"` evaluates `expr` and inserts its string representation.

The expression inside `{}` must have type `T` where `T: Show`. Primitive
types (`Int`, `Float`, `Bool`, `String`, `Char`) satisfy `Show` implicitly.
Custom types require an explicit `Show` implementation.

Interpolation calls `Show.show` on the embedded expression. This is a
typed feature: a missing `Show` instance is a compile error, not a
runtime error.

### 1.7 Comments

- `--` begins a line comment. Everything after `--` to end of line is
  ignored.
- `--|` begins a doc comment. Doc comments are attached to the
  immediately following declaration and are available to tooling.
- There are no block comments.

---

## 2. Structs

Structs are product types with named fields. A struct block may also
contain inherent methods (§2.8), nested struct/enum/type definitions
(§2.9), and constructors.

```kea
struct Point
  x: Float
  y: Float

  fn distance(_ self: Point, _ other: Point) -> Float
    let dx = self.x - other.x
    let dy = self.y - other.y
    Float.sqrt(dx * dx + dy * dy)

  fn origin() -> Point
    Point { x: 0.0, y: 0.0 }
```

### 2.1 Construction

```kea
let p = Point { x: 1.0, y: 2.0 }
```

All fields must be provided. There are no default values.

### 2.2 Field Access

```kea
p.x    -- Float
p.y    -- Float
```

### 2.3 Functional Update

```kea
p~{ x: 3.0 }
```

Produces a new value with the specified fields replaced. All other
fields are copied. The original value is unchanged (immutable semantics).

When the reference count is 1, the runtime performs the update in-place
(copy-on-write optimisation). This is unobservable — semantics are
always immutable.

### 2.4 Update vs Extension (Typing Rules for ~)

The `~` operator produces a new value with the union of the original
fields and the specified fields. Update field expressions are
evaluated left-to-right. Duplicate labels in an update block are a
compile error.

The typing rules depend on the input:

**Nominal struct input:**
- `p~{ x: 3.0 }` where `p: Point` — `x` must be a field of `Point`.
  Unknown field names are compile errors. The result type is `Point`.
- Extension (adding new fields) is not allowed on nominal structs.
  The result must have the same type as the input.

**Open row input:**
- `r~{ x: 3.0 }` where `r: { y: Int | tail }` — if `x` is in the
  known fields, it's an update. If `x` is not in the known fields,
  it's an extension and requires `tail lacks x`. The result type
  includes `x` in the known fields.

**Closed anonymous row input:**
- `r~{ x: 3.0 }` where `r: { x: Float, y: Int }` — `x` must be
  a known field. Extension is not allowed on closed rows.

### 2.5 Anonymous Records

```kea
let point = #{ x: 1.0, y: 2.0 }
```

`#{ field: value, ... }` creates an anonymous record. The type is a
closed row: `{ x: Float, y: Float }`.

Anonymous records are structurally typed — two anonymous records with
the same fields and types are the same type. They have no nominal
identity and cannot have inherent methods or trait implementations.

Anonymous records exist to make row polymorphism practical. A function
expecting `{ name: String | r }` can be called with either a named
struct or an anonymous record.

```kea
fn greet(_ person: { name: String | r }) -> String
  "Hello, {person.name}!"

greet(User { name: "Alice", email: "a@b.com" })  -- named struct
greet(#{ name: "World" })                          -- anonymous record
```

### 2.6 Trailing Commas

Trailing commas are always permitted in struct literals, anonymous
records, function arguments, list literals, and enum variant fields.

### 2.7 Modules as Singleton Structs

There are no bare functions. Every function belongs to a struct.
A module with no fields is a singleton struct:

```kea
struct Math

  fn clamp(_ value: Float, min: Float, max: Float) -> Float
    if value < min then min
    else if value > max then max
    else value
```

### 2.8 Inherent Methods

Inherent methods are defined **inside** the struct block. They are
the only methods that may be defined without a trait.

```kea
struct Point
  x: Float
  y: Float

  fn distance(_ self: Point, _ other: Point) -> Float
    let dx = self.x - other.x
    let dy = self.y - other.y
    Float.sqrt(dx * dx + dy * dy)

  fn origin() -> Point
    Point { x: 0.0, y: 0.0 }
```

External modules cannot add inherent methods to a type they do not
own. Trait implementations are separate blocks (§6.2) and are the
only mechanism for adding methods from outside the defining module.

There are no standalone `fn Type.method()` declarations outside
the struct block. All inherent methods live inside the struct.

### 2.9 Nested Types

Structs may contain nested struct, enum, and type alias definitions.
Nested types are accessed via `Parent.Child` syntax.

```kea
struct Server
  port: Int

  struct Config
    port: Int
    handler: Request -[IO, Send]> Response

  struct Request
    method: Method
    path: String
    headers: Map String String
    body: Bytes

  struct Response
    status: Int
    headers: Map String String
    body: Bytes

    fn html(_ status: Int, _ body: String) -> Server.Response
      Server.Response {
        status: status,
        headers: Map.of([("Content-Type", "text/html")]),
        body: Bytes.from_string(body),
      }

  enum Method
    Get
    Post
    Put
    Delete
```

From outside: `Server.Config`, `Server.Request`, `Server.Response`,
`Server.Method`. Nested types may have their own inherent methods
and trait implementations. The nesting is purely for namespacing —
it has no effect on type identity or memory layout.

---

## 3. Enums (Algebraic Data Types)

### 3.1 Definition

```kea
enum Shape
  Circle(center: Point, radius: Float)
  Rectangle(origin: Point, width: Float, height: Float)
  Point
```

Variants may have zero or more named fields. Variants with no fields
are unit variants.

### 3.2 Parameterised Enums

```kea
enum Tree A
  Leaf(value: A)
  Branch(left: Tree A, right: Tree A)
```

### 3.3 GADTs

Constructors may specify their return type:

```kea
enum Expr T
  IntLit(value: Int)                              : Expr Int
  BoolLit(value: Bool)                            : Expr Bool
  Add(left: Expr Int, right: Expr Int)            : Expr Int
  If(cond: Expr Bool, then: Expr T, else: Expr T) : Expr T
```

When a constructor's return type specialises the enum's type parameter,
pattern matching on that constructor introduces an equality constraint
that refines the type variable within the match arm (§4.4).

### 3.4 Constructor Scoping

**In patterns:** Constructors are always unqualified.

```kea
match tree
  Leaf(v) -> ...
  Branch(l, r) -> ...
```

**In expressions:**
- Within the module that defines the enum: unqualified.
- Outside that module: qualified with the enum name (`Tree.Leaf(v)`).
- Explicit import brings constructors into scope:
  `use Trees.Tree.{Leaf, Branch}`.

**Built-in enum constructors** (`Some`, `None`, `Ok`, `Err`) are
always in scope, unqualified, in all modules.

---

## 4. Pattern Matching

### 4.1 Match Expressions

```kea
match expr
  Pattern1 -> body1
  Pattern2 -> body2
```

`match` is an expression. All arms must have the same type.

### 4.2 Pattern Forms

| Pattern                | Matches                              |
|------------------------|--------------------------------------|
| `Constructor(p1, p2)`  | Enum variant, binding fields         |
| `Constructor`          | Unit variant (no fields)             |
| `(p1, p2)`             | Tuple                                |
| `{ f1: p1, f2: p2 }`  | Struct/record destructuring          |
| `{ f1, .. }`           | Struct with punning, ignoring rest   |
| `[p1, p2]`             | List of exact length                 |
| `[head, ..tail]`       | List cons (head + rest)              |
| `[]`                   | Empty list                           |
| `42`, `"hello"`, `true`| Literal                              |
| `name`                 | Variable binding                     |
| `_`                    | Wildcard (matches anything, no bind) |

`..tail` in list patterns is only allowed at the end and only once.

### 4.2.1 Guards

```kea
match msg
  Withdraw(amount) when amount <= self.balance -> ...
  Withdraw(_) -> fail InsufficientFunds
```

`Pattern when condition -> body`. The guard condition is evaluated
after the pattern matches and variable bindings are available. If
the guard evaluates to `false`, matching continues to the next arm.

The keyword is `when`, not `if`, to avoid ambiguity with `if`/`else`
expressions inside case arms.

Guards must be pure expressions — no semantic effects (IO, Send,
Spawn) and no Fail. Guards may reference variables bound by the
pattern. This is enforced by the compiler.

### 4.3 Exhaustiveness

Non-exhaustive `match` on an enum is a compile error. The compiler
verifies all constructors are covered. `_` is a catch-all.

`match` over `Int`, `String`, `Float`, or `Bool` requires a `_` arm.

### 4.4 GADT Refinement

When matching on a GADT constructor whose return type specialises a
type variable, that variable is refined within the match arm.

```kea
fn eval(_ expr: Expr T) -> T
  match expr
    IntLit(v) -> v      -- T = Int in this arm, v: Int, return: Int
    BoolLit(v) -> v     -- T = Bool in this arm
    ...
```

Refinement is branch-local. It does not extend beyond the match arm.

---

## 5. Effects

Kea has algebraic effects with handlers. Effects are user-defined.
The standard library defines common effects (`IO`, `Fail`); other
libraries define their own (`Send`, `Spawn`, `Alloc`, `Log`, etc.).
The language provides the mechanism; libraries provide the effects.

### 5.1 Effect Annotations

Every function has an effect signature. Pure functions use `->`.
Effectful functions use `-[effects]>`.

```kea
fn add(_ a: Int, _ b: Int) -> Int
fn read(_ path: String) -[IO, Fail FileError]> Bytes
```

`->` asserts the empty effect set (pure). `-[effects]>` asserts
exactly the listed effects.

**All `fn` definitions require a full signature** — parameter
types, return type, and effect annotation. `->` is a pure
assertion; `-[effects]>` lists the exact effect set. The
compiler infers the body's effects and checks them against
the declared signature.

**Closures have inferred signatures.** Parameter types, return
type, and effects are all inferred from context. Annotations
are optional.

```kea
-- fn definitions: full signature required
fn add(_ a: Int, _ b: Int) -> Int
fn load(_ path: String) -[IO, Fail ConfigError]> Config

-- Closures: everything inferred
users.filter(|u| -> u.active)
users.map(|u| -> u.name.to_uppercase())

-- Closures CAN have annotations
users.map(|u: User| -> u.name)
```

This means every `fn` is self-documenting — the signature
tells you the inputs, outputs, and effects without hovering
in the LSP. Effect provenance is traceable by reading
signatures alone. `grep -r "\-\[IO\]"` finds every function
that performs IO.

```
error: function `load` requires an effect annotation
  --> src/db.kea:3:1
   |
3  | fn load(_ path: String)
   |    ^^^^ missing return type and effect annotation
   |
   = note: inferred signature: -[IO, Fail DbError]> Config
```

### 5.2 Defining Effects

An effect declaration introduces a set of operations:

```kea
effect IO
  fn read_file(_ path: String) -> Bytes
  fn write_file(_ path: String, _ data: Bytes) -> Unit
  fn stdout(_ msg: String) -> Unit
  fn clock_now() -> Timestamp
  fn net_connect(_ addr: String, _ port: Int) -> Connection
```

Each operation is a function signature. Performing an effect
operation introduces that effect into the current function's
effect set.

Effects may be parameterised:

```kea
effect Fail E
  fn fail(_ error: E) -> Never

effect State S
  fn get() -> S
  fn put(_ new_state: S) -> Unit
```

`Fail E` is parameterised by the error type. `State S` is
parameterised by the state type.

Effect declarations may appear at the top level of a module,
inside a struct block, or inside a library. Effects follow the
same visibility rules as types (`pub` for public).

### 5.3 Performing Effects

Calling an effect operation performs the effect. The effect is
added to the current function's effect set:

```kea
fn greet(_ name: String) -[IO]> Unit
  IO.stdout("Hello, {name}!")        -- performs IO

fn load(_ path: String) -[IO, Fail FileError]> Config
  let data = IO.read_file(path)      -- performs IO
  Config.parse(data)?                -- performs Fail
```

Effect operations are called with qualified syntax:
`Effect.operation(args)`. This makes effect usage visible and
explicit in the code.

### 5.4 Effect Set Algebra

Effects form a commutative, idempotent set under union (⊔).
When the compiler joins effect sets (from branches, sequencing,
or function composition), it takes the union of effects.

A function without any effects is **pure**. Pure functions:
- Can be memoised.
- Can be reordered or run in parallel.
- Can have dead code eliminated when the result is unused.

There is no subeffect relation between effects by default.

For `Fail`, joining two branches with different error types
requires unification or `From` conversion:

```kea
fn f(_ b: Bool) -[Fail AppError]> Int
  if b
    Fail.fail(FileError(...))     -- requires From FileError for AppError
  else
    Fail.fail(ParseError(...))    -- requires From ParseError for AppError
```

A function may have at most one `Fail E` in its effect set.
Multiple error types must be unified into a single sum type.

### 5.5 Effect Polymorphism

Higher-order functions can be polymorphic in effects:

```kea
fn map(_ self: List A, _ f: A -[e]> B) -[e]> List B
```

If `f` is pure, `map` is pure. If `f` has `IO`, `map` has `IO`.
The effect variable `e` represents an arbitrary effect set.

Effect row variables can appear in type aliases (§11.5) and
where clauses (§7.6), making effect sets reusable:

```kea
type DbEffects = [IO, Fail DbError]
type WebEffects = [IO, Fail AppError, Log]

fn query(_ sql: String) -DbEffects> Rows
fn handle_request(_ req: Request) -WebEffects> Response
```

Effect row variables in where clauses constrain effect sets:

```kea
fn retry(_ n: Int, _ f: () -[Fail E, e]> T) -[e]> Option T
  where E: Show
```

This constrains the error type to be showable while propagating
all other effects. See §11.5 for the full rules on effect aliases.

### 5.6 Handlers

A handler intercepts effect operations and provides their
implementation. Handlers are how effects are given meaning.

```kea
handle expr
  Effect.operation(args) -> handler_body
```

Inside the handler body, `resume value` returns `value` to the
point where the effect was performed, and execution continues
from there.

**Example — logging handler:**

```kea
effect Log
  fn log(_ level: Level, _ msg: String) -> Unit

fn with_stdout_logger(_ f: () -[Log, e]> T) -[IO, e]> T
  handle f()
    Log.log(level, msg) ->
      IO.stdout("[{level}] {msg}")
      resume ()
```

The handler removes `Log` from the effect set and adds `IO`
(because the implementation uses `IO.stdout`). The typing rule:
if the handler body for effect `E` has effects `{H...}`, and the
handled expression has effects `{E, R...}`, the `handle`
expression has effects `{H..., R...}` — the handled effect is
replaced by the handler's effects.

**Example — state handler:**

```kea
effect State S
  fn get() -> S
  fn put(_ new_state: S) -> Unit

fn with_state(_ initial: S, _ f: () -[State S, e]> T) -[e]> (T, S)
  let state = Unique initial
  let result = handle f()
    State.get() ->
      resume state.freeze()
    State.put(new_state) ->
      state = new_state
      resume ()
  (result, state.freeze())
```

**Example — mock IO for testing:**

```kea
fn with_mock_fs(_ files: Map String Bytes, _ f: () -[IO, e]> T) -[e]> T
  handle f()
    IO.read_file(path) ->
      match files.get(path)
        Some(data) -> resume data
        None -> panic "mock: file not found: {path}"
    IO.write_file(path, data) ->
      resume ()
    IO.stdout(msg) ->
      resume ()
    IO.clock_now() ->
      resume (Timestamp.epoch())
    IO.net_connect(addr, port) ->
      panic "mock: network access not allowed"
```

This handler replaces real IO with mock behaviour. Code under
test runs with `-[IO]>` but no actual side effects occur. The
handler removes `IO` from the effect set.

### 5.7 Resumption

`resume value` returns `value` to the call site of the effect
operation and continues execution.

**Kea restricts resumptions to at-most-once (zero or one):**

- **One resumption:** Normal case. The handler provides a value
  and execution continues. Used by `Log`, `State`, `Alloc`, etc.
- **Zero resumptions:** The handler does not resume. Execution
  of the handled computation is aborted. Used by `Fail` (the
  handler catches the error and returns without resuming).

Multi-shot continuations (resuming more than once) are not
supported. This restriction simplifies the implementation
(no need to copy the continuation stack) and avoids surprising
non-determinism.

`resume` is only valid inside a handler body. It is not a
first-class value — it cannot be stored, returned, or passed
to another function.

### 5.8 Fail: Error Propagation (Sugar)

`Fail E` is a parameterised effect defined in the standard
library:

```kea
effect Fail E
  fn fail(_ error: E) -> Never
```

Because error handling is ubiquitous, Kea provides syntactic
sugar that desugars to `Fail` operations and handlers:

**`fail expr`** is sugar for `Fail.fail(expr)`:

```kea
fn validate(_ x: Int) -[Fail String]> Int
  if x < 0
    fail "must be non-negative"
  x
```

**`?` operator** unwraps `Result` or performs `Fail`:

```kea
let value = fallible_call()?
-- desugars to:
let value = match fallible_call()
  Ok(v) -> v
  Err(e) -> Fail.fail(From.from(e))
```

If the `Err` type of the callee differs from the current
function's `Fail E` type, a `From` implementation must exist.
The compiler inserts the conversion automatically.

**`catch` handler** converts `Fail` to `Result`:

```kea
let result = catch some_call()
```

Typing rule: if `expr` has type `T` with effects `{Fail E, R...}`,
then `catch expr` has type `Result T E` with effects `{R...}`.
`Fail E` is removed; all other effects are preserved.

`catch` desugars to a handler that does not resume:

```kea
-- catch expr desugars to:
handle expr
  Fail.fail(error) -> Err(error)
then |value| -> Ok(value)
```

### 5.9 Alloc: Arena-Scoped Allocation (Stdlib Effect)

`Alloc` is an effect defined in the standard library:

```kea
effect Alloc
  fn alloc(_ layout: Layout) -> Ptr UInt8
```

The `Alloc` effect redirects heap allocations to an arena. Inside
an `-[Alloc]>` function, code is unchanged — allocation is
implicit. The effect handler provides the arena.

**`with_arena` handler:**

```kea
fn with_arena(_ f: () -[Alloc, e]> T) -[e]> T
```

`with_arena` creates an arena, handles `Alloc` by bump-allocating
from it, deep-copies the return value into the caller's allocation
context, and frees the arena. Typing rule: `Alloc` is removed;
all other effects are preserved.

**Default handler:** If `Alloc` is not explicitly handled, the
runtime's default handler uses the normal refcounted heap.
`-[Alloc]>` signals that arena allocation would be beneficial,
not that it is required.

The full specification of arena allocation semantics — inbound
references, return-value copying, nesting, interaction with
`Unique`, and actor messages — is in §12.7.

### 5.10 Standard Library Effects

The standard library defines these effects. They are not
language primitives — they are ordinary effect declarations.

| Effect      | Defined in      | Operations                     | Common handler                |
|-------------|-----------------|--------------------------------|-------------------------------|
| `IO`        | `kea-io`        | `read_file`, `write_file`, `stdout`, `clock_now`, `net_connect`, ... | Runtime (or mock for tests) |
| `Fail E`    | `kea-core`      | `fail`                         | `catch` (sugar)               |
| `Alloc`     | `kea-core`      | `alloc`                        | `with_arena`                  |

Other libraries define their own effects:

| Effect      | Defined in      | Operations              | Example handler               |
|-------------|-----------------|-------------------------|-------------------------------|
| `Send`      | `kea-actors`    | `tell`, `ask`           | Actor runtime                 |
| `Spawn`     | `kea-actors`    | `spawn`                 | Actor runtime                 |
| `Log`       | `kea-log`       | `log`                   | `with_stdout_logger`, etc.    |
| `State S`   | `kea-state`     | `get`, `put`            | `with_state`                  |
| `Rand`      | `kea-rand`      | `random`, `random_int`  | `with_seed`                   |
| `Tx`        | `kea-db`        | `query`, `execute`      | `with_transaction`            |

**Purity:** A function with no effects (`->`) is pure. A function
whose only effect is `Fail E` is deterministic and pure for
optimisation purposes. A function whose only effect is `Alloc` is
pure modulo allocation strategy.

### 5.11 Effect Inference

Effects are inferred bottom-up. The effect set of a function body
is the union of the effect sets of all expressions in the body.

For `fn` definitions, inference is verification — the compiler
infers the body's effects and checks them against the explicit
annotation. For closures, inference determines the signature.

An explicit annotation may be broader than inferred (declaring
more effects than used). It may not be narrower (claiming purity
when the body has effects).

### 5.12 IO and the Runtime

`IO` is the one effect that cannot be fully handled by user code
in production. Its handler is the runtime — the runtime provides
the actual file system, network, and clock operations.

For testing, `IO` can be handled by mock handlers (§5.6). This
is the primary mechanism for testing effectful code without real
side effects.

`fn main() -[IO]> Unit` is the entry point. The runtime handles
`IO` operations in `main`. Any unhandled effects at the `main`
boundary (other than `IO`) are a compile error.

### 5.13 Handler Typing Rules (Summary)

A `handle` expression has the following typing:

```
Given:
  expr : T  with effects {E, R...}
  handler for E.operation(args) -> handler_body
  handler_body : _  with effects {H...}

Then:
  handle expr { E.operation(args) -> handler_body }
    : T  with effects {H..., R...}
```

The handled effect `E` is removed. The handler body's effects
`H` are added. All other effects `R` pass through. This is
row polymorphism on the effect set.

### 5.14 Effect-Parameterised Types

Structs and enums may take effect row parameters. This lets
types carry their effect footprint, enabling reusable abstractions
over effectful computations.

```kea
type Handler E = Request -[E]> Response

struct Server E
  handler: Handler E
  port: Int
  middleware: List (Handler E -> Handler E)
```

`E` here has kind `Eff` (an effect row). The type is instantiated
with a concrete effect set:

```kea
let server: Server [IO, Fail AppError] = Server
  handler: my_handler
  port: 8080
  middleware: [logging, auth]
```

**Effect-parameterised enums:**

```kea
enum Step E A
  Continue(A)
  Yield(A, () -[E]> Step E A)
  Done
```

This enables lazy, effectful iteration where the effect set is
a parameter of the stream type.

**Handler wrapper pattern.** A common use is abstracting over
handler-shaped functions:

```kea
type Wrap E_in E_out T = (() -[E_in]> T) -[E_out]> T

fn compose_handlers(_ outer: Wrap E1 E2 T, _ inner: Wrap E2 E3 T)
  -> Wrap E1 E3 T
  |f| -> outer(|| -> inner(f))
```

This gives middleware composition without needing effect
subtraction operators. The compiler infers `E1`, `E2`, `E3`
at each application site.

**Restrictions (v0):**

1. Effect row variables in type parameter position only — not
   arbitrary computed effect expressions.
2. Effect rows remain sets (no duplicates, commutative).
3. No effect subtraction or addition operators at the type level.
   Effect removal happens operationally via `handle`, not via
   type-level algebra.

These restrictions keep inference tractable and error messages
clear. If effect-set algebra proves necessary for real library
design, it can be added later without breaking existing code.

See §6.6 for the kind system, §11.5 for effect row aliases.

The `then` clause (optional) transforms the result when the
handled computation completes normally (without performing the
handled effect):

```kea
handle expr
  E.operation(args) -> handler_body
then |result| -> transform(result)
```

When `E` is performed: the handler body runs. Whether to
`resume` is the handler's choice.

When `E` is NOT performed: the `then` clause transforms the
result. If no `then` clause, the result passes through unchanged.

### 5.15 Effect Compilation Guarantees

Effects are a type-system feature first and a runtime feature
second. The compiler classifies effects by compilation strategy
to ensure effectful code is competitive with hand-written
imperative code.

**Capability effects** — compile to direct calls with no
handler overhead:

| Effect  | Compilation                                  |
|---------|----------------------------------------------|
| `IO`    | Direct runtime calls (syscalls, libc)        |
| `Send`  | Direct actor runtime calls                   |
| `Spawn` | Direct actor runtime calls                   |

These effects exist for type-level tracking. In production,
their handler is the runtime — there is no continuation
capture, no evidence lookup, no closure allocation. An
`-[IO]>` function compiles to the same code as an equivalent
function with direct syscalls in C or Go.

In tests, these effects can be handled by mock handlers
(§5.6), which use the general handler machinery. The
performance cost is only paid when you opt into it.

**Zero-resumption effects** — compile to early return:

| Effect    | Compilation                                |
|-----------|--------------------------------------------|
| `Fail E`  | Result-passing, branch-on-error            |

`Fail.fail(e)` compiles to returning an error value.
`?` compiles to a conditional branch. `catch` compiles to
a match on the result. No continuation capture — the handler
never resumes, so there is no continuation to capture. This
is equivalent to Rust's `Result` + `?` at the machine level.

**Tail-resumptive handlers** — compile to direct function
calls:

A handler clause where `resume` is the last expression
(tail position) does not need continuation capture. The
handler body executes, then control returns to the operation
call site. This covers the vast majority of handlers in
practice:

```kea
-- Tail-resumptive: resume is last expression
Log.log(level, msg) ->
  IO.stdout("[{level}] {msg}")
  resume ()              -- tail position → direct call

State.get() ->
  resume state.freeze()  -- tail position → direct call
```

The compiler classifies each handler clause at compile time.
Tail-resumptive clauses compile as direct function calls with
no stack manipulation. Only non-tail-resumptive handlers
(where `resume` appears in non-tail position) use the full
handler machinery.

**General handlers** — full handler compilation:

Non-tail-resumptive handlers require continuation capture.
This is the most expensive compilation strategy and is
reserved for handlers that transform the computation around
the resume point:

```kea
-- Non-tail-resumptive: resume in non-tail position
Choose.choose(options) ->
  let picked = resume(options.first())
  transform(picked)    -- code after resume
```

This case is rare in practice. Most real-world handlers are
tail-resumptive (log-and-resume, read-state-and-resume,
write-state-and-resume).

**Monomorphization.** Generic functions are monomorphized by
default (like Rust). A function `fn map(list: List A, f: A -> B) -> List B`
generates specialised code for each concrete `A` and `B`.
Trait method calls on known types are direct calls, not
dynamic dispatch. Dynamic dispatch (trait objects) is opt-in
for cases that require runtime polymorphism.

**Performance target.** Effectful code using capability
effects and tail-resumptive handlers should have no
measurable overhead compared to equivalent code without
effects. The effect system is a zero-cost abstraction for
the common case — you pay only for the handler machinery
you actually use.

---

## 6. Traits

### 6.1 Definition

```kea
trait Show
  fn show(_ self: Self) -> String
```

Trait methods use explicit `self` parameter. Static methods omit
`self`. `Self` refers to the implementing type.

### 6.2 Implementation

```kea
Point as Show
  fn show(_ self: Point) -> String
    "({self.x}, {self.y})"
```

The syntax is `Type as Trait`. Within the block, all methods must
be provided. Trait implementations are always separate blocks,
outside the struct definition.

### 6.3 Conditional Implementations

```kea
Tree A as Show where A: Show
  fn show(_ self: Tree A) -> String
    match self
      Leaf(v) -> "Leaf({v.show()})"
      Branch(l, r) -> "Branch({l.show()}, {r.show()})"
```

`where` clauses constrain type parameters on impl blocks.

### 6.4 Parameterised Traits

```kea
trait From T
  fn from(_ value: T) -> Self
```

Implementation:

```kea
ConfigError as From FileError
  fn from(_ value: FileError) -> ConfigError
    ConfigError.IoError(value)
```

`Self` is always the type on the left of `as`.

### 6.5 Associated Types

```kea
trait Iterator
  type Item
  fn next(_ self: Self) -> Option (Self.Item, Self)
```

### 6.6 Kind System

Kea has two kinds:

- `*` — ordinary types (Int, String, List Int, Map String Int)
- `Eff` — effect rows ([IO, Fail E], [Send, Spawn])

There are no higher-kinded types (`* -> *`). Type constructors
like `List`, `Option`, and `Map` are not first-class — you cannot
abstract over "any type constructor." Effects replace the primary
motivation for HKTs: IO, State, Error, Reader are effects, not
monadic types. Handler composition replaces monadic composition.
Collection traits (`Foldable`, `Enumerable`, `Filterable`) work
on concrete types — `Self` is `List Int`, not `List`. This is
Elixir's Enum protocol: any type implementing `Foldable` gets
`fold`, `sum`, `find` via trait dispatch. What you can't write
is `fn summarize(c: F Int) where F: Foldable` — abstracting
over the container. You write `fn summarize(c: impl Foldable)`
where the concrete type carries both container and element info.
Container-specific operations like `map` are inherent methods
(`List.map`, `Option.map`).

**Kind inference.** The compiler infers kinds from usage. A type
parameter used in effect position (`-[E]>`) is inferred to have
kind `Eff`. All other type parameters have kind `*`. Explicit kind
annotations are not part of the language.

```kea
struct Server E        -- E : Eff (inferred from usage below)
  handler: Request -[E]> Response

trait Runnable E       -- E : Eff
  fn run(_ self: Self) -[E]> Unit

fn transform(_ x: A) -> A    -- A : * (default)
```

Kind errors are reported when a type parameter is used
inconsistently (e.g., as both a type and an effect row).

### 6.7 Supertraits

```kea
trait Ord where Self: Eq
  fn compare(_ self: Self, _ other: Self) -> Ordering
```

An `Ord` implementation requires an `Eq` implementation to exist.

### 6.8 Coherence (Orphan Rule)

A trait implementation is allowed if and only if the implementing
module owns the trait or owns the type. Implementing a foreign trait
for a foreign type is a compile error.

**Nested type ownership:** A nested type (`Parent.Child`) is owned
by the module that defines the outer struct. `Server.Request` defined
in `http/server.kea` is owned by the `Http.Server` module. Trait
implementations for `Server.Request` follow the same orphan rule —
they are allowed in `Http.Server` or in the module that defines the
trait.

### 6.9 Deriving

```kea
@derive(Show, Eq)
struct Point
  x: Float
  y: Float
```

`@derive` invokes a compiler recipe that generates trait implementations
from the type definition. The generated implementation must type-check.

---

## 7. Row Polymorphism

### 7.1 Row Types

A row type is an unordered set of label-type pairs, either open or closed.

- Open: `{ name: String, age: Int | r }` — at least these fields,
  possibly more via row variable `r`.
- Closed: `{ name: String, age: Int }` — exactly these fields.

Field order is insignificant: `{ x: Int, y: Int }` and `{ y: Int, x: Int }`
are the same type. Duplicate labels are a compile error in row type
annotations, record literals (`#{ ... }`), struct literals, and
update expressions (`~`).

### 7.2 Row-Polymorphic Functions

```kea
fn greet(_ person: { name: String | r }) -> String
  "Hello, {person.name}!"
```

This accepts any value — named struct or anonymous record — that has
at least a `name: String` field.

### 7.3 Lacks Constraints

When extending a row with label `l`, the row variable must lack `l`:

```kea
fn add_field(_ rec: { x: Int | r }, _ y: Bool)
  -> { x: Int, y: Bool | r }
  where r lacks y
  rec~{ y: y }
```

### 7.4 Row Unification

Unifying `{ x: Int | r1 }` with `{ y: Bool | r2 }` produces:

```
r1 ~ { y: Bool | r3 }
r2 ~ { x: Int  | r3 }
r3 lacks x, y
```

This is Rémy-style row decomposition. Lacks constraints propagate
during unification.

### 7.5 Structural Projection

Named structs are **nominal** for trait dispatch and type identity.
They are **structurally projected** for row polymorphism.

A function expecting `{ name: String | r }` accepts `User`,
`Company`, or any struct with a `name: String` field. The value
retains its nominal type — projection is a unification rule, not
a type conversion.

**Visibility rule:** Outside the defining module, a named struct
projects only its `pub` fields into row types. Inside the defining
module, all fields are projected. Private fields are never visible
through row polymorphism from external modules.

### 7.6 Row Constraints in Where Clauses

Type variables may carry row constraints:

```kea
fn run_all(_ tasks: List A) -[IO]> List String
  where A: Runnable, A: { name: String | _ }
```

This requires `A` to implement `Runnable` AND have at least a
`name: String` field. The `_` indicates the remaining fields are
existentially quantified and not referenced.

---

## 8. Type Inference

### 8.1 Hindley-Milner with Extensions

- Let-generalisation: `let id = |x| -> x` gives `id` the type
  `A -> A` (polymorphic).
- Lambda-bound variables are monomorphic within the body.
- Annotations on public functions are checked against inferred types.

### 8.2 Bidirectional Checking

When an expected type is available (from annotations, return position,
or assignment context), the checker uses it to guide inference.

```kea
let x: Option Int = Some(42)
```

The expected type `Option Int` is propagated inward, resolving
the constructor's type parameter without explicit annotation.

### 8.3 Where Clauses

Trait bounds and row constraints constrain type variables:

```kea
fn sort(_ list: List A) -> List A where A: Ord
```

---

## 9. Methods and Dispatch

Kea uses **dot syntax** for all name resolution: field access, method
calls, namespace qualification, and nested type access. The dot is the
only accessor operator. There is no `::` turbofish. There is no `|>`
pipe operator.

**Disambiguation rule:** PascalCase after a dot is a namespace step
(module, type, or trait qualifier). Lowercase after a dot on a value
is field access or method call. This is a lexical rule — the parser
never needs type information to distinguish namespace access from
field access.

### 9.1 Method Resolution

**Field vs method:** `expr.name` (no parens) is always field access.
`expr.name(args)` (with parens) is always a method call. A field and
a zero-arg method with the same name may coexist but produce a lint
warning.

For `expr.method_name(args)`, lookup proceeds:

1. **Inherent methods** on the nominal type of `expr` (defined inside
   the struct block). If found, **inherent wins** — stop here.
2. **Trait methods** from traits that are in scope (via `use` or
   prelude) and implemented for the type of `expr`. Only reached
   if no inherent match exists.

Inherent-vs-trait is never ambiguous: inherent always wins. To call
the trait version when an inherent method shadows it, use qualified
dispatch: `expr.Trait.method()`.

Trait-vs-trait collision (multiple in-scope traits provide the same
method name for the same type) is an ambiguity error requiring
qualified dispatch.

**Structural types:** Anonymous records and open-row-typed values
have no inherent methods. Only trait methods from in-scope traits
apply. This means `#{ x: 1, y: 2 }.show()` works (via `Show`
trait) but you cannot define inherent methods on structural types.

**Scope of unqualified dot:** Only inherent methods and in-scope
trait methods are candidates. Module functions are not part of
unqualified dot resolution. To call a module function as a method,
use qualified dispatch: `expr.Module.function(args)`.

A trait's methods are only available for dispatch if the trait name
has been brought into scope. The **standard prelude** automatically
brings core traits into scope in every module (see Appendix C for
the full list).

### 9.2 Qualified Dispatch

PascalCase in dot position is a namespace qualifier (trait, module,
or type). The same dot syntax used for field access and unqualified
methods also serves for explicit qualification:

```kea
value.Show.show()               -- trait-qualified
things.List.map(f)              -- module/struct-qualified
users.Enum.filter(|u| -> u.active)  -- module-qualified
```

**Dot is dot.** There is no separate namespace operator. PascalCase
after a dot is always a namespace step; lowercase after a dot on a
value is always field access or method call. The parser distinguishes
these lexically — no type information needed.

### 9.3 Universal Receiver Placement with `$`

By default, `expr.method(args)` places the receiver as the first
positional (`_`-prefixed) parameter. `$` overrides this, placing
the receiver at the `$` position:

```kea
-- Default: receiver is first positional param
users.filter(|u| -> u.active)
-- equivalent to: List.filter(users, |u| -> u.active)

-- $ overrides receiver position
text.String.replace("old", $, "new")
-- equivalent to: String.replace("old", text, "new")

body.Json.decode($, User)
-- equivalent to: Json.decode(body, User)
```

`$` may appear at most once in a method call's argument list.

Receiver placement rules:
1. If `$` is present: receiver fills the `$` position.
2. If `$` is absent: receiver fills the first `_` (positional)
   parameter of the resolved function.
3. If no `$` and no positional parameter exists: compile error
   ("cannot use method syntax — no positional parameter for receiver").
4. Labeled parameters are never receiver candidates.

`$` works with both qualified and unqualified method calls.

**Grammar restriction:** `$` is valid only in the argument list of
a dot-method call (`expr.method(... $ ...)`) or a qualified dot-method
call (`expr.Qual.method(... $ ...)`). It is not a general expression,
cannot appear in patterns, prefix calls, operator operands, or any
other syntactic position. `$` outside a method-call argument list is
a parse error.

### 9.4 Method Chaining

Method syntax provides left-to-right chaining without pipes:

```kea
users
  .filter(|u| -> u.active)
  .map(|u| -> u.name)
  .sort()
  .take(10)
```

Each `.method(args)` call takes the result of the previous expression
as its receiver. This is the idiomatic way to chain operations.

### 9.5 Prefix Calls

Functions can always be called in prefix form:

```kea
let n = Int.parse("42")
let s = String.join(parts, ", ")
let total = Enum.sum(scores)
```

Module functions on singleton structs are called qualified.

---

## 10. Functions and Closures

Top-level function declarations must be inside a struct block (§2.8)
or a singleton module struct (§2.7). Lambdas are first-class values
and may appear in any expression position.

**Function-typed value application:** If a local binding, parameter,
or field has a function type, it may be called directly: `f(args)`.
This is value application, not a bare function definition.

```kea
let f = |x| -> x * 2
f(10)                    -- legal: f is a function-typed value

let handler = router.get("/")
handler(request)         -- legal
```

**Name resolution for `name(args)` (no dot, no qualifier):**

1. Local bindings and parameters in current scope.
2. Enum constructors in scope (imported or same module).
3. If `name` matches none of the above: compile error.

`name(args)` never resolves to a module function. Module functions
require qualification: `Module.function(args)`. This ensures the
parser and type checker never confuse function-value calls with
module function calls.

### 10.1 Function Definitions

```kea
struct Point
  x: Float
  y: Float

  fn distance(_ self: Point, _ other: Point) -> Float
    let dx = self.x - other.x
    let dy = self.y - other.y
    Float.sqrt(dx * dx + dy * dy)
```

### 10.2 Labeled and Positional Parameters

`_` marks positional (unlabeled) parameters. All others are labeled:

```kea
fn substring(_ s: String, from: Int, to: Int) -> String
```

Call: `substring("hello", from: 1, to: 3)`.

### 10.2.1 Parameter Conventions

Parameters have a convention that determines ownership transfer:

| Convention | Syntax | Meaning |
|---|---|---|
| Default | `_ x: T` | Shared access. Refcount incremented on entry, decremented on exit. |
| Borrow | `borrow x: T` | Read-only loan. No refcount change. Callee may not store, return, or capture the reference. |

For `Unique T` parameters, the default convention is **move**:
the caller transfers ownership and may not reference the value
after the call. `borrow` on a `Unique T` parameter grants
temporary read access without consuming ownership (§12.6).

`borrow` may be combined with `_` for positional borrowed
parameters: `fn length(borrow _ self: Unique Buffer) -> Int`.

### 10.3 Lambdas

```kea
let double = |x| -> x * 2
let add = |a, b| -> a + b
```

Multi-line:

```kea
let process = |item| ->
  let cleaned = item.clean()
  let validated = cleaned.validate()
  validated.transform()
```

The body of a lambda is the indented block following `->`.

### 10.4 If Expressions

`if` is an expression.

```kea
let abs = if x >= 0 then x else -x
```

When used as an expression (value is consumed), `else` is required.
When used as a statement (value is `Unit`), `else` may be omitted:

```kea
if should_log
  IO.println("logged")
```

**Syntax variants:**
- `if cond then expr else expr` — single-line (requires `then`)
- `if cond` / indented block / `else` / indented block — multi-line

### 10.5 For Loops

```kea
for x in xs
  IO.println(x.show())
```

`for x in xs` desugars to `Enumerable.to_seq(xs)` followed by
sequential consumption. The body has type `Unit`. `for` is a statement,
not an expression — it always returns `Unit`.

For collecting results, use `.map()` or `.fold()` instead of `for`.

### 10.6 With Expressions (Callback Flattening)

`with` is syntactic sugar for passing the rest of the current block
as a callback (the last argument) to a function. It exists to flatten
nested handler application and resource scoping.

**Non-binding form:**

```kea
with Logging.with_stdout
with Database.with_transaction(conn)
let result = catch OrderService.process_order(order)
IO.stdout(result.show())
```

Desugars to:

```kea
Logging.with_stdout(|| ->
  Database.with_transaction(conn, || ->
    let result = catch OrderService.process_order(order)
    IO.stdout(result.show())
  )
)
```

Each `with expr` takes everything after it in the current block,
wraps it in `|| ->`, and appends it as the last argument to `expr`.

**Binding form:**

```kea
with conn <- Db.with_connection(config)
with file <- File.with_open(path)
process(conn, file)
```

Desugars to:

```kea
Db.with_connection(config, |conn| ->
  File.with_open(path, |file| ->
    process(conn, file)
  )
)
```

Each `with pattern <- expr` wraps everything after it in
`|pattern| ->` and appends it as the last argument to `expr`.
The pattern must be irrefutable (variable binding or destructuring
that always succeeds). Refutable matching should use `match`
inside the continuation.

**`@with` annotation required.** `with` only works with functions
whose last parameter is annotated `@with`. This prevents accidental
control-flow rewrites — a function whose last parameter happens to
be a callback is not automatically `with`-able.

```kea
struct Logging
  @with
  fn with_stdout(_ f: () -[Log, e]> T) -[IO, e]> T
    handle f()
      Log.log(level, msg) ->
        IO.stdout("[{level}] {msg}")
        resume ()

struct Db
  @with
  fn with_connection(_ config: DbConfig, _ f: Connection -[e]> T)
    -[IO, Fail DbError, e]> T
    let conn = Db.connect(config)?
    let result = f(conn)
    conn.close()
    result
```

A function without `@with` on its last parameter cannot be used
with `with`. This is a compile error:

```
error: cannot use `with` — Pool.register is not marked @with
  --> src/app.kea:5:6
   |
5  |   with Pool.register("worker")
   |        ^^^^^^^^^^^^^^^^^^^^^^^ not @with-able
   |
   = help: `with` requires the target function's last parameter
     to be annotated @with. Pool.register takes a callback as its
     last argument but is not designed for scoped use.
```

**Placement rule.** `with` statements should appear contiguously
at the beginning of a block (after initial `let` bindings).
Interleaving `with` with other statements is a lint warning:

```kea
-- Good: with statements at top of block
let config = load_config()
with Logging.with_stdout
with conn <- Db.with_connection(config.db)
query(conn, "SELECT 1")

-- Lint warning: with after non-with statement
do_setup()
with Logging.with_stdout   -- warning: with after non-with statement
do_work()
```

The grammar permits `with` anywhere in a block, but the linter
enforces contiguous placement. This keeps scoping predictable —
readers can see the full handler stack at a glance.

**Typing rules:**

`with expr` requires `expr` to be a function application missing
its last `@with` argument, where that argument has function type.
The compiler inserts the generated callback as the final argument.

For `with expr` (non-binding): the missing last argument must
have type `() -[e1]> T` for some effects `e1` and return type `T`.

For `with pattern <- expr` (binding): the missing last argument
must have type `(A) -[e1]> T` for some `A`, effects `e1`, and
return type `T`. The bound pattern has type `A`.

The desugared program is what gets type-checked. `with` introduces
no special effect behavior — the callback's effect row is inferred
normally. All existing inference and diagnostics apply to the
desugared form.

**Scope:** `with` captures everything after it until the end of
the enclosing block (indentation level). Multiple `with`
statements in sequence nest from top to bottom (outermost first).

```kea
let config = load_config()
with Logging.with_stdout
with conn <- Db.with_connection(config.db)
-- config is visible here (captured by the callback)
-- conn is bound by the with
query(conn, "SELECT 1")
```

### 10.7 While Loops

```kea
while condition
  body
```

`while` is syntactic sugar for tail-recursive iteration. The above
desugars to:

```kea
let rec loop () =
  if condition
    body
    loop ()
loop ()
```

`while` has type `Unit`. It is a statement, not an expression.
For accumulating results, use explicit recursion or `.fold()`.

`while` exists for clarity in imperative-style code inside
`Unique` blocks and effect handlers. It does not introduce
mutable state — the loop condition must change via effects
(e.g., `State`) or by consuming a data structure.

### 10.8 Tail Call Optimization

The compiler optimizes direct tail calls (a function calling
itself in tail position) into loops. This is guaranteed for
self-recursive functions.

**`@tailrec` annotation:** Opt-in verification that a recursive
call is in tail position. If the annotated call is not actually
a tail call, the compiler emits an error.

```kea
fn sum(xs: List Int, acc: Int) -> Int
  case xs
    [] -> acc
    [x, ..rest] -> @tailrec sum(rest, acc + x)
```

```
error: @tailrec call is not in tail position
  --> src/list.kea:4:25
   |
4  |     [x, ..rest] -> @tailrec sum(rest, acc + x) + 1
   |                     ^^^^^^^ this call has `+ 1` after it
```

`@tailrec` is applied at the call site, not the function
definition. This makes it explicit which recursive calls the
programmer expects to be optimized.

Mutual tail calls (A calls B calls A) are not guaranteed to be
optimized in the bootstrap compiler. `@tailrec` on a mutual
call is a compile error until mutual TCO is implemented.

---

## 11. Modules

### 11.1 One File, One Module

Each `.kea` file defines exactly one module. The file path determines
the module name:

```
src/http/server.kea   → Http.Server
src/app.kea           → App
```

Multiple structs per file are allowed. The file path defines the
module name; struct names are independent of the file name.

### 11.2 Imports

```kea
use Http.Server
use Http.Client.{get, post}
use Trees.Tree.{Leaf, Branch}
```

`use` brings names into scope. Selective imports with `{}` import
specific items.

### 11.3 Visibility

`pub` marks items as public. Everything without `pub` is module-private.

```kea
pub struct User
  pub name: String    -- field visible outside module
  email: String       -- field private to module
```

### 11.4 No Circular Dependencies

Module imports form a DAG. Circular imports are a compile error.

### 11.5 Type Aliases

```kea
type Handler = Request -[IO]> Response
type Middleware = (Handler, Request) -[IO]> Response
type Pairs A = List (String, A)
```

Type aliases are purely syntactic. The compiler expands them at every
use site. They introduce no new nominal type and cannot have trait
implementations.

Aliases may be parameterised. They may not be recursive.

**Effect row aliases.** Type aliases may name effect rows using
bracket syntax. An effect alias expands to an effect set wherever
an effect annotation is expected:

```kea
type DbEffects = [IO, Fail DbError]
type WebEffects = [IO, Fail AppError, Log]

fn query(_ sql: String) -DbEffects> Rows
-- expands to: fn query(_ sql: String) -[IO, Fail DbError]> Rows

fn serve(_ req: Request) -WebEffects> Response
-- expands to: fn serve(_ req: Request) -[IO, Fail AppError, Log]> Response
```

Effect aliases may be parameterised and may include row tails:

```kea
type Failable E = [Fail E]
type WithDb e = [IO, Fail DbError, e]

fn load(_ id: Id) -WithDb e> Entity
-- expands to: fn load(_ id: Id) -[IO, Fail DbError, e]> Entity
```

Effect aliases compose by union. Using multiple aliases in one
annotation merges them:

```kea
type Logs = [Log]
type Stores = [IO, Fail DbError]

fn process(_ x: Input) -[Logs, Stores]> Output
-- expands to: fn process(_ x: Input) -[Log, IO, Fail DbError]> Output
```

Effect aliases are purely syntactic — the compiler expands them
before type checking. They do not create new effects or change
the effect algebra. They exist so that common effect bundles
(like "all the effects a database layer needs") can be named
once and reused.

---

## 12. Memory Model

### 12.1 Immutable Values

All values are semantically immutable. There is no mutable state.
Actor state changes are modeled as producing new values (§19).

The optimisations in §12.3, §12.5, and §12.6 may cause mutation
of the underlying representation. This is unobservable — the
semantics are always immutable. A correct program cannot distinguish
between a copied value and an in-place-mutated value.

### 12.2 Reference Counting

Heap-allocated values use reference counting for memory management.
When a reference count reaches zero, the value is immediately
deallocated. There is no garbage collector.

Cycles are not automatically collected. Cyclic data structures
cannot arise from immutable values (you cannot construct a value
that references itself). Actor references (`Ref M`) do not
participate in reference counting — they are managed by the
actor runtime.

### 12.3 Copy-on-Write

Functional update (`~`) checks the reference count at runtime. If
the count is 1 (sole owner), the update is performed in-place.
Otherwise, the value is copied. This is unobservable — semantics
are always immutable.

### 12.4 Stack vs Heap

- Stack: primitives, small structs, unboxed closures.
- Heap: large structs, strings, collections, enum variants with fields.

The threshold for stack allocation is implementation-defined.

### 12.5 Reuse Analysis

The compiler performs static analysis to determine where a value's
reference count is guaranteed to be 1 at a given program point.
Where this can be proven:

- Functional update (`~`) skips the runtime refcount check and
  performs unconditional in-place mutation.
- Deallocation of a consumed value and allocation of a replacement
  value may be fused (reuse). The memory from the old value is
  rewritten rather than freed and reallocated.

**Drop before last use.** When a value is consumed (pattern matched,
passed to a function) and never referenced again, the compiler may
insert a drop before the consuming operation. This ensures the
refcount reaches 1 at the consumption point, enabling reuse.

**Reuse tokens.** When a value is dropped and the subsequent
operation allocates a value of the same size and layout, the
compiler may reuse the dropped value's memory directly.

These optimisations are always unobservable. They are performed
as part of the MIR-to-backend lowering and require no programmer
annotation. They apply to all values, not only `Unique`-wrapped
values (§12.6).

### 12.6 Unique T

`Unique T` is a type wrapper that provides a compile-time guarantee
of single ownership. A value of type `Unique T` has exactly one
reference. The compiler enforces this through move semantics: using
a `Unique T` value moves it, and subsequent references to the
moved binding are compile errors.

`Unique` is defined in the standard library, not the language
syntax. The compiler has built-in knowledge of `Unique` for
move checking.

**Construction:**

```kea
let buf = Unique Buffer { data: Bytes.alloc(1024), len: 0 }
```

Wrapping a newly constructed value in `Unique` asserts sole
ownership. The compiler verifies that the inner value is freshly
constructed (not aliased).

**Consumption (move semantics):**

```kea
let buf2 = buf.append(chunk)    -- buf is moved, buf2 is the new owner
-- buf is no longer accessible here — compile error if referenced
```

A function that takes `Unique T` as a parameter consumes it.
The caller may not reference the value after the call. Functions
that transform unique values return `Unique T` to preserve the
uniqueness chain.

**Borrowing (non-consuming access):**

```kea
fn length(borrow self: Unique Buffer) -> Int
  self.len
```

The `borrow` parameter convention grants temporary read access
to a `Unique T` value without consuming it. The caller retains
ownership after the call returns.

Rules for `borrow`:
1. The callee may read fields and call other `borrow` functions
   on the borrowed value.
2. The callee may not store, return, or capture the borrowed
   reference in a closure that outlives the call.
3. The callee may not pass the borrowed value to a function that
   takes `Unique T` (which would consume it).
4. Multiple `borrow` parameters from different unique values are
   permitted in the same call.
5. `borrow` may also be used on non-unique values as an
   optimisation hint: it tells the compiler that the callee will
   not increment the refcount.

**Freezing (dropping uniqueness):**

```kea
fn freeze(_ self: Unique T) -> T
```

`freeze` consumes the `Unique T` and returns a regular `T`. The
value becomes refcounted from this point. This is a zero-cost
operation — the runtime representation is identical. `freeze` is
a generic function available for all `Unique T`.

**Claiming (acquiring uniqueness):**

```kea
fn try_claim(_ self: T) -> Option (Unique T)
```

`try_claim` checks the reference count at runtime. If it is 1,
the value is wrapped in `Unique` and returned as `Some`. If it is
greater than 1, returns `None`. This is the only runtime check
in the uniqueness system.

**Unique fields in structs:**

Structs may contain `Unique T` fields:

```kea
struct Builder
  buffer: Unique Buffer
  count: Int
```

A struct containing unique fields is itself subject to move
semantics when the unique field is accessed or updated:

```kea
let b2 = b~{ buffer: new_buf }
-- b is consumed: its unique field was moved out
-- b2 is the new owner of new_buf
```

Functional update on a struct with unique fields moves the
replaced unique fields out (dropping or reusing them) and moves
the new values in. The old binding is consumed. Accessing a
unique field by name (`b.buffer`) is a move unless the access
is in `borrow` context.

**Unique values in collections:**

`Unique T` may appear as an element type in collections:
`List (Unique T)`, `Map K (Unique T)`. Operations that access
elements (indexing, iteration) yield `borrow` references by
default. Operations that remove elements (pop, drain) yield
owned `Unique T` values.

**Actor messages:**

`Unique T` values may be sent as actor messages. Sending moves
the value — the sender loses access:

```kea
Send.tell(ref, TransferOwnership(unique_buf))
-- unique_buf is consumed, receiver gets sole ownership
```

`borrow` references may NOT appear in actor messages. A borrow
is valid only for the duration of a synchronous call. Actor
messages are asynchronous. This is a compile error.

**Interaction with effects:**

`Unique` is orthogonal to effects. A function may have any
combination:

```kea
fn pure_transform(_ b: Unique Buffer) -> Unique Buffer
fn io_write(_ b: Unique Buffer) -[IO]> Unique Buffer
fn send_buffer(_ b: Unique Buffer) -[Send]> Unit
```

The effect signature describes what the function does. The
uniqueness of the parameter describes ownership transfer.
These are independent dimensions.

**Compiler guarantees for Unique T:**

When a value is `Unique T`, the compiler:
1. Elides all refcount checks for operations on that value.
2. Performs unconditional in-place mutation for functional updates.
3. Emits no retain/release pairs for `borrow` parameters.
4. May fuse deallocation and reallocation (reuse) without analysis,
   since single ownership is guaranteed by the type.

### 12.7 Arena Allocation

Arena allocation in Kea is expressed through the `Alloc` effect
(§5.9). The `Alloc` effect redirects heap allocations to a
region-based bump allocator. The effect handler (`with_arena`)
manages the arena lifecycle: creation, allocation, return-value
copy, and bulk deallocation.

The arena is invisible to code inside the effect. All standard
Kea allocation — struct construction, collection operations,
closure creation — is served by the arena when `Alloc` is in
the effect set. No special syntax or explicit arena handles are
required.

**Performance characteristics:**

| Operation | Refcounted heap | Arena (`Alloc`) |
|---|---|---|
| Allocate | General-purpose allocator | Pointer bump (one instruction) |
| Deallocate | Individual, on refcount drop | Bulk, on `with_arena` return |
| Refcount overhead | Per-value retain/release | None for arena-internal values |
| Return value | Already in caller's context | Copied at `with_arena` boundary |

Arena allocation is most beneficial for allocation-heavy passes
that produce a result much smaller than their intermediaries:
compiler passes, data transformations, query planning, tree
rewriting.

**Arenas and Unique:** `Unique T` inside an `-[Alloc]>` function
gives the strongest performance guarantees: zero refcount checks
(from `Unique`) combined with bump allocation (from `Alloc`).
Functional updates on unique arena-allocated values are
unconditional in-place mutations with no allocation overhead.

**Low-level arena access:** For cases that require explicit
arena management (custom allocators, FFI, data structure
internals), a low-level `Arena` struct is available in the
standard library with `Unique` ownership and `Ptr T` access
(§17.2, §17.3). Most code should use the `Alloc` effect
instead.

### 12.8 Layout Annotations

`@unboxed` guarantees a struct is always stack-allocated and
passed by value, with no heap indirection and no refcount:

```kea
@unboxed
struct Vec3
  x: Float32
  y: Float32
  z: Float32
```

Rules for `@unboxed`:
1. All fields must be primitives, fixed-width numerics, or
   other `@unboxed` types.
2. No recursive or self-referential types.
3. Size must be known at compile time.
4. Cannot be heap-allocated. Not refcounted. Copied on
   assignment (value semantics, always).
5. Can implement traits and have inherent methods normally.

`@unboxed` types are primarily for FFI structs, SIMD-friendly
layouts, and performance-critical inner loops where indirection
costs matter.

---

## 13. Built-in Operators

### 13.1 Operator Table

| Operator           | Types          | Description                |
|--------------------|----------------|----------------------------|
| `+`, `-`, `*`, `/` | `Additive`/`Numeric` | Arithmetic           |
| `%`                | `Int`          | Remainder                  |
| `==`, `!=`         | `Eq`           | Equality                   |
| `<`, `>`, `<=`, `>=`| `Ord`         | Ordering                   |
| `&&`, `\|\|`       | `Bool`         | Short-circuit logic        |
| `!`                | `Bool`         | Negation                   |
| `++`               | `Concatenable` | Concatenation              |
| `<>`               | `Monoid`       | Monoidal combine           |
| `~`                | Struct/row     | Functional update          |
| `?`                | `Result T E`   | Error propagation          |

### 13.2 Operator Desugaring

Operators desugar to trait method calls:

- `a + b` → `Additive.add(a, b)`
- `a * b` → `Numeric.mul(a, b)`
- `a == b` → `Eq.eq(a, b)`
- `a < b` → `Ord.lt(a, b)`
- `a ++ b` → `Concatenable.concat(a, b)`
- `a <> b` → `Monoid.combine(a, b)`

`and`, `or`, and `not` are short-circuit/built-in for `Bool` only
and do NOT desugar to trait calls. `&&`, `||`, and `!` are rejected
by the parser with messages directing to the keyword forms.

### 13.3 Three-Operator Algebra for Combining Values

Three operators with distinct intent:

- `+` for numeric addition (`Additive`): `1 + 2`, `3.0 + 4.0`
- `++` for ordered concatenation (`Concatenable`): `"a" ++ "b"`,
  `[1, 2] ++ [3, 4]`
- `<>` for monoidal combine (`Monoid`): `map1 <> map2`

`"hello" + " world"` is a type error. `+` is strictly numeric.

### 13.4 No Pipe Operator

There is no `|>` pipe operator. Method syntax with UMS (§9)
provides left-to-right chaining:

```kea
-- Instead of: data |> f(x) |> g(y)
-- Write:      data.f(x).g(y)
```

`$` placement (§9.3) handles cases where the receiver is not the
first argument, which is the only case where pipes would have been
useful beyond what method syntax provides.

---

## 14. Annotations

| Annotation           | Meaning                                 |
|----------------------|-----------------------------------------|
| `@pure`              | Compiler-verified purity assertion      |
| `@inline`            | Inlining hint                           |
| `@unboxed`           | Stack-only, value-type layout (§12.8)   |
| `@unsafe`            | Unsafe function (§17.2)                 |
| `@deprecated(msg)`   | Deprecation warning on use              |
| `@derive(Trait, ..)` | Generate trait implementations          |
| `@test`              | Mark function as test                   |
| `@extern("lang")`    | FFI binding (§17.1)                     |

**`@pure` and effect arrows:** The `->` arrow already denotes purity.
`@pure` is an explicit assertion that a function with *inferred*
effects must be pure. If the compiler infers any semantic effects
(IO, Send, Spawn), and `@pure` is present, this is a compile error.

`@pure` on a function with an explicit `->` arrow is redundant but
permitted (no error, no warning). `@pure` on a function with an
explicit `-[IO]>` arrow is a compile error (contradiction).

`@pure` is primarily useful for public API boundaries where the
author wants to guarantee purity even if the implementation changes,
and for recipe annotations where purity is a precondition for
specialised lowering (§15.2).

---

## 15. Compiler Recipes (Overview)

The compiler's HIR and MIR are Kea types. Compiler passes are pure
Kea functions that transform these types. `@derive` is implemented
as a compiler recipe.

### 15.1 IR Stability Tiers

| Tier           | Audience          | Stability                        |
|----------------|-------------------|----------------------------------|
| **StableHIR**  | Recipe authors    | Versioned, row-extensible        |
| **UnstableMIR**| Power users       | May break between minor versions |
| **InternalIR** | Compiler devs     | Private, no stability promise    |

Recipes targeting StableHIR should use row-polymorphic interfaces
to remain forward-compatible when the compiler adds new IR nodes.

### 15.2 Restricted Sublanguages

Domain-specific compilation targets (GPU compute, DataFusion,
FPGA synthesis) may require a restricted subset of the language —
no closures, no recursion, no heap allocation — to enable
lowering to specialised backends (e.g. MLIR, StableHLO, SQL).

These restricted sublanguages are introduced by recipes, not by
the core language. A recipe can validate that a function body
conforms to a restricted grammar and then lower it through a
custom backend pipeline. The `@pure` annotation verifies effect
purity; a recipe annotation (e.g. `@gpu`, `@sql`) can additionally
verify structural restrictions.

This is a post-v0 capability. The recipe system (§15) provides
the extension point; the KERNEL does not define specific restricted
sublanguages.

---

## 16. Packages (Overview)

### 16.1 Manifest

```toml
[package]
name = "my_app"
version = "0.1.0"

[dependencies]
http = "0.1"
```

### 16.2 Resolution

Minimal version selection. `kea.lock` pins exact versions.

### 16.3 Import Resolution Order

1. Standard library (`Kea.*`)
2. Package modules (`_deps/`)
3. Project modules (`src/`)

Project modules shadow package modules with a warning.

### 16.4 Types Flow, Imports Don't

Types from transitive dependencies flow through return values.
Calling a transitive dependency's functions requires declaring
it as a direct dependency.

---

## 17. FFI

### 17.1 External Functions

```kea
@extern("c")
fn write(_ fd: Int32, _ buf: Ptr UInt8, _ count: UInt64) -[IO]> Int64

@extern("rust")
fn cranelift_compile(_ module: Ptr UInt8, _ len: UInt64) -[IO]> Ptr UInt8
```

FFI functions always have at least the `IO` effect. The compiler
cannot verify the purity or safety of foreign code.

**Calling convention:** `@extern("c")` uses the C ABI.
`@extern("rust")` uses the Rust ABI. Other conventions may be
added. The convention string determines how Kea types are
marshalled at the boundary.

**Type marshalling:**

| Kea type    | C ABI                    |
|-------------|--------------------------|
| `Int8..64`  | `int8_t..int64_t`        |
| `UInt8..64` | `uint8_t..uint64_t`      |
| `Float`     | `double`                 |
| `Float32`   | `float`                  |
| `Bool`      | `_Bool` / `uint8_t`      |
| `Ptr T`     | `T*`                     |
| `Unit`      | `void` (return only)     |

`String`, `Bytes`, `List`, and other managed Kea types cannot
be passed directly to FFI. They must be converted to `Ptr UInt8`
plus length at the call boundary.

### 17.2 Unsafe

Kea provides a scoped unsafe mechanism for operations the type
system cannot verify: raw pointer arithmetic, unchecked casts,
manual memory management.

**`@unsafe` functions:**

```kea
@unsafe
fn read_u32_at(_ ptr: Ptr UInt8, _ offset: Int) -> UInt32
  let target = ptr.offset(offset)
  Ptr.read(target.cast())
```

An `@unsafe` function may use unsafe primitives (§17.3).
Calling an `@unsafe` function from safe code requires an
`unsafe` block:

```kea
fn parse_header(_ data: Bytes) -[Fail ParseError]> Header
  let ptr = data.as_ptr()
  let magic = unsafe read_u32_at(ptr, 0)
  if magic != 0x4B454121
    fail ParseError.invalid_magic(magic)
  -- ...
```

The `unsafe` block is an expression. It marks the boundary where
the programmer takes responsibility for invariants the compiler
cannot check. The block's result type and effects are the same
as the contained expression.

**Audit rule:** Every use of unsafe is visible in source as
either an `@unsafe` annotation or an `unsafe` block. A codebase
search for `unsafe` finds every boundary.

### 17.3 Ptr T

`Ptr T` is a raw, unmanaged pointer to a value of type `T`.
It does not participate in reference counting. The programmer
is responsible for ensuring the pointed-to memory is valid.

`Ptr T` may only be used inside `@unsafe` functions or `unsafe`
blocks, with one exception: `Ptr T` values may be *held* in
safe code (as opaque handles for FFI), but may not be
dereferenced, offset, or cast outside of unsafe context.

**Operations (all require `@unsafe` or `unsafe` block):**

| Operation | Signature | Description |
|---|---|---|
| `Ptr.read` | `(_ p: Ptr T) -> T` | Dereference: read value at pointer |
| `Ptr.write` | `(_ p: Ptr T, _ val: T) -> Unit` | Write value at pointer |
| `Ptr.offset` | `(_ p: Ptr T, _ n: Int) -> Ptr T` | Advance pointer by `n * size_of(T)` bytes |
| `Ptr.cast` | `(_ p: Ptr A) -> Ptr B` | Reinterpret pointer type |
| `Ptr.null` | `() -> Ptr T` | Null pointer |
| `Ptr.is_null` | `(_ p: Ptr T) -> Bool` | Null check (safe) |
| `Ptr.alloc` | `(_ count: Int) -> Ptr T` | Allocate raw memory |
| `Ptr.free` | `(_ p: Ptr T) -> Unit` | Free raw memory |

**`Ptr.is_null` is the only safe operation on `Ptr T`.** All
others require unsafe context.

**Interaction with Unique:** `Ptr T` is orthogonal to `Unique`.
`Ptr` is unmanaged memory — no refcount, no CoW, no compiler
guarantees. `Unique` is managed memory with a compile-time
ownership guarantee. They serve different purposes and should
not be confused:

| | Managed (`T`, `Unique T`) | Unmanaged (`Ptr T`) |
|---|---|---|
| Refcounted | Yes (`T`) / No but tracked (`Unique T`) | No |
| Safe | Yes | Only in `@unsafe` |
| GC/drop | Automatic | Manual |
| Use case | Application code | FFI, data structure internals |

---

## 18. Error Model

There are no exceptions. All errors are values.

- Recoverable errors: `Result T E` or equivalently `Fail E` effect.
- Unrecoverable errors: `panic` (terminates the actor or program).

`panic` is not catchable in normal code. Actor supervisors may
observe a panic through the supervision protocol.

---

## 19. Actors (Library)

Actors are entirely a library concern (`kea-actors`). The language
provides the effect system (§5) and GADTs (§3, §4.4); the library
builds actors on top of them. There are no actor-specific language
primitives, operators, or syntax.

### 19.1 Effects (Library-Defined)

The actor library defines two effects:

```kea
effect Send
  fn tell(_ ref: Ref M, _ msg: M Unit) -> Unit
  fn ask(_ ref: Ref M, _ msg: M T) -> T

effect Spawn
  fn spawn(_ actor: A, _ config: A.Config) -> Ref A.Msg where A: Actor
```

`Send.tell` sends a fire-and-forget message (the GADT return type
must be `Unit`). `Send.ask` sends a message and suspends until the
response arrives, returning the response type `T` from the GADT.
`Spawn.spawn` creates a new actor and returns a typed ref.

These are ordinary effects. They are handled by the actor runtime,
which the library provides. In tests, they can be handled by mock
handlers.

### 19.2 Ref M

`Ref M` is an opaque handle to an actor that accepts messages of
protocol `M`. `M` is a GADT whose type parameter encodes response
types. `Ref` is parameterised by the message protocol, not by the
actor's internal state.

```kea
fn notify(_ counter: Ref CounterMsg) -[Send]> Unit
  Send.tell(counter, Increment)
  Send.tell(counter, Increment)
  let count = Send.ask(counter, Get)
  IO.stdout("Count is {count}")
```

`Send.tell` only accepts messages whose GADT return type is `Unit`.
Silently discarding a response is a type error. To send and
explicitly discard: `let _ = Send.ask(ref, msg)`.

### 19.3 Actor Trait

```kea
trait Actor
  type Msg _             -- GADT message protocol (takes one type parameter)
  type Config
  fn init(_ config: Self.Config) -> Self
  fn handle(_ self: Self, _ msg: Self.Msg T, _ reply: T -> Unit) -[Send]> Self
```

`handle` receives the message and a `reply` callback. The actor
calls `reply(value)` to send the response back to the caller.
This decouples *when* the reply happens from message processing.

**Immediate reply** — the common case:

```kea
fn handle(_ self: Self, _ msg: CounterMsg T, _ reply: T -> Unit) -[Send]> Self
  match msg
    Increment ->
      reply(())
      self~{ count: self.count + 1 }
    Get ->
      reply(self.count)
      self
```

**Deferred reply** — store the callback, reply later:

```kea
fn handle(_ self: Self, _ msg: PoolMsg T, _ reply: T -> Unit) -[Send]> Self
  match msg
    Acquire ->
      match self.available
        conn :: rest ->
          reply(conn)
          self~{ available: rest }
        [] ->
          -- Park the caller; reply when a connection is returned
          self~{ waiting: self.waiting ++ [reply] }
    Release(conn) ->
      match self.waiting
        next :: rest ->
          next(conn)   -- reply to the parked caller
          self~{ waiting: rest }
        [] ->
          self~{ available: self.available ++ [conn] }
```

This maps to OTP's `From` parameter in `handle_call`. The caller
blocks on `Send.ask` until `reply` is called — whether that
happens immediately in the same `handle` invocation, or later
when another message triggers it.

**Fire-and-forget** — for `M ()` messages sent via `tell`, the
runtime inserts `reply(())` automatically if `handle` returns
without calling `reply`. This is a convenience; explicit
`reply(())` is also valid.

`handle` may have the `Send` effect (messaging other actors).
It may not have `IO`. Side effects in handlers happen through
messages to dedicated IO actors.

### 19.4 GADT Message Protocols

```kea
enum CounterMsg T
  Increment   : CounterMsg ()
  Decrement   : CounterMsg ()
  Get         : CounterMsg Int
```

The GADT parameter `T` encodes the response type. The type system
ensures:
- `tell` only works with `M Unit` messages
- `ask` returns the exact type `T` for the specific message
- The `reply` callback in `handle` has type `T -> Unit`, matching
  the message's `T` — calling `reply` with the wrong type is
  a compile error

### 19.5 Supervision (Library)

The supervisor protocol uses opaque `ChildId` handles. Supervisors
do not need to know children's message types — they only observe
lifecycle events (started, stopped, crashed).

Restart strategies (OneForOne, OneForAll, RestForOne) and maximum
restart intensity are library-level configuration.

### 19.6 Registry (Library)

A typed actor registry is a supervised actor that maps types to refs.
Actors register by type; lookup returns a typed `Ref M`:

```kea
let store = Registry.get(Todo.Store)   -- : Ref Todo.Msg
```

`Registry.get(A)` returns `Ref A.Msg` where `A: Actor`. The type
system guarantees the ref matches the actor's protocol. No string
keys, no casting, no `Any`.

---

## Appendix A: Reserved Words

```
struct  enum  trait  effect  fn   let   const  match  if  then  else
where   use   pub   as   self  Self   true   false
type    fail  catch  for  in  handle  resume  unsafe  borrow  with
```

31 reserved words.

## Appendix B: Tokens

```
-- line comment             --| doc comment
:  type annotation          :: list cons pattern
-> pure arrow               -[e]> effectful arrow
~  functional update        $  receiver placement
?  error propagation        @  annotation
++ concatenation            <> monoidal combine
.. spread/rest (in patterns)
<- with-binding              (in with expressions)
{  }  struct/row literal    [  ]  list literal
(  )  grouping/tuple        ,  separator
=  binding                  |  lambda parameter delimiter
#{ }  anonymous record
```

## Appendix C: Prelude Traits

The following traits are in scope in every module without explicit
`use` declarations:

```
-- Core
Show  Eq  Ord  From  Codec

-- Numeric
Additive  Numeric

-- Combining
Concatenable  Monoid

-- Collections
Enumerable  Iterator  Foldable  Filterable
```

These traits are available for unqualified method dispatch (§9.1)
in all modules. Additional traits require explicit `use` to bring
their methods into scope.

## Appendix D: Standard Trait Hierarchy (Informative)

```
Eq
Ord : Eq
Show
From T
Codec

Additive          -- (+), zero
Numeric : Additive -- (*), (/)

Concatenable      -- (++)
Monoid            -- (<>), empty

Enumerable        -- to_seq
Iterator          -- next
Foldable          -- fold, sum, any, all, find
Filterable        -- filter

-- No HKT traits (Functor, Monad, etc.) — effects replace monadic
-- composition. Collection traits above work on concrete types
-- (Self = List Int, not List). map is an inherent method.
```

---

*Kea: clever, small, unexpectedly powerful.*
