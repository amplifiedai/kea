# The Compiler as Data

Most languages have a compiler and a language. They're separate things.
The compiler is a program that reads your code and produces a binary.
The language is what you write. The compiler is privileged — it can do
things your code can't.

Kea eliminates this distinction.

---

## The compiler's IR is a Kea type

When Kea self-hosts, the compiler's intermediate representations —
the data structures it uses internally to represent your program as
it transforms source code into machine code — are Kea types:

```kea
type HirExpr =
  Let { name: String, value: HirExpr, body: HirExpr }
  | If { cond: HirExpr, then_branch: HirExpr, else_branch: HirExpr }
  | Call { func: HirExpr, args: List HirExpr }
  | Lit { value: Literal }
  | Handle { body: HirExpr, clauses: List HandlerClause }
  | ...
```

This isn't a simplified representation exposed for tooling. It's the
actual IR the compiler operates on. And because it's a Kea type, you
get everything Kea gives any type:

- **Pattern matching is exhaustive.** Write a function over `HirExpr`
  and the compiler verifies you handled every case. Add a new IR node
  and every function that forgot to handle it becomes a compile error.
- **Row polymorphism gives forward compatibility.** A recipe that
  handles `Let`, `If`, and `Call` passes everything else through via
  a row variable. When the compiler adds `Handle` in a later release,
  existing recipes don't break.
- **The effect system tracks what passes do.** A pure optimization
  has `->`. A pass that emits diagnostics has `-[Compile]>`. You can
  read a pass's signature and know whether it just transforms IR or
  does something more.

Compare this to Zig's comptime, which gives you type metadata but not
the program's IR. Or Rust's proc macros, which give you token streams
with no type information. Or Lisp macros, which give you untyped
s-expressions. Kea gives you the **typed, effect-annotated
intermediate representation** of the program itself, as a value you
can pattern-match on, transform, and hand back.

---

## Every tool is a handler

A compiler pipeline is an effectful computation:

```
Source -[Compile]> HIR -[Compile]> MIR -[Compile]> Target
```

Each stage is a pure function under the `Compile` effect. What makes
this powerful is that different tools are just **different handlers**
for the same pipeline:

```
Compiler  = handle pipeline with Cranelift backend handler
LSP       = handle pipeline with "emit diagnostics + spans" handler
MCP       = handle pipeline with "return types as JSON" handler
REPL      = handle pipeline with "JIT and eval" handler
Formatter = handle parse stage with "emit formatted source" handler
Linter    = handle pipeline through HIR with "emit lint warnings" handler
```

These aren't different programs that reimplement parts of
compilation. They're **the same program with different handlers.**
The compilation logic exists exactly once. Each tool is a handler
composition over that logic.

This is where effects make the architecture structural rather than
aspirational. Every language project starts with "one semantic
engine powering all tools." Most end up with the compiler and the
language server as separate programs that drift apart. Rust has
rustc and rust-analyzer — two different type checkers. Go maintained
two separate type checkers for years. TypeScript's compiler and
language service share code but have different entry points and
different caching strategies.

The reason this happens is that tools have different requirements
(the LSP needs incrementality, the compiler needs throughput, the
REPL needs interactivity) and without a composition mechanism, the
only way to meet different requirements is different implementations.

Effects *are* that composition mechanism. The pipeline stages stay
the same. The handlers change. And because effects are tracked in
the type system, you can **prove** that the formatter doesn't depend
on type information (it only handles the parse stage), that the
linter doesn't need codegen (it stops at HIR), and that the REPL
handler doesn't touch the filesystem (it JITs in memory). The
boundaries between tools aren't conventions — they're types.

---

## Grammar blocks embed languages, not syntax

`embed <Grammar> { ... }` doesn't paste tokens into the host
language. It invokes a full compilation pipeline for a different
language:

```kea
trait Grammar
  type Ast
  type Out
  type Err

  fn parse(src: String) -[Compile]> Result(Self.Ast, Self.Err)
  fn check(ast: Self.Ast, ctx: GrammarCtx) -[Compile]> Result(Typed(Self.Out), Diag)
  fn lower(typed: Typed(Self.Out)) -[Compile]> LoweredExpr
```

The grammar defines parsing, type-checking, and lowering — the same
three stages the Kea compiler itself has. `check` runs inside the
host type system via `GrammarCtx`, so types flow between the embedded
language and the host. `lower` produces Kea IR, which then flows
through the rest of the compilation pipeline.

This means:

**SQL is type-checked at compile time:**

```kea
let users = embed Sql {
  SELECT name, age FROM users WHERE active = {is_active}
}
-- users : List { name: String, age: Int }
-- {is_active} is a parameterised binding, not string interpolation
-- SQL injection is structurally impossible
```

The `Sql` grammar's `check` step introspects the database schema at
compile time (under the `Compile` effect) and produces a return type
that is the exact row type of the selected columns.

**HTML templates are component-typed:**

```kea
let page = embed Html {
  <div class={style}>
    <UserCard user={current_user} />
  </div>
}
```

The `Html` grammar checks that `class` expects `String`, that
`UserCard` is a component whose `user` prop accepts the type of
`current_user`. All at compile time, zero runtime cost.

**GPU kernels are validated and lowered to a different target:**

```kea
@gpu
fn matmul(a: Matrix Float, b: Matrix Float) -> Matrix Float
  -- body must conform to GPU-restricted grammar:
  -- no closures, no recursion, no heap allocation
```

The `@gpu` recipe validates the function body against a restricted
grammar, then lowers through a GPU-specific backend (MLIR,
StableHLO, PTX). Same mechanism as SQL and HTML.

---

## Any language, any compilation path

Here is the insight that connects everything.

The Grammar trait defines a language: parsing, type-checking, and
lowering. The recipe system routes IR through different backends.
The handler mechanism lets you compose these arbitrarily.

So `embed Lua { ... }` isn't "Kea with Lua syntax." It's a Grammar
implementation that:

1. **Parses** actual Lua syntax
2. **Type-checks** at the Kea boundary — Lua values crossing into
   Kea are typed, Kea values crossing into Lua are validated
3. **Lowers** to whatever target makes sense — a Lua interpreter,
   a JIT, or native code via a Lua-to-MIR lowering

The embedded language retains its own semantics. It doesn't get
rewritten into Kea. It goes through its own compilation pipeline,
touching the host only at typed boundaries. And the `Compile`
effect ensures the whole process is sandboxed — no filesystem
access, no network, no ambient IO unless explicitly granted.

This generalises. A `@sql` recipe validates a restricted subset
of Kea and lowers to SQL. A `@gpu` recipe validates a different
subset and lowers to SPIR-V. A `@wasm` recipe targets WebAssembly.
Each defines a Grammar (the restricted subset it accepts) and a
Backend (the target it lowers to). Same trait, same mechanism.

The embed block defines **the language.** The recipe chain defines
**the compilation strategy.** The handler at the end defines **the
target.** And the effect system ensures these three concerns compose
without leaking into each other.

---

## Row polymorphism makes it sustainable

The reason this doesn't collapse under its own weight is row
polymorphism. When the compiler adds a new IR node — say, `Await`
for async — every existing recipe, grammar, and backend that uses
a row variable absorbs it automatically:

```kea
fn simplify(expr: HirExpr { Let: _, If: _, Call: _ | r })
    -> HirExpr { Let: _, If: _, Call: _ | r }
  -- handles Let, If, Call
  -- Await passes through r unchanged
```

This is the same mechanism that makes effect rows extensible (add
a new effect, existing handlers pass it through) and record types
extensible (add a new field, existing functions still work). Applied
to the compiler's IR, it means:

- **Recipes are forward-compatible.** New language features don't
  break existing compiler plugins.
- **Grammars are extensible.** An HTML grammar transformation that
  handles `div` and `span` works unchanged when someone adds
  `dialog` — new tags pass through the row variable.
- **Backends don't need to handle every node.** A GPU backend
  rejects unsupported nodes at validation time and handles only
  the subset it knows about.

StableHIR is versioned with these properties: additive changes
(new IR nodes) are absorbed by row variables. Breaking changes
(removing or modifying nodes) bump the major version. This is
semver, enforced by the type system.

---

## Testing the compiler with the language's own test tools

If compiler passes are pure functions under `Compile`, they're
tested the same way user code is tested — by providing different
handlers:

```kea
test "dead code elimination"
  let input = HirExpr.Let
    name: "x"
    value: HirExpr.Lit(42)
    body: HirExpr.Lit(7)  -- x is never used

  let output = handle Passes.eliminate_dead_code(input)
    Compile.warn(msg) -> resume()  -- silence diagnostics in test

  assert output == HirExpr.Lit(7)
```

No special test harness for compiler internals. No mock compilation
context. The same `handle` mechanism that lets you test user code
with fake IO lets you test compiler passes with fake diagnostics.

---

## What this replaces

| System | What you get | What's missing |
|--------|-------------|----------------|
| Zig comptime | Type metadata at compile time | No access to IR, no row extensibility |
| Rust proc macros | Token stream transformation | Untyped, arbitrary IO, no composition |
| Template Haskell | IO in the Q monad | Uncontrolled effects, no stability tiers |
| Lisp macros | Full program as data | No types, no effect tracking |
| C++ templates | Compile-time computation | No grammar extensibility, poor errors |
| Scala macros | Typed AST access | No row extensibility, complex API surface |

Kea is the first system that gives you typed, effect-tracked access
to the compiler's own IR, with row-polymorphic extensibility and
stability tiers, through the same mechanisms the language provides
for any other data.

---

## When this lands

This is Phase 1-2 work. Phase 0 builds the bootstrap compiler in
Rust with internal IR types. When Kea self-hosts:

1. The Rust `HirExpr` enum becomes a Kea type with row variables
2. Compiler passes become Kea functions under `Compile`
3. `@derive` becomes a recipe consuming StableHIR
4. Backends implement the Grammar trait over MIR
5. LSP, MCP, REPL become handler configurations

The bootstrap compiler is the prototype. The self-hosted compiler
is the product. And the language features that make the self-hosted
compiler possible — effects, handlers, row polymorphism, typed
grammars — are the same features users write application code with.

There is no "compiler magic." There is only Kea.
