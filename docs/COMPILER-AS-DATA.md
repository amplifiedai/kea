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
  has `->`. A pass that emits diagnostics has `-[Diagnose]>`. You can
  read a pass's signature and know whether it just transforms IR or
  does something more.

Compare this to Zig's comptime, which gives you type metadata but not
the program's IR. Or Rust's proc macros, which give you token streams
with no type information. Or Lisp macros, which give you untyped
s-expressions. Kea gives you the **typed, effect-annotated
intermediate representation** of the program itself, as a value you
can pattern-match on, transform, and hand back.

---

## Compilation effects are granular, not monolithic

Kea's thesis is that coarse effects hide capability requirements.
The compiler's own effects are not exempt from this principle.

A monolithic `Compile` effect would give every compilation phase
access to everything — parsing, type-checking, lowering, diagnostics.
But a formatter only needs to parse. A linter needs parsing and type
information but not code generation. A backend needs lowering but not
the type checker. If these distinctions aren't tracked, the "one
semantic engine" promise erodes: tools get more capability than they
need, and nothing prevents a grammar's `parse` method from
accidentally invoking the type checker.

The compilation pipeline decomposes into granular effects:

```kea
effect Parse
  fn source_span() -> Span
  fn report_parse_error(_ err: ParseError) -> Never

effect TypeCheck
  fn resolve_binding(_ name: String) -> Option TypedBinding
  fn unify(_ expected: Type, _ actual: Type) -> Result(Type, TypeError)
  fn current_scope() -> Scope

effect Lower
  fn emit_ir(_ node: LoweredExpr) -> Unit
  fn fresh_name(_ prefix: String) -> String

effect Diagnose
  fn warn(_ msg: String) -> Unit
  fn error(_ msg: String) -> Unit
  fn note(_ msg: String, _ span: Span) -> Unit
```

These are ordinary effects, defined in the compiler's standard
library. They follow the same rules as `IO`, `Log`, `Send` — they're
user-defined, handler-provided, and tracked in the type system.

A compiler pass that only transforms IR without emitting diagnostics
is pure (`->`). A pass that emits warnings has `-[Diagnose]>`. A
pass that needs to resolve types has `-[TypeCheck, Diagnose]>`. The
effect signature is the capability contract — machine-checked, not
convention.

**Consequence for the tool story:** The "every tool is a handler"
architecture now has precise capability boundaries:

```
Formatter = handle parse stage with Parse handler only
Linter    = handle through HIR with Parse + TypeCheck + Diagnose handlers
LSP       = handle through HIR with Parse + TypeCheck + Diagnose + incremental handlers
Compiler  = handle full pipeline with Parse + TypeCheck + Lower + Diagnose + backend handlers
REPL      = handle full pipeline with Parse + TypeCheck + Lower + JIT handler
MCP       = handle through HIR with Parse + TypeCheck + "return types as JSON" handler
```

The formatter's handler signature proves it doesn't depend on type
information. The linter's signature proves it doesn't need codegen.
These boundaries are types, not conventions. And when the compiler
drifts — when someone adds a type-checking call to what should be a
parse-only pass — the effect system catches it at compile time.

---

## Every tool is a handler

A compiler pipeline is an effectful computation:

```
Source -[Parse]> AST -[TypeCheck, Diagnose]> HIR -[Lower]> MIR -[Lower]> Target
```

Each stage declares exactly the effects it needs. What makes this
powerful is that different tools are just **different handlers** for
the same pipeline:

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
on type information (it only handles the `Parse` stage), that the
linter doesn't need codegen (it stops at HIR, never touches `Lower`),
and that the REPL handler doesn't touch the filesystem (it JITs in
memory). The boundaries between tools aren't conventions — they're
types.

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

  fn parse(_ src: String, _ splices: List Splice) -[Parse]> Result(Self.Ast, Self.Err)
  fn check(_ ast: Self.Ast) -[TypeCheck]> Result(Typed(Self.Out), Diag)
  fn lower(_ typed: Typed(Self.Out)) -[Lower]> LoweredExpr
```

The grammar defines parsing, type-checking, and lowering — the same
three stages the Kea compiler itself has. `${expr}` interpolation
points in the embed block are extracted by the Kea parser into typed
`Splice` handles before `parse` is called. Each method declares
exactly the compilation effects it needs:

- **`parse`** runs under `Parse` — it receives the source with
  `${...}` interpolation points extracted into a `Splice` list.
  It can report parse errors and track source spans, but cannot
  access the host type system.
- **`check`** runs under `TypeCheck` — it can resolve host bindings,
  unify types across the grammar boundary, get splice types via
  `TypeCheck.type_of_splice`, and inspect the host scope. Types flow
  between the embedded language and the host through effect
  operations, not through a parameter.
- **`lower`** runs under `Lower` — it produces Kea IR and can
  generate fresh names, but cannot invoke the type checker or parser.

There is no `GrammarCtx` parameter. The `TypeCheck` effect *is* the
context. Where an earlier design would have written
`ctx.resolve_binding("user")`, the grammar's `check` method writes
`TypeCheck.resolve_binding("user")`. The handler — which is the host
compiler's type checker — provides the implementation. This is
cleaner and it's exactly how effects are supposed to replace
parameter-threaded contexts.

This also means different embedded languages that need host type
information — SQL looking up table schemas, HTML checking component
prop types, a GPU grammar validating restricted subsets — all use
the same `TypeCheck` effect operations. The grammar doesn't need to
know *how* host bindings are resolved. It performs the effect. The
handler answers.

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

The `Sql` grammar's `check` step uses `TypeCheck.resolve_binding`
to look up `is_active` in the host scope. It uses `TypeCheck.unify`
to verify the binding's type matches the SQL column type. It
introspects the database schema at compile time (the schema source
is handler-provided) and produces a return type that is the exact
row type of the selected columns.

**HTML templates are component-typed:**

```kea
let page = embed Html {
  <div class={style}>
    <UserCard user={current_user} />
  </div>
}
```

The `Html` grammar's `check` step uses `TypeCheck.resolve_binding`
to look up `style` and `current_user`, then uses `TypeCheck.unify`
to verify that `class` expects `String` and that `UserCard`'s `user`
prop accepts the type of `current_user`. All at compile time, zero
runtime cost.

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

1. **Parses** actual Lua syntax (under `Parse`)
2. **Type-checks** at the Kea boundary (under `TypeCheck`) — Lua
   values crossing into Kea are typed, Kea values crossing into Lua
   are validated
3. **Lowers** to whatever target makes sense (under `Lower`) — a
   Lua interpreter, a JIT, or native code via a Lua-to-MIR lowering

The embedded language retains its own semantics. It doesn't get
rewritten into Kea. It goes through its own compilation pipeline,
touching the host only at typed boundaries. And the decomposed
compilation effects ensure the whole process is capability-bounded —
a grammar's `parse` method cannot access the host type system, and
its `lower` method cannot re-invoke parsing. Each phase does exactly
what its effect signature declares.

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

Row polymorphism handles **additive changes** — new IR nodes, new
fields on existing nodes. This is the common case and it's free.

---

## IR evolution: structure and semantics

Row polymorphism handles additive changes automatically. But IR
evolution isn't always additive. Fields change type. Invariants
tighten or loosen. Semantic contracts shift. Kea uses a layered
defense for these cases.

### Structural changes: version tags

StableHIR carries a version parameter. `HirExpr V2` and
`HirExpr V3` are different types. A recipe targeting V2 won't
typecheck against V3 input. Migration is explicit — you update
your recipe to target V3, which forces you to review the
changelog.

Additive changes (new nodes) are absorbed by row variables
within a version. Breaking structural changes (removing nodes,
changing field types) bump the major version.

### Semantic invariants: validation passes

Structural types don't encode semantic invariants. If V3
requires that `Let` nodes are always in A-normal form (values
are always atomic), a grammar that constructs
`Let { name: "x", value: Call { ... }, body: ... }` is
structurally valid but semantically wrong. No type system
catches this.

The defense is **validation passes** — pure Kea functions over
`HirExpr` that check semantic invariants:

```kea
fn validate_anf(_ expr: HirExpr { Let: _ | r }) -[Diagnose]> Unit
  match expr
    Let { value, .. } ->
      if not value.is_atomic()
        Diagnose.error("Let value must be atomic in ANF")
    other -> ()
```

Validation passes are ordinary functions. They compose. They
run under `Diagnose` (or are pure). They're tested with the
same handler-based infrastructure as any other compiler pass.
The compiler runs them after each transformation to catch
semantic violations early.

This is the same pragmatic tradeoff Kea makes with actors:
static types for structure, runtime checks for semantics,
supervision for recovery. Don't pretend the type system catches
everything.

### Field widening: a direction for revision-preserving evolution

Additive changes (new nodes) and breaking changes (removed nodes,
changed field types) have clear strategies. There's a third
category that's harder: **widening** an existing field's type.

Consider `Let`'s `name` field changing from `String` to `Pattern`
(supporting destructuring), where `String` is a subtype of
`Pattern` (every string is a trivial pattern). This isn't a
breaking change in the traditional sense — all existing `Let`
nodes are still valid. But existing passes that assume `name` is
always `String` will see a wider type.

Row polymorphism doesn't help here — the field's type itself
changed. Version tags force a hard boundary — V2 and V3 are
separate types, and you can't write a function that works on both.

There's a more principled approach, inspired by set-theoretic
type systems (see Dashbit's work on [data evolution with
revisions](https://dashbit.co/blog/data-evolution-with-set-theoretic-types)):
**revision-preserving signatures**. The idea: if each revision's
field types are supertypes of the previous revision, the compiler
can generate function signatures that preserve which revision the
input belongs to. A pass that receives a V2 `Let` (where `name`
is always `String`) returns a V2 `Let`. A pass that receives a V3
`Let` (where `name` might be a destructuring pattern) returns a V3
`Let`. The preservation property is checked automatically.

In a set-theoretic type system, this uses intersection types and
negation. Kea doesn't have those. But the combination of row
polymorphism (for structural extension) and an explicit revision
mechanism (for field widening) could achieve the same practical
guarantees. The revision number serves as the discriminant; the
compiler generates the appropriate match arms.

This is post-v1 design territory. The question only matters once
there's an ecosystem of third-party recipes targeting StableHIR.
But the direction is clear: revisions as a general language
mechanism — not compiler-specific — so that every library gets
the same evolution guarantees the compiler gives itself.

---

## Testing the compiler with the language's own test tools

If compiler passes are pure functions (or functions under
`Diagnose`), they're tested the same way user code is tested —
by providing different handlers:

```kea
test "dead code elimination"
  let input = HirExpr.Let
    name: "x"
    value: HirExpr.Lit(42)
    body: HirExpr.Lit(7)  -- x is never used

  let output = handle Passes.eliminate_dead_code(input)
    Diagnose.warn(msg) -> resume()  -- silence diagnostics in test

  assert output == HirExpr.Lit(7)
```

No special test harness for compiler internals. No mock compilation
context. The same `handle` mechanism that lets you test user code
with fake IO lets you test compiler passes with fake diagnostics.

Semantic invariant validation is tested the same way:

```kea
test "ANF validation catches non-atomic let values"
  let bad_ir = HirExpr.Let
    name: "x"
    value: HirExpr.Call { func: HirExpr.Lit(42), args: [] }
    body: HirExpr.Lit(7)

  let diagnostics = []
  handle validate_anf(bad_ir)
    Diagnose.error(msg) ->
      diagnostics = diagnostics ++ [msg]
      resume()

  assert diagnostics.any(|d| d.contains("atomic"))
```

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

## The compiler optimises itself

A compiler is the perfect workload for Perceus-style RC. Every pass
is a tree transformation — pattern match on a node, construct a new
node. When the IR is uniquely owned (Unique T through a linear
pipeline), every transformation is zero-allocation: the old node's
memory is reused for the new node via reuse tokens.

Type the pipeline with Unique:

```kea
fn parse(_ src: String) -> Unique Ast -[Parse, Diagnose]>
fn infer(_ ast: Unique Ast) -> Unique TypedAst -[TypeCheck, Diagnose]>
fn lower(_ typed: Unique TypedAst) -> Unique MirExpr -[Lower]>
fn optimize(_ mir: Unique MirExpr) -> Unique MirExpr   -- pure!
fn codegen(_ mir: Unique MirExpr) -> Bytes -[Codegen]>
```

Zero RC overhead through the entire pipeline. No increments, no
decrements, no COW checks. This isn't an optimisation — it's a
type-level proof that the compiler never does unnecessary work.

Lean 4 validates the approach. Their self-hosted compiler uses RC +
destructive updates on unique values and spends only 17% of runtime
on deallocation, vs OCaml's 90% in GC. And Lean doesn't even have
Unique T as a type-level guarantee — they do it with runtime checks.
Kea's Unique pipeline is strictly stronger.

The effect system adds three capabilities no other self-hosted
compiler has:

1. **Pure passes parallelise automatically.** `fn optimize(mir) ->
   MirExpr` has no effects — `Par.map(module.functions, optimize)`
   is type-checked safe. Not per-translation-unit (gcc) or
   per-codegen-unit (rustc) — per *function*. Sorbet achieves 100K
   lines/sec/core this way, but through engineering discipline. In
   Kea, the effect system proves it and Unique T proves the data
   doesn't alias.

2. **Arena allocation via Alloc effect.** The parse phase allocates
   hundreds of thousands of AST nodes and discards them after
   lowering. `handle parse(src) with Alloc -> Arena.new(4096)` gives
   bump allocation for the phase, bulk deallocation at handler exit.
   2-5x from cache locality alone.

3. **Incremental queries via Query effect.** Content-addressed hashing
   on immutable IR nodes gives early cutoff: if a whitespace-only edit
   doesn't change the AST hash, all downstream passes are skipped.
   Rust-analyzer's Salsa does this with manual annotations. In Kea,
   the Query effect *is* the annotation.

See `BRIEFS/design/self-hosting-perf.md` for the full analysis,
performance targets, and references.

---

## When this lands

This is Phase 1-2 work. Phase 0 builds the bootstrap compiler in
Rust with internal IR types. When Kea self-hosts:

1. The Rust `HirExpr` enum becomes a Kea type with row variables
2. Compiler passes become Kea functions under decomposed
   compilation effects (`Parse`, `TypeCheck`, `Lower`, `Diagnose`)
3. `@derive` becomes a recipe consuming StableHIR
4. Backends implement the Grammar trait over MIR
5. LSP, MCP, REPL become handler configurations — each handling
   only the compilation effects it needs

The grammar block mechanism is a library feature, not a language
primitive. The `Grammar` trait and `embed` keyword are
language-level, but any specific grammar (Hir, Sql, Html) is an
implementation. The bootstrapping sequence:

1. Rust bootstrap compiles Kea stdlib + self-hosted compiler
   (using direct pattern matching on IR types)
2. Self-hosted compiler compiles itself (still direct pattern
   matching)
3. Grammar implementations are written as Kea libraries
4. Compiler passes optionally adopt grammar blocks as sugar

No special compiler support is needed beyond the general `embed`
mechanism. Grammar blocks are a convenience layer, not a
requirement. The first self-hosted compiler proves the approach
works with plain pattern matching and construction.

The stdlib is written in Kea from Phase 0, compiled by the Rust
bootstrap compiler. By Phase 1, the compiler's first user — its own
stdlib — has been exercising the language for months. Every stdlib
tier validates the compilation phase that enables it: Tier 0 tests
the module system and pure codegen, Tier 1 tests handler compilation,
Tier 2 tests the memory model, Tier 3 tests the full type system.

The bootstrap compiler is the prototype. The self-hosted compiler
is the product. And the language features that make the self-hosted
compiler possible — effects, handlers, row polymorphism, typed
grammars — are the same features users write application code with.

There is no "compiler magic." There is only Kea.
