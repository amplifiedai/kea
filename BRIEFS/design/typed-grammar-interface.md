# Brief: Typed Grammar Interface (HTML/SQL/CSS/Einsum)

**Status:** design
**Priority:** Phase 1-2 (after core comptime substrate exists)
**Depends on:** 0d-codegen-pure, 0g-advanced-types, packaging-ffi-comptime, runtime-introspection-mcp
**Blocks:** first-class templating story (Templ/HEEx-class), typed SQL blocks, typed DSL ecosystem

## Motivation

Kea should support embedded domain grammars (HTML, SQL, CSS, tensor
expressions) without hardcoding each as compiler syntax forever.

The right model is:

1. One host embedding mechanism in the language.
2. Grammar implementations as typed compile-time extensions.
3. Outputs lowered to normal typed Kea IR (no special runtime).

This keeps Kea coherent with:

- struct-everything,
- effects as capability boundaries,
- comptime as controlled code generation,
- semantic platform contracts (shared diagnostics/introspection).

## Problem Statement

If we add `html {}`, `sql {}`, `css {}`, `einsum {}` as separate
compiler features, we create:

- parser/typechecker bloat,
- inconsistent diagnostics and tooling behavior,
- security drift (ad hoc execution paths),
- inability for ecosystem packages to define new grammars safely.

## Core Design

### 1) Universal Grammar Contract

Define a standard trait for compile-time grammars:

```kea
trait Grammar
  type Ast
  type Out
  type Err

  fn parse(_ src: String) -[Compile]> Result(Self.Ast, Self.Err)
  fn check(_ ast: Self.Ast, _ ctx: GrammarCtx) -[Compile]> Result(Typed(Self.Out), Diag)
  fn lower(_ typed: Typed(Self.Out)) -[Compile]> LoweredExpr
```

Key rule: `lower` must produce normal Kea typed IR forms.
No grammar gets a privileged runtime execution path.

### 2) Host Syntax: generic first, sugar second

Canonical form (generic):

```kea
embed Html { <h1>{user.name}</h1> }
embed Sql  { select * from users where id = {id} }
```

Domain sugars can desugar into `embed`:

- `html { ... }` -> `embed Html { ... }`
- `sql { ... }` -> `embed Sql { ... }`

This keeps the surface ergonomic while preserving a single mechanism.

### 3) Type/effect integration

Grammar outputs are ordinary Kea values:

- `Html` grammar outputs `Html` values (or typed component trees).
- `Sql` grammar outputs typed query plans / query functions.
- `Css` grammar outputs typed style objects or scoped class tables.
- `Einsum` grammar outputs tensor programs with shape constraints.

Effects remain explicit:

- Pure render/query construction remains `->`.
- Execution effects (`IO`, DB transport, etc.) appear only at runtime
  boundary APIs, not at grammar parse/check stages.

### 4) Comptime/extension integration

Grammar implementations are packages using `Compile` effect APIs from
the comptime brief:

- parse/check/lower run at compile-time only,
- no install/build scripts,
- no ambient filesystem/network privileges,
- extension effects are capability-gated and auditable.

This is the same trust model as deriving/comptime, not a separate
plugin runtime.

### 5) Tooling and semantic platform integration

Grammar diagnostics must flow through normal `kea-diag` categories/codes.
Semantic tools (LSP/MCP/REPL/test output) consume grammar results via
the same semantic query contracts.

No side-channel diagnostics format per grammar.

## Html v1 Contract (Reference Grammar)

`Html` is the first production grammar and the benchmark for whether
the typed grammar interface is viable.

### 1) Surface forms (v1)

Supported:

```kea
embed Html {
  <div class="card">
    <h1>{title}</h1>
    {body}
  </div>
}

html {
  <Button label={label} on_click={handler} />
}
```

Rules:
- `html { ... }` is sugar for `embed Html { ... }`.
- `{expr}` interpolation is expression injection.
- Component tags are `PascalCase`.
- Native tags are lowercase (`div`, `span`, `input`).

### 2) Type contract

- Grammar output type: `Html`.
- Interpolation requires:
  - `Html` (insert as node), or
  - `String` / scalar with `Show` (insert as escaped text), or
  - `Option Html` / `Option String` (none emits nothing).
- Attributes are typed:
  - string-like attrs require `String`/`Show`,
  - boolean attrs require `Bool`,
  - event attrs require callable values with declared handler type.
- Component props are compile-time checked against component signature.

### 3) Escaping and safety

- Text interpolation is HTML-escaped by default.
- Attribute interpolation is escaped by default.
- Raw HTML insertion requires explicit trusted wrapper API
  (`Html.raw(...)`) and is opt-in/auditable.
- No implicit raw string passthrough.

### 4) Effects and purity

- Building `Html` trees is pure (`->`) by default.
- Rendering/streaming to network/file is boundary API and effectful
  (`-[IO]>`, etc.) outside grammar construction.
- Grammar parse/check/lower runs under compile-time `Compile` only.

### 5) Diagnostics contract

Must provide precise diagnostics for:
- malformed markup,
- unknown component,
- missing required prop,
- unknown prop,
- prop type mismatch,
- invalid interpolation type.

All diagnostics must include:
- source span within the embedded block,
- expected vs found type where relevant,
- actionable fix hints.

### 6) Lowering contract

`Html` lowering target in v1:
- typed `Html` IR node constructors, or
- equivalent normalized builder calls.

Lowered form must be deterministic and must not require a special
runtime interpreter distinct from ordinary Kea execution.

## Security and Policy Invariants

1. Grammar compilation runs under `Compile` capability only.
2. No arbitrary runtime eval from embedded grammar blocks.
3. No raw compiler internals exposed as stable public API.
4. Output IR must pass normal type/effect checking.
5. Grammar package permissions are explicit in manifest metadata.

## Roadmap Slotting

### Phase 1 foundation

- Land generic `embed <Grammar> { ... }` core path.
- Land `Html v1` reference grammar with typed props/interpolation and
  escaping defaults (templating competitiveness target).

### Phase 2 expansion

- Add `Sql` and one additional grammar (`Css` or `Einsum`) as proofs
  that the interface generalizes.
- Add tooling conformance tests (diagnostics + semantic query parity).

## Implementation Plan (when promoted)

1. Define `Grammar` trait, `GrammarCtx`, and `LoweredExpr` compiler API.
2. Add parser support for `embed <Ident> { ... }` blocks.
3. Add compile-time extension execution path via `Compile` effect hooks.
4. Implement built-in `Html` grammar package per `Html v1 Contract`.
5. Add sugar parsing/desugaring for `html { ... }` after generic path is stable.
6. Add conformance tests across LSP/MCP/REPL diagnostics.
7. Publish `Html v1` performance and diagnostics baseline numbers.

## Testing Requirements

- Parse tests for generic `embed` and sugar forms.
- Type/effect tests ensuring lowered output is ordinary Kea IR.
- Security tests: grammar packages cannot exceed declared compile-time capabilities.
- Snapshot tests for diagnostics and source spans inside embedded blocks.
- Performance tests: compile-time overhead bounded for large templates/queries.
- Html-specific tests:
  - escaping defaults for text and attributes,
  - explicit raw HTML API behavior,
  - component prop type-check coverage,
  - interpolation type-check coverage,
  - lowering determinism snapshots.

## Definition of Done

- Generic typed grammar mechanism exists and is documented.
- `Html` grammar is production-usable for templating.
- `Html v1 Contract` is fully satisfied and benchmarked.
- Grammar diagnostics and semantic queries integrate with existing tooling.
- No grammar-specific runtime privilege path exists.

## Grammar–Recipe–IR Convergence

KERNEL §15 states: "The compiler's HIR and MIR are Kea types. Compiler
passes are pure Kea functions that transform these types." This means
the Grammar trait and the Recipe system (§15) converge:

| Concept | Grammar interface | Recipe system (§15) |
|---------|------------------|---------------------|
| Input | Source text in `embed` block | StableHIR / UnstableMIR nodes |
| Validation | `check` under `Compile` effect | Recipe validates IR subset |
| Output | `LoweredExpr` (normal Kea IR) | Transformed IR / codegen output |
| Extension | Package implements `Grammar` trait | Package implements recipe |
| Stability | Grammar contract is versioned | StableHIR is row-extensible |

**Key insight:** Restricted sublanguages (§15.2) ARE grammars. A `@gpu`
recipe validates that a function body conforms to a restricted grammar
(no closures, no recursion, no heap) and then lowers through a custom
backend. The Grammar trait's `parse → check → lower` is exactly what
a recipe does: parse IR nodes → validate constraints → produce target
output. The `Compile` effect governs both.

**Row polymorphism is the versioning mechanism.** StableHIR uses
row-polymorphic interfaces (§15.1) so recipes tolerate new IR nodes —
the row variable absorbs additions. This is the same row extensibility
that powers record types and effect rows throughout the language.

**What this means for backends:** A compilation backend is a Grammar
that accepts MIR and lowers to its target representation. The backend
interface trait from performance-backend-strategy.md is a grammar
contract. Cranelift, LLVM, and a future Kea-native backend are all
Grammar implementations over MIR. The interface is unified.

**What this means for self-hosting:** When Kea compiles itself, its
own IR passes through the same typed grammar mechanism that user code
uses for HTML/SQL. The compiler is not special — it is another grammar
consumer. `@derive` is a recipe. A linter is a recipe. A backend is
a grammar. The typed grammar interface is the universal extension point.

See [ir-recipes-grammar-convergence](ir-recipes-grammar-convergence.md)
for the full design brief connecting these mechanisms.

## Non-Goals (initial)

- Arbitrary runtime code execution inside embedded grammar blocks.
- Supporting every DSL immediately.
- Distributed optimization/runtime execution for grammar outputs.
