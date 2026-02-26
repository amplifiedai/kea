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

## Security and Policy Invariants

1. Grammar compilation runs under `Compile` capability only.
2. No arbitrary runtime eval from embedded grammar blocks.
3. No raw compiler internals exposed as stable public API.
4. Output IR must pass normal type/effect checking.
5. Grammar package permissions are explicit in manifest metadata.

## Roadmap Slotting

### Phase 1 foundation

- Land generic `embed <Grammar> { ... }` core path.
- Land one reference grammar (`Html`) for templating competitiveness.

### Phase 2 expansion

- Add `Sql` and one additional grammar (`Css` or `Einsum`) as proofs
  that the interface generalizes.
- Add tooling conformance tests (diagnostics + semantic query parity).

## Implementation Plan (when promoted)

1. Define `Grammar` trait, `GrammarCtx`, and `LoweredExpr` compiler API.
2. Add parser support for `embed <Ident> { ... }` blocks.
3. Add compile-time extension execution path via `Compile` effect hooks.
4. Implement built-in `Html` grammar package with strict typing.
5. Add sugar parsing/desugaring for `html { ... }` after generic path is stable.
6. Add conformance tests across LSP/MCP/REPL diagnostics.

## Testing Requirements

- Parse tests for generic `embed` and sugar forms.
- Type/effect tests ensuring lowered output is ordinary Kea IR.
- Security tests: grammar packages cannot exceed declared compile-time capabilities.
- Snapshot tests for diagnostics and source spans inside embedded blocks.
- Performance tests: compile-time overhead bounded for large templates/queries.

## Definition of Done

- Generic typed grammar mechanism exists and is documented.
- `Html` grammar is production-usable for templating.
- Grammar diagnostics and semantic queries integrate with existing tooling.
- No grammar-specific runtime privilege path exists.

## Non-Goals (initial)

- Arbitrary runtime code execution inside embedded grammar blocks.
- Supporting every DSL immediately.
- Distributed optimization/runtime execution for grammar outputs.
