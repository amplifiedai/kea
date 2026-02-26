# Brief: MCP Server (Day One)

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0b-type-system-core (needs working type checker)
**Blocks:** all agent-assisted development from 0c onward

## Motivation

The MCP server is the primary feedback loop for agentic development.
The ROADMAP says "MCP server from day one" and this is not
aspirational — it's load-bearing. Every agent working on 0c, 0d,
and beyond uses the MCP server to test type checking, evaluate
expressions, and get diagnostics. If the MCP server slips, agent
productivity drops for every subsequent phase.

rill-mcp (371 LOC) is a direct adaptation target. The protocol
layer, tool surface, and compiler-as-MCP-server pattern all transfer.
Only the semantic backend changes (Rill type system → Kea type
system).

## What transfers from Rill

**rill-mcp** (371 LOC):
- MCP protocol handling (JSON-RPC, tool definitions, resource
  serving) — direct transfer
- Tool surface: `type_check`, `evaluate`, `diagnose`, `get_type`
  — same tools, different semantic backend
- Compiler integration pattern: MCP server wraps the type
  checker and evaluator, exposes them as tools

**The adaptation is small.** Replace rill's type checker calls
with kea's. Replace rill's AST types with kea's. The MCP protocol
layer doesn't care what language it's checking.

## Implementation Plan

### Step 1: Adapt rill-mcp

Copy rill-mcp to `crates/kea-mcp/`. Rename rill → kea. Replace
the backend:
- `type_check` tool: parse Kea source → type check → return
  inferred types and diagnostics
- `get_type` tool: given an expression, return its inferred type
  (including effect signature)
- `diagnose` tool: given Kea source, return all diagnostics

Initially `evaluate` can be a stub or omitted — we don't have
a runtime until 0d/0e. The type checker is the critical tool.

### Step 2: Effect-aware tools

Once 0c lands:
- `type_check` shows effect signatures
- `get_type` shows full `-[effects]>` annotations
- New tool: `list_effects` — given a function, list all effects
  it performs and where they're performed

### Step 3: Integration with Lean workflow

Same predict/probe/classify/act protocol as Rill (ROADMAP §MCP-First
Workflow). The MCP server is the oracle for the Lean formalization.

### Step 4: Structured diagnostic output

The MCP server returns `Diagnostic` structs serialized to JSON, not
rendered strings. Agents get machine-readable fields:

```json
{
  "code": "E0001",
  "category": "type_mismatch",
  "severity": "error",
  "message": "argument 2 has type String but count_to expects Int",
  "location": {"file_id": 0, "start": 142, "end": 155},
  "labels": [
    {"location": {"start": 142, "end": 155}, "message": "this is String"},
    {"location": {"start": 38, "end": 44}, "message": "parameter declared as Int here"}
  ],
  "help": "Try Int.parse(value)? to convert"
}
```

This requires `#[derive(Serialize)]` on `Diagnostic`, `Category`,
`Severity`, `SourceLocation`, `DiagLabel` in kea-diag. Error codes
are stable API — agents can pattern-match on them.

The CLI renders the same `Diagnostic` via ariadne for human-readable
output with colored source snippets and underlines. One structured
type, two renderers.

## Testing

- MCP server starts and responds to tool calls
- `type_check` returns correct types for pure Kea programs
- `type_check` returns correct diagnostics for ill-typed programs
- `diagnose` returns structured JSON matching the Diagnostic schema
- `get_type` returns inferred types including effects (after 0c)

## Definition of Done

- `kea-mcp` crate exists and builds
- MCP tools work: type_check, get_type, diagnose
- Agents can use the MCP server to test Kea type checking
- `mise run check` passes

## Timing

This should land **immediately after 0b** — as soon as the type
checker works, wrap it in an MCP server. Don't wait for effects
(0c) or codegen (0d). A type-check-only MCP server is already
enormously valuable for agent development.

Folding this into 0b is acceptable if it stays small. But if 0b
is already large (it is), a separate brief keeps it visible as
a deliverable that must not slip.
