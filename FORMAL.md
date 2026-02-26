# Kea Type System Formalization

Lean 4 formalization of Kea's type-and-effect system.

This work starts by cannibalizing the existing Rill formal corpus and then extending it for Kea's effect-row and handler semantics.

## Current Status

- **Phase 1 (active):** Core migration from Rill `formal/` into `kea/formal/`, with effect-row surface aligned to Kea (`Ty.functionEff` + `EffectRow`) and current Lean build green.
- **Phase 1 (active):** Core migration now includes explicit WF judgments and substitution-preservation lemmas for the effect-row-extended core surface.
- **Phase 2 (next):** Kea-specific effect typing and handler theorems.

The formal workspace lives at [`formal/`](formal/).

## Scope

### Phase 1: Core HM + Row Migration

Migrate and align these Lean modules with `kea-types` and `kea-infer`:

- `Kea/Ty.lean`
- `Kea/Substitution.lean`
- `Kea/FreeVars.lean`
- `Kea/OccursCheck.lean`
- `Kea/LacksConstraints.lean`
- `Kea/Unify.lean`
- `Kea/Generalize.lean`
- `Kea/Traits.lean`
- `Kea/Typing.lean`

### Phase 2: Kea Effect/Handler Formalization

Add Kea-native theorems for:

- Handler effect removal
- Resume linearity (at-most-once)
- Fail as zero-resume
- Fail/Result equivalence
- Effect polymorphism soundness

## Workflow Contract

Use MCP-first verification, mirroring the Rill protocol:

1. Predict (Lean conjecture + explicit preconditions)
2. Probe (`kea-mcp`: `type_check`, `diagnose`, `get_type`)
3. Classify (agreement / precondition gap / divergence)
4. Act (prove, revise, or log divergence)
5. Traceability (theorem + MCP evidence link)

All session evidence goes to [`formal/mcp-log.md`](formal/mcp-log.md).

## Build

```bash
cd formal && lake build
```

Lean runs independently of Rust checks.
