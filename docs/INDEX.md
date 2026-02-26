# Kea Documentation

## Vision

- [VISION.md](VISION.md) — Why Kea exists: effect-driven programming, struct-everything, typed OTP, the five pillars.

## Specifications

- [spec/KERNEL.md](spec/KERNEL.md) — Kea Kernel Specification v4: types, structs, enums, effects, handlers, traits, row polymorphism, memory model, actors.
- [spec/CALL-SYNTAX.md](spec/CALL-SYNTAX.md) — Call Syntax Matrix: method dispatch, UMS, receiver placement, resolution algorithm.
- [spec/ROADMAP.md](spec/ROADMAP.md) — Implementation Roadmap v2: phases, rill inventory, timeline, risk register.
- [spec/PLATFORM-ADOPTION.md](spec/PLATFORM-ADOPTION.md) — Platform strategy: one semantic engine for compiler/LSP/REPL/tests/MCP/runtime introspection, adoption wedges, and roadmap slotting.

## Design

- [REPL.md](REPL.md) — REPL design: type-and-effect-aware exploration, Cranelift JIT, indentation handling, effect/actor interaction, MCP integration.

## Language

- [PEDAGOGY.md](PEDAGOGY.md) — Documentation style guide: progressive disclosure, error message principles.
- [VALUES-AND-COMPOSITION.md](VALUES-AND-COMPOSITION.md) — Why values beat mutable objects: combinators, copy-on-write, effect-driven testing, and what Kea gets from the model.
- [COMPILER-AS-DATA.md](COMPILER-AS-DATA.md) — Why Kea's compiler IR is a Kea type: self-describing compilation, every tool as a handler, grammar blocks as language embedding, and row polymorphism as extension sustainability.
- [EFFECTS-ORIENTED.md](EFFECTS-ORIENTED.md) — Effects-oriented programming: the problems effects solve, how Kea's effect system works, and why it matters for testing, refactoring, and correctness.
- [UNIVERSAL-DOT.md](UNIVERSAL-DOT.md) — User guide for Kea's call style: dot dispatch, `::` qualification, and `$` receiver placement.

## Working Documents

- [../AGENTS.md](../AGENTS.md) — Guide for coding agents working on the codebase.
- [../BRIEFS/](../BRIEFS/) — Implementation briefs (design decisions, in-progress work, completed work).
- [../FORMAL.md](../FORMAL.md) — Kea Lean formalization scope, migration status, and MCP-first verification workflow.
