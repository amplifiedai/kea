# Brief: Bootstrap Infrastructure

**Status:** active
**Priority:** v1-critical
**Depends on:** *(none — first brief)*
**Blocks:** all Phase 1 crate work

## Motivation

Kea needs the same development infrastructure that made rill productive: Cargo workspace, mise task runner, agent-safe build scripts, BRIEFS tracking, documentation structure, and .claude integration. We cannibalise this wholesale from rill.

## Implementation Plan

1. Initialize git repo
2. Create directory structure (BRIEFS/, docs/, scripts/, .claude/, crates/)
3. Adapt AGENTS.md from rill for kea
4. Adapt mise.toml and scripts/ from rill
5. Set up .claude/CLAUDE.md symlink to AGENTS.md
6. Create BRIEFS/INDEX.md with initial workboard
7. Create docs/INDEX.md and spec document placeholders
8. Create Cargo.toml workspace
9. Create .gitignore

## Testing

- `mise run check` should work (even with no crates yet)
- All scripts should be executable
- Symlink should resolve correctly

## Progress

- 2026-02-26: Initial scaffolding — DONE
- 2026-02-26: Spec docs saved (KERNEL.md, CALL-SYNTAX.md, ROADMAP.md, REPL.md) — DONE
- 2026-02-26: VISION.md written — DONE
- 2026-02-26: AGENTS.md strengthened (rill cannibalisation mandate) — DONE
