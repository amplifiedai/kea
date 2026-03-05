# -[kea]>

A statically-typed functional programming language with algebraic effects, handlers, and row polymorphism.

**Status:** Early development. The bootstrap compiler is being built in Rust. Phase 0d (code generation for the pure subset) is active.

## Features

- **Algebraic effects and handlers** — effects are declared, tracked in types, and handled with scoped handlers. Resumable continuations with at-most-once semantics.
- **Row polymorphism** — extensible records and effect rows using Remy-style unification. The same mechanism powers both data and effects.
- **Indentation-sensitive syntax** — no braces or semicolons. Blocks are delimited by indentation.
- **Cranelift backend** — compiles to native code via Cranelift. JIT for `kea run`, AOT for `kea build`.
- **Standard library** — 21 modules including IO, collections, text, math, effects, and testing.
- **Editor support** — plugins for VS Code, Neovim (tree-sitter), Helix, and bat. See [`editors/`](editors/).
- **Tree-sitter grammar** — full parser grammar in [`tree-sitter-kea/`](tree-sitter-kea/) for syntax highlighting and structural editing.
- **MCP server** — `kea-mcp` exposes type checking and diagnostics over MCP for editor and agent integration.
- **Formal verification** — Lean 4 formalization of the type system in [`formal/`](formal/), tracking substitution, unification, and typing soundness.

## Project structure

```
crates/
  kea            # compiler CLI
  kea-ast        # AST nodes and source spans
  kea-codegen    # Cranelift code generation
  kea-diag       # error reporting and diagnostics
  kea-hir        # typed high-level IR
  kea-infer      # HM type inference with row unification
  kea-mcp        # MCP server
  kea-mir        # backend-neutral mid-level IR
  kea-runtime    # runtime with work-stealing scheduler
  kea-syntax     # lexer and recursive-descent parser
  kea-types      # type representations
  kea-bench      # benchmarking infrastructure
stdlib/          # standard library (.kea sources)
editors/         # editor plugins (VS Code, Neovim, Helix, bat)
formal/          # Lean 4 formalization
benchmarks/      # benchmark programs and regression baselines
tree-sitter-kea/ # tree-sitter grammar
keadocs/         # documentation system and design preview
```

## Building

Requires Rust stable (edition 2024) and [mise](https://mise.jdx.dev/) for task running.

```sh
git clone https://github.com/amplifiedai/kea.git
cd kea
mise run check       # clippy lint
mise run test        # test suite
mise run bench       # compiler microbenchmarks
cargo build          # build all crates
```

## Usage

```sh
kea run program.kea   # compile and run via JIT
kea build program.kea # compile to executable
```

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT), at your option.

Copyright 2026 Amplified AI, Inc.
