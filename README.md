# -[kea]>

A statically-typed functional programming language with algebraic effects, handlers, and row polymorphism.

**Status:** Active development. The bootstrap compiler is implemented in Rust and the language/runtime surface is still evolving.

## Features

- **Algebraic effects and handlers** — effects are declared, tracked in types, and handled with scoped handlers. Resumable continuations with at-most-once semantics.
- **Row polymorphism** — extensible records and effect rows using Remy-style unification. The same mechanism powers both data and effects.
- **Indentation-sensitive syntax** — no braces or semicolons. Blocks are delimited by indentation.
- **Compiler pipeline** — parser, type inference, HIR/MIR lowering, and Cranelift-backed execution/compilation are all in-tree.
- **Tooling surface** — single `kea` CLI, including `kea mcp` for MCP-based type checking and diagnostics.

## Building

Requires Rust stable (edition 2024) and [mise](https://mise.jdx.dev/) for task running.

```sh
git clone https://github.com/amplifiedai/kea.git
cd kea
mise run check       # lint
mise run test        # test suite
cargo run -p kea -- run path/to/program.kea
```

## Usage

```sh
kea run program.kea   # compile and run via JIT
kea build program.kea # compile to executable
kea test              # run test blocks
kea mcp               # run MCP server over stdio
kea pkg init          # initialize kea.toml in the current directory
```

## Documentation

Public documentation is not published yet.

For now, see:
- [`stdlib/`](stdlib/) for language examples and module surfaces
- [`crates/kea/tests/`](crates/kea/tests/) for executable coverage of language/runtime behavior

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT), at your option.

Copyright 2026 Amplified AI, Inc.
