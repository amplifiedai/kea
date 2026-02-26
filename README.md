# Kea

A statically-typed functional programming language with algebraic effects, handlers, and row polymorphism.

**Status:** Early development. The bootstrap compiler is being built in Rust. Phase 0d (code generation for the pure subset) is active.

## Features

- **Algebraic effects and handlers** — effects are declared, tracked in types, and handled with scoped handlers. Resumable continuations with at-most-once semantics.
- **Row polymorphism** — extensible records and effect rows using Remy-style unification. The same mechanism powers both data and effects.
- **Indentation-sensitive syntax** — no braces or semicolons. Blocks are delimited by indentation.
- **Cranelift backend** — compiles to native code via Cranelift. JIT for `kea run`, AOT for `kea build`.
- **MCP server** — `kea-mcp` exposes type checking and diagnostics over MCP for editor and agent integration.

## Building

Requires Rust stable (edition 2024) and [mise](https://mise.jdx.dev/) for task running.

```sh
git clone https://github.com/amplifiedai/kea.git
cd kea
mise run check       # lint
mise run test        # test suite
cargo build          # build all crates
```

## Usage

```sh
kea run program.kea   # compile and run via JIT
kea build program.kea # compile to executable
```

## Documentation

See [`docs/INDEX.md`](docs/INDEX.md) for the full documentation suite, including the [kernel specification](docs/spec/KERNEL.md) and [roadmap](docs/spec/ROADMAP.md).

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT), at your option.

Copyright 2026 Amplified AI, Inc.
