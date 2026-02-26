# Brief: Live Code Loading

**Status:** design
**Priority:** Phase 0d+ (REPL/script), Phase 2 (dev reload), Phase 3 (production)
**Depends on:** 0d-codegen-pure (Cranelift JIT), 0e-runtime-effects (actor runtime), packaging-ffi-comptime (package resolution)
**Blocks:** scripting ergonomics, REPL usability, dev iteration speed
**Related:** [testing](testing.md) (effect-driven isolation), [packaging-ffi-comptime](packaging-ffi-comptime.md) (package resolution)

## Motivation

Kea has three features that no other compiled language combines:
a Cranelift JIT, an actor model, and an effect system. Together
they enable live code loading — from REPL dependency installation
to dev-mode hot reload to (potentially) production code swapping.

This isn't a new feature to build. It's a capability that falls
out of features we're already building, if we design the seams
correctly.

## Ground Truth

Cranelift's `JITModule` supports function redefinition via
`JITBuilder::hotswap(true)`. When enabled, function pointers go
through indirect trampolines. Redefining a function updates the
trampoline target — existing function pointers route to new code
without caller changes. `rustc_codegen_cranelift` uses this for
incremental JIT. This is the mechanism, not a hack.

Erlang/BEAM is the only production system with battle-tested hot
code reload. It works because of: uniform term representation
(no struct layout changes), process isolation (actors), two-version
module loading, and explicit `code_change` callbacks. Every other
compiled language's hot reload is either experimental (Nim),
fragile (C dlopen/dlclose), or niche (Common Lisp SBCL).

Kea cannot match Erlang's ease of hot reload (we have concrete
struct layouts, not uniform terms). But we can exceed every other
compiled language because we have the actor isolation model AND
the JIT, and the effect system provides compatibility checking
that Erlang lacks.

## Three Tiers

### Tier 1: REPL and Script Dependency Loading

**When:** Phase 0d+ (JIT exists), extended in Phase 2 (packages)
**Risk:** Low. Uses existing JIT infrastructure.

The REPL already JIT-compiles each input via Cranelift. `:load`
already loads `.kea` files into the session. Extending this to
package dependencies is a natural step.

**REPL: `Pkg.install`**

```kea
> Pkg.install(["json", "http"])
-- resolves versions, downloads source, compiles via Cranelift JIT
-- type information loaded into REPL type environment
-- functions available immediately

> let data = Http.get("https://api.example.com/users")
> Json.decode(data.body, List User)
```

Mechanism:
1. Resolve dependency tree (same resolver as `kea pkg`)
2. Download source (or use cache)
3. Compile each module via Cranelift JIT into the running session
4. Register types, traits, and functions in the REPL environment
5. Cache compiled artifacts for subsequent sessions

This preserves the "no install scripts" principle: `Pkg.install`
downloads source and compiles it with the Kea compiler. No
arbitrary code runs during installation. The effect system still
tracks what the loaded code can do — if `http` has `-[IO]>` in
its signatures, the REPL shows it.

**Scripts: `@install`**

```kea
#!/usr/bin/env kea run
@install("http 1.2", "json 0.5")

struct Main
  fn main() -[IO]> ()
    let resp = Http.get("https://api.example.com/data")
    let users = Json.decode(resp.body, List User).unwrap()
    IO.stdout(users.map(|u| -> u.name).join(", "))
```

First run: resolve, download, compile, cache, execute.
Subsequent runs: load from cache, execute. Cache key includes
dependency versions + Kea compiler version (like Mix.install).

This is Deno's model (dependencies declared in source, cached
locally) but with static types and effect tracking. Deno caches
compiled JS; Kea caches JIT artifacts.

**What transfers from Elixir Mix.install:**
- Cache keyed on dependency spec + compiler version
- Cannot be called twice in the same session (or explicit `force`)
- First run is slow (network + compilation), cached runs are fast
- Dependencies available immediately after install completes

**What Kea adds over Mix.install:**
- Effect signatures visible on loaded code (pure packages provably
  safe even when loaded dynamically)
- Type checking against loaded code (not just runtime dispatch)
- Compiled to native code, not bytecode

### Tier 2: Dev-Mode Hot Reload

**When:** Phase 1-2
**Risk:** Medium. Needs careful synchronization.

`kea run --watch` monitors source files. On change: recompile
the modified module, swap the function via Cranelift hotswap,
continue execution.

```
$ kea run --watch server.kea
  server listening on :8080
  [reload] src/handlers.kea changed, recompiling...
  [reload] 3 functions updated (12ms)
  -- next request uses new code
```

**Mechanism:**

1. File watcher detects source changes
2. Recompile changed module to MIR
3. Type-check against existing environment:
   - Effect signature changes flagged as warnings
   - Type signature changes that break callers are errors
   - Pure additions (new functions) always safe
4. Call `prepare_for_function_redefine` for changed functions
5. Redefine via Cranelift JIT
6. Call `finalize_definitions`
7. Trampolines now route to new code

**Actor reload boundary:**

For actor-based programs, the reload is even cleaner. Actors
process one message at a time. The reload happens between
messages:

1. Actor finishes processing current message
2. Before dequeuing next message: check for pending reload
3. If reload pending: swap to new message handler
4. Process next message with new code

This is Erlang's model. The actor mailbox is the natural
synchronization point. No mid-execution swap, no torn state.

**What the effect system adds:**

Erlang has no compile-time check on hot reload compatibility.
You can reload a module that changes the message protocol and
your actors crash with `badmatch` at runtime.

Kea can check:
- **Effect signature compatibility.** If the new version of a
  handler adds `Send` to its effect row, flag it — the caller
  may not have a Send handler installed.
- **Message type compatibility.** If an actor's message type
  changes, the reload system can reject the swap or warn.
  Erlang can't — messages are untyped.
- **Pure function safety.** Pure functions can be swapped with
  zero risk. The compiler proves it.

**Limitations (honest):**

- **Struct layout changes require restart.** If a struct's
  fields change, existing values in memory have the old layout.
  Unlike Erlang's uniform terms, we can't transparently migrate.
  Dev-mode reload rejects struct layout changes and tells you
  to restart.
- **Closure captures.** A closure captured before reload still
  references old code. New closures capture new code. This is
  the same as Erlang's behaviour (old code in closures stays
  old until the closure is GC'd).
- **Thread safety is manual.** Cranelift's hotswap doesn't
  synchronize. The actor mailbox boundary handles this for
  actor code. Non-actor code (pure computations in flight)
  needs a quiescent point — the simplest approach is to only
  reload between top-level operations.

### Tier 3: Production Hot Code Reload

**When:** Phase 3+ (if ever)
**Risk:** High. May not be worth it.

Full Erlang-style production hot reload: deploy new code to a
running system, actors pick it up between messages, no downtime.

**Why it's hard:**

- **Struct layout migration.** Production data has the old layout.
  Migrating requires either: (a) uniform term representation
  (gives up performance), (b) explicit migration callbacks
  (Erlang's `code_change`), or (c) serialise-deserialise through
  a format that handles schema evolution.
- **Two-version coordination.** Need to keep old and new code
  loaded simultaneously. Old actors finish with old code, new
  messages get new code. Refcounting handles cleanup, but the
  module loader needs to track which version each actor uses.
- **Rollback.** If new code crashes, need to roll back to old
  version. Erlang's release handler does this. Kea would need
  equivalent infrastructure.

**Why it might be worth it (for actors):**

Kea's actor model is isolated by design. Each actor has private
state, communicates via typed messages, and processes one message
at a time. This is exactly the model that makes Erlang hot reload
work. If we add:
- A `code_change` callback on the Actor trait (optional, default
  is identity — keep the same state)
- Typed message migration via Encode/Decode (serialise old state,
  deserialise into new struct)
- Supervision-driven rollback (supervisor restarts actor with old
  code if new code fails init)

...then actor hot reload is feasible. Non-actor code still needs
restart for struct changes.

**Honest assessment:** Rolling restarts behind a load balancer
are simpler, safer, and better understood. Tier 3 is a Phase 3+
bet that should only be pursued if the actor ecosystem is large
enough that the Erlang-style experience is a competitive
differentiator. Don't build it speculatively.

## Design Constraints on Current Work

These constraints ensure Tiers 1-2 are viable without
rearchitecting later.

### 1. JIT module must support incremental compilation

The 0d JIT path must use `JITBuilder::hotswap(true)` from the
start — even if hot reload isn't implemented yet. Switching from
non-hotswap to hotswap mode later changes the calling convention
(direct calls vs trampolines) and could break assumptions.

Cost: one level of indirection on all JIT function calls (the
trampoline). This is a single indirect jump — negligible for
REPL and dev-mode use. AOT builds are unaffected (no trampolines).

### 2. Module identity must be stable

The compiler must track module identity so that "recompile
module X" is a well-defined operation. Each module needs a
stable identifier that persists across recompilation. This is
already implied by the module system (one file = one module,
path determines identity).

### 3. Type environment must be separable from compiled code

The REPL and reload system need to update type information
independently of code. When a module is reloaded, its type
exports must be re-registered in the environment without
invalidating unrelated type information. The type checker
should support incremental updates to its environment.

### 4. No global mutable state in the compiler pipeline

The compiler pipeline (parse → check → lower → codegen) must
be callable multiple times in the same process without residual
state from previous compilations interfering. This is standard
good engineering but worth stating explicitly: the compiler is
a function, not a stateful process.

## Interaction with "No dlopen" Principle

The packaging brief states "no dlopen/runtime loading." This
is about external native libraries — Kea does not load arbitrary
`.so` files at runtime.

Live code loading is a different mechanism: Kea source is
compiled by the Kea compiler (via Cranelift JIT) and linked into
the running process. No foreign code execution. No arbitrary
binary loading. The effect system still tracks what loaded code
can do. Pure packages remain provably pure even when loaded at
runtime.

This is analogous to Erlang loading `.beam` files — it's not
dlopen, it's the language runtime loading code in its own format.

## Interaction with Package Security

`Pkg.install` in the REPL downloads and compiles source code.
The same security properties apply as static builds:

- **No install scripts.** Source is compiled by the Kea compiler,
  nothing else.
- **Effect tracking.** Loaded packages declare their effects.
  A pure package can't suddenly do IO just because it's loaded
  at runtime. The type checker verifies this.
- **Immutable versions.** Cached artifacts are keyed by version
  hash. Reloading the same version produces identical code.

The attack surface is: "what if the source code itself is
malicious?" Same answer as static builds — the effect system
constrains what code can do. A package without IO in its
signatures provably cannot exfiltrate data, whether loaded
statically or dynamically.

## What This Is NOT

- **Not a plugin system.** No `.so` loading, no C ABI, no
  Go-style `plugin.Open`. Kea source only.
- **Not runtime metaprogramming.** You can't generate and
  execute arbitrary code strings at runtime. All code goes
  through the full compiler pipeline (parse, type-check, etc.).
- **Not eval.** There is no `eval("code")` function. The REPL
  compiles inputs through the same pipeline as `kea build`.
  `Pkg.install` compiles packages through the same pipeline.
  The JIT is a compilation target, not an interpreter.

## Precedent Comparison

| Feature | Erlang | Julia | Deno | Go | **Kea** |
|---------|--------|-------|------|----|---------|
| REPL dep loading | Mix.install | Pkg.add | URL import | N/A | **Pkg.install** |
| Script deps | Mix.install | Project.toml | URL import + cache | N/A | **@install** |
| Dev hot reload | automatic (BEAM) | Revise.jl (fragile) | --watch (restart) | N/A | **--watch (JIT swap)** |
| Prod hot reload | release handler | N/A | N/A | N/A | **Tier 3 (maybe)** |
| Type-checked reload | No | Partial | No (JS) | N/A | **Yes (effects + types)** |
| Native speed | No (bytecode) | Yes (LLVM JIT) | No (V8) | Yes (but no JIT) | **Yes (Cranelift JIT)** |

## Implementation Timeline

### Phase 0d (with codegen)
- Enable `JITBuilder::hotswap(true)` for REPL JIT module
- Compiler pipeline is reentrant (no global mutable state)
- `:load <file>` works in REPL (already planned)

### Phase 0d+ (shortly after)
- `:reload <file>` recompiles and swaps in REPL
- Type/effect compatibility checking on reload
- Incremental type environment updates

### Phase 2 (with package system)
- `Pkg.install` in REPL (resolve, download, compile, link)
- Script `@install` with caching
- Cache keyed on dep spec + compiler version

### Phase 2-3 (with actor runtime)
- `kea run --watch` dev-mode hot reload
- Actor mailbox reload boundary
- Effect signature compatibility warnings
- Struct layout change detection (reject, suggest restart)

### Phase 3+ (speculative)
- Production hot code reload for actors
- `code_change` callback on Actor trait
- State migration via Encode/Decode
- Supervision-driven rollback

## Open Questions

- **Should `Pkg.install` be available outside the REPL?** In
  production code, dynamic dependency loading is probably an
  anti-pattern. Proposal: `Pkg.install` only in REPL and script
  mode. Production code uses `kea.toml` exclusively.

- **Cache eviction for JIT artifacts.** How long do cached
  compilations persist? Proposal: same cache as `kea pkg` with
  content-addressed storage. Evict on `kea clean`.

- **Should `kea run --watch` work for non-actor programs?**
  For a simple CLI program, "hot reload" means "restart on
  change" (like `nodemon`). For actor programs, it means
  "swap code between messages." Should `--watch` do both,
  or should non-actor programs just get restart-on-change?
  Proposal: restart-on-change for non-actor programs, true
  hot reload for actor programs. The effect signature tells
  you which mode applies (presence of Send/Spawn = actor mode).

- **Interaction with AOT builds.** Hot reload is JIT-only. AOT
  binaries (`kea build`) cannot be hot-reloaded — they're static
  native executables. Should the AOT binary embed the JIT for
  optional hot reload? Proposal: no. AOT = static, JIT = dynamic.
  If you want hot reload, use `kea run`. If you want a static
  binary, use `kea build`.
