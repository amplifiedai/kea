# Brief: Incremental Stdlib Bootstrap

**Status:** active
**Priority:** v1-critical
**Depends on:** 0d1-module-system (needs multi-file compilation)
**Blocks:** Phase 1 (self-hosting requires working stdlib)
**Also read before implementing:**
- [0d1-module-system](../done/0d1-module-system.md) — module loading, prelude, intrinsics
- [KERNEL §1-2](../../docs/spec/KERNEL.md) — primitive types, collection types, structs
- [KERNEL §5](../../docs/spec/KERNEL.md) — effects, Fail, catch, ?
- [KERNEL Appendix C](../../docs/spec/KERNEL.md) — prelude traits
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — why stdlib in Kea matters for self-hosting

## Motivation

The stdlib is not a late phase. It grows alongside the compiler.
Each phase that adds compilation capabilities delivers the stdlib
code those capabilities unlock. By the time Phase 1 (self-hosting)
starts, the stdlib is 3000+ lines of battle-tested Kea code —
written by the bootstrap compiler, validated against real use.

Writing the stdlib in Kea from day one serves three purposes:

1. **Integration test.** The stdlib is the most thorough test of
   the language. If `List.map` doesn't compile, the type system
   has a bug. If `IO.read_file` doesn't link, the effect system
   has a gap. Every stdlib module is a test of the phase that
   enables it.

2. **No throwaway work.** The `List` you write in Phase 0d is the
   `List` that exists at self-hosting. There's no "builtin List"
   that gets replaced later. The code improves — linked list
   becomes contiguous array in 0f — but it's always Kea code.

3. **Self-hosting velocity.** When Phase 1 starts, the compiler's
   dependencies (collections, IO, error handling, traits) already
   exist. Self-hosting is "rewrite the compiler in Kea" — not
   "rewrite the compiler AND write a stdlib."

## Stdlib Tiers

### Tier 0: Pure (lands with 0d1)

Everything compiled with `->` or `-[Fail]>`. No effects beyond
Fail (which compiles as Result-passing). Core traits defined with
manual impls.

```
stdlib/
  prelude.kea      -- Option, Result, Bool extensions, Unit
  list.kea         -- List (struct wrapping Option (A, List A))
  string.kea       -- String operations via @intrinsic
  int.kea          -- Int: abs, min, max, clamp
  float.kea        -- Float: abs, floor, ceil, round
  order.kea        -- Ordering enum, comparison utilities
  eq.kea           -- Eq trait + manual impls for primitives
  ord.kea          -- Ord trait (manual, no supertrait yet)
  show.kea         -- Show trait + manual impls for primitives
```

**~500-800 lines.** Enough for non-trivial pure programs.

**What this exercises:** Enums, structs, pattern matching, closures,
higher-order functions, recursion, generics, basic trait dispatch,
the module system itself.

**List is a linked list, struct wrapping `Option (A, List A)`.**
No `Cons`/`Nil` — use the existing `Option` type for the empty case.
Empty list is `List None`, cons is `List Some(x, xs)`. UMS hangs
methods on the struct. Pattern matching goes through Option.

```kea
record List A
  head: Option (A, List A)
```

It's O(n) for indexing but sufficient for bootstrap. `List` is the
permanent name for linked list — it does NOT get renamed or replaced.
Tier 2 adds `Vector` as a separate type for array-backed collections.

**String operations use @intrinsic.** `String.length`,
`String.concat`, `String.slice` call Rust-provided runtime
functions. The Kea signatures provide the type; the runtime
provides the implementation.

**Traits have manual impls only.** `@derive` doesn't exist yet
(lands in Tier 3). Every `impl Eq for MyType` is written by hand.
This is acceptable for a small stdlib.

### Tier 1: Effects (lands with 0e)

Effect declarations, handlers, and IO operations. Stdlib modules
that perform effects.

```
stdlib/
  io.kea           -- IO effect: stdout, stderr, read_file, write_file
  net.kea          -- Net effect: TCP/TLS primitives
  http.kea         -- Http client: get, post, request (over Net)
  stream.kea       -- Stream effect: chunked Bytes producer (monomorphic;
                    -- parameterized Stream T requires Eff kind from 0g)
  state.kea        -- State effect + with_state handler
  log.kea          -- Log effect + stdout/collect handlers
  reader.kea       -- Reader effect + with_reader handler
  test.kea         -- assert (Fail-based), basic test utilities
```

**~500-700 additional lines.**

**IO wraps intrinsics.** `IO.stdout` is a Kea function with
`-[IO]>` in its signature that calls `@intrinsic("__kea_io_stdout")`.
The effect annotation is Kea; the syscall is Rust.

**State/Log/Reader handlers are pure Kea.** `with_state` is a
handler written in Kea that intercepts `State.get`/`State.put`.
This is the first real validation that handler compilation works.

**Test utilities use Fail.** `assert` is `fn assert(cond: Bool)
-[Fail AssertionError]> Unit`. The test runner handles the Fail
effect.

### Tier 2: Performance (lands with 0f)

Data structures that need Ptr, @unsafe, Unique, and fixed-width
integers. These replace the Tier 0 linked-list implementations.

```
stdlib/
  vector.kea       -- Contiguous-memory array (Unique + Ptr)
  map.kea          -- HAMT Map (Ptr-based nodes, @unsafe internals)
  set.kea          -- HAMT Set
  bytes.kea        -- Bytes (Ptr UInt8 + length)
  buffer.kea       -- Mutable buffer (Unique Buffer)
```

**~800-1200 additional lines.**

**Vector is a separate type, not a List replacement.** `List`
remains the linked list permanently — it's the correct name for
a linked list, and Kea is a functional language where linked lists
are idiomatic for recursive processing. `Vector` is the array-backed
collection for when you need O(1) indexing and cache-friendly
iteration. Backed by contiguous memory via `Ptr` and `@unsafe`.
`Unique` ensures single-ownership for in-place mutations. Users
choose explicitly: `List` for recursive/cons patterns, `Vector`
for performance-sensitive sequential access.

**HAMT Map/Set.** Hash Array Mapped Tries per KERNEL §1.2.
Internal nodes use `Ptr` and `@unsafe` for the trie structure.
External API is pure. This is the production Map.

**Writing these IS the test for 0f.** If HAMT can't be written
with Ptr + @unsafe, the memory model has a gap.

**Numeric extensions needed:** HAMT needs `popcount` (KERNEL §1.1.4)
for index calculation and bitwise ops (§1.1.2) for trie navigation.
Hash functions need `wrapping_mul`/`wrapping_add` (§1.1.3). Hex
literal prefixes (`0xFF`, §1.5) are needed for hash constants and
byte manipulation. These all land in 0f Step 6.

### Tier 3: Abstractions (lands with 0g)

Trait hierarchies, @derive, and the abstractions that make the
stdlib ergonomic. Also absorbs what was previously 0h Checkpoint 1.

```
stdlib/
  foldable.kea     -- Foldable trait + associated Item type
  iterator.kea     -- Iterator trait + lazy iteration
  derive/show.kea  -- @derive(Show) recipe
  derive/eq.kea    -- @derive(Eq) recipe
  derive/ord.kea   -- @derive(Ord) recipe
  codec.kea        -- Encode/Decode traits
  json.kea         -- JSON via Encode/Decode
  sorted_map.kea   -- SortedMap (Ord supertrait constraint)
  sorted_set.kea   -- SortedSet
  format.kea       -- String formatting, pretty-printing
  http/server.kea  -- Http server: listen, row-polymorphic middleware
                    -- (nested module: Http.Server — test case for 0d1 module system)
  http/router.kea  -- Basic routing utilities
  shutdown.kea     -- Shutdown effect for graceful server termination
```

**~1000-1400 additional lines.**

**@derive lands here.** Moved from 0h. Tightly coupled to the
trait system and associated types from 0g. @derive(Show, Eq, Ord)
for structs and enums.

**Supertraits enable Ord : Eq.** The Tier 0 Ord trait was
standalone. Now it properly requires Eq.

**This tier completes the self-hosting stdlib.** After Tier 3,
the compiler has: collections (Map, Vector, Set), IO (file
read/write, stdout), error handling (Fail, catch, Result),
traits (Show, Eq, Ord, Foldable, Iterator), serialization
(JSON via Encode/Decode), and formatting. Enough to write a
compiler.

## Intrinsics

Stdlib functions that bottom out in runtime operations use
`@intrinsic`:

```kea
struct String
  @intrinsic("__kea_string_length")
  fn length(self: String) -> Int

  @intrinsic("__kea_string_concat")
  fn concat(self: String, other: String) -> String
```

Codegen recognizes `@intrinsic` and emits a call to the named
runtime function instead of compiling a Kea body. The runtime
functions are Rust code linked into the JIT/AOT module.

**Intrinsic sets by tier:**

| Tier | Intrinsics |
|------|-----------|
| 0 | String ops, alloc/free, print (debug) |
| 1 | IO syscalls (read/write/stdout/stderr), clock, TCP/TLS (Net) |
| 2 | Ptr ops (read/write/alloc/free/offset) |
| 3 | None (pure Kea, builds on Tier 0-2 intrinsics) |

## Stdlib-as-test principle

Every tier is a test of the phase that enables it:

| Tier | Tests |
|------|-------|
| 0 | Enums, pattern matching, closures, recursion, generics, trait dispatch, module system |
| 1 | Effect declarations, handler compilation, evidence passing, IO runtime, Net, HTTP client, Stream |
| 2 | Unique T, move checking, Ptr/@unsafe, refcounting, reuse analysis |
| 3 | GADTs, associated types, supertraits, @derive recipes, HTTP server, row-polymorphic middleware |

If the stdlib compiles and its tests pass, the phase works.

## Definition of Done (per tier)

**Tier 0:** Option, Result, List, String, Int, Float, Eq, Ord,
Show exist as `.kea` files. A user program can `use List` and
call `List.map`. At least 20 tests exercising stdlib functions.

**Tier 1:** IO, Net, Http (client), Stream, State, Log, Reader
exist with working handlers. A program can make an HTTP request,
read a file, process it with State, and write output. Test
handlers for Net return canned responses with zero network access.
At least 15 handler tests.

**Tier 2:** Vector and HAMT Map replace linked-list for production
use. Benchmark comparison: HAMT Map within 5x of Rust HashMap for
10K-entry lookup.

**Tier 3:** @derive(Show, Eq, Ord) works on structs and enums.
Foldable/Iterator enable `list.fold(0, |a, b| -> a + b)`. JSON
round-trips through Encode/Decode. HTTP server with row-polymorphic
middleware composition — at least one middleware that adds a context
field and one that adds an effect, composed together with correct
type inference. Stdlib is sufficient for compiler self-hosting.

## HTTP

HTTP is stdlib, not a framework dependency. Most programs are HTTP
clients before they're servers. The effect system makes the API
naturally testable and composable.

### Client (Tier 1)

Lands alongside IO. Minimal request/response:

```kea
struct Http
  fn get(_ url: String) -[Net, Fail HttpError]> Response
  fn post(_ url: String, body: Body) -[Net, Fail HttpError]> Response
  fn request(_ req: Request) -[Net, Fail HttpError]> Response
```

Note `Net`, not `IO` — the effect signature documents that this
touches the network and nothing else. Test handlers return canned
responses with zero network access.

Tier 3 adds `.json(T)` deserialization via the `Codec` trait,
and a reusable client struct with retry/timeout/auth via
functional update:

```kea
let client = Http.client()
  ~{ base_url: "https://api.example.com" }
  ~{ auth: Bearer(token) }
  ~{ retry: Retry.exponential(max: 3) }
```

### Server (Tier 3)

Lands when middleware composition and streaming patterns are solid.
A server handler is a function — the `net/http` insight:

```kea
struct Server
  fn listen(_ port: Int, _ handler: Request -[e]> Response)
      -[Net, Shutdown, e]> Unit
```

The effect variable `e` propagates handler effects through the
server. If the handler does `[DB, Log]`, the server's signature
shows `[Net, Shutdown, DB, Log]`. The `Shutdown` effect models
graceful shutdown — the caller decides the policy via handler.

**Row-polymorphic request context.** This is the genuinely novel
part. Middleware transforms the request's row type:

```kea
-- Auth middleware: removes user requirement, adds Net + Fail AuthError
fn auth(_ next: { user: User | r } -[e]> Response)
    -> { headers: Headers | r } -[Net, Fail AuthError, e]> Response
  |req| ->
    let token = req.headers.get("Authorization")
      .ok_or(AuthError.missing_token())?
    let user = Auth.verify(token)?
    next(req~{ user })
```

The middleware takes a handler that *requires* `user: User` in
its context and returns a handler that doesn't — it provides the
user by verifying the auth token and adding the field via `~{}`.
The row variable `r` preserves all other context fields.

Stack middlewares and the types compose:

```kea
let stack = App.handle         -- needs { user: User, db: Pool, request_id: String }
  |> Middleware.auth           -- removes user, adds Net + Fail AuthError
  |> Middleware.db_pool        -- removes db, adds Net
  |> Middleware.request_id     -- removes request_id, adds Clock
-- Final: needs {} (nothing), effects [Net, Fail AuthError, Log, Clock]
```

Forget a middleware? Type error — `user: User` is missing from
the context. Wrong order? Type error — a middleware tries to read
a field that hasn't been added yet. **Compile-time middleware
ordering validation from row polymorphism.** No existing framework
has this.

**Error message quality is load-bearing here.** The raw type error
is row unification failure. The user-facing error must be:

```
error[E0312]: handler requires `user: User` in request context
  --> src/server.kea:15:3
   |
15 |   Server.listen(8080, stack)
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^ missing field `user` in request context
   |
   = help: add `Middleware.auth` to the middleware stack
```

Not "row unification failed: expected `{ user: User | r42 }`."
The error message is the difference between a headline feature
and an academic curiosity. This is 0h territory but is a hard
requirement for the HTTP server to be usable.

**Context fields vs effects.** These are complementary, not
competing. Context fields are *values*: a pool handle, a user
struct, a request ID string. Effects are *capabilities*: the
ability to query, to log, to read the clock. Middleware provides
the value (adds `db: Pool` to the context row); the effect system
tracks what the handler does with it (`DB.query` operations that
the pool connection backs). A handler receives `db: Pool` through
the row and uses it through `DB` effect operations.

**Connection-scoped effect handlers.** Per-request handlers *are*
request scoping:

```kea
fn serve(_ req: Request) -[Net]> Response
  handle App.handle(req)
    DB.query(sql, params) -> resume pool.execute(sql, params)
    Log.log(level, msg) -> resume logger.log(level, "[{req.id}] {msg}")
```

Every request gets its own handler scope. Logging automatically
includes the request ID. DB queries route to the pool. No Context
parameter threading, no request-scoped DI container. When the
handler scope exits, the request scope is done.

### What's NOT in stdlib

Routing libraries, template engines, ORM layers, WebSocket
frameworks — these are ecosystem packages. The stdlib provides
the HTTP primitives and the language provides the composition
mechanisms (effects, handlers, rows, grammars). The framework
is what the community builds. The stdlib is the foundation that
makes the framework thin.

### Stream effect (Tier 1, general-purpose)

`Stream` is not HTTP-specific. It belongs in core alongside IO.

Tier 1 ships a monomorphic `Stream Bytes` — parameterized effects
require the `Eff` kind from 0g. The type parameter generalizes
in Tier 3 when `Stream T` becomes possible:

```kea
-- Tier 1: monomorphic
effect Stream
  fn chunk(_ data: Bytes) -> Unit
  fn done() -> Never
    -- Never = uninhabited. Code after done() is unreachable.
    -- The handler catches done() and doesn't resume —
    -- the producer is finished.

-- Tier 3 (after 0g): parameterized
effect Stream T
  fn chunk(_ data: T) -> Unit
  fn done() -> Never
```

Consumers: HTTP streaming responses, file reading, database
cursors, CSV parsing, WebSocket messages.

**Backpressure through effect suspension.** The handler side is
where `Stream` gets interesting:

```kea
handle large_download(req)
  Stream.chunk(data) ->
    Http.write_chunk(conn, data)  -- blocks if TCP send buffer full
    resume ()                      -- resumes producer only when ready
```

The effect handler *is* the backpressure mechanism. `resume` only
fires when the downstream is ready. The producer suspends
automatically at each `Stream.chunk` call. No reactive streams
library, no `Flow` or `Publisher/Subscriber` — just normal effect
handler semantics doing what backpressure frameworks do with a
fraction of the API surface.

### Shutdown (Tier 3, with server)

Graceful shutdown is an effect, not a special server mode:

```kea
effect Shutdown
  fn on_signal(_ sig: Signal) -> ShutdownAction
```

The caller decides the policy via handler:

```kea
handle Server.listen(8080, stack)
  Shutdown.on_signal(SigInt) -> resume Drain(timeout: Duration.seconds(30))
  Shutdown.on_signal(SigTerm) -> resume Immediate
```

`Server.listen` returns `Unit` instead of `Never` because
shutdown is an expected exit path. The effect signature documents
that the server can be shut down, and the handler determines how.

## Tier-0 List Runtime Notes

`List` is now available in repo stdlib on the bootstrap runtime path as a
heap-node recursive sum carrier (`Nil | Cons(Int, List)`), with execute-path
coverage for `map`, `filter`, `fold`, `length`, and `is_empty`.

Current posture:

- Correctness-first representation: linked heap nodes via existing 0d aggregate
  lowering and recursive payload loads.
- Mixed sum runtime handling in codegen supports unit+payload variants in the
  same sum during tag loads.
- RC is conservative for mixed-representation sums during bootstrap to avoid
  immediate-tag misclassification.

Deferred to 0f+ (performance/memory optimization, not semantic blockers):

- Reuse analysis for in-place list transforms when ownership is unique.
- More precise RC insertion/removal for recursive aggregate paths.
- Specialized contiguous collections (`Vector`) as a separate data structure.

---

## Open Questions

- Should Tier 0 List be `type List A = Cons(A, List A) | Nil`
  (classic algebraic) or a struct wrapping a recursive enum?
  Struct gives a namespace for methods via UMS. (Proposal: struct
  wrapping the enum, methods on the struct.)
- When Tier 2 Vector lands, does it replace the `List` name or
  coexist as `Vector`? (Proposal: coexist. `List` stays as the
  linked list, `Vector` is the array. Users choose based on
  access pattern. The prelude exports both.)
- Should the stdlib directory structure be flat (`stdlib/list.kea`)
  or nested (`stdlib/collections/list.kea`)? (Proposal: flat for
  Tier 0-1, introduce nesting in Tier 2-3 as the stdlib grows.)

## Progress
- 2026-02-27 18:20: Bootstrapped initial real stdlib repository modules while closing 0d1: added `stdlib/prelude.kea`, `stdlib/option.kea`, and `stdlib/text.kea` (`Text.length` is intrinsic-backed via `@intrinsic("strlen")`). Added execute-path integration coverage through the module system (`Option.unwrap_or` + `Text.length`) plus real prelude autoload coverage against repo `stdlib/`.
- 2026-02-27 18:41: Explicitly deferred heap-list Tier 0 implementation from 0d1 closeout after validating current 0d codegen cannot lower builtin heap-list carriers (`List(Int)` runtime lowering gap). `List` lands in this brief once list runtime shape (linked-list carrier lowering) is available; do not ship placeholder/fake `List.map` implementations.
- 2026-02-27 18:58: Added initial Tier-0 numeric/order module files: `stdlib/int.kea` (`abs`, `min`, `max`, `clamp`), `stdlib/float.kea` (`fabs`), and `stdlib/order.kea` (`Ordering`, `reverse`, `reversed_less_is_greater`). Added execute-path integration regression `compile_and_execute_real_stdlib_int_module_exit_code` proving real repo stdlib import + execution for `Int` through the 0d1 module pipeline.
- 2026-02-27 19:03: Validated this slice with `mise run check` and `PKG=kea mise run test-pkg` (105/105 passing in `kea`). Observed and deferred two backend/runtime gaps while probing broader Tier-0 coverage: module-qualified sum constructors from stdlib modules are not callable as value expressions (`Order.Less`), and float-heavy execute paths currently crash in compiled mode (SIGSEGV). Keep `float/order` modules in-tree, but gate execute-path coverage on currently stable int/option/text paths until those gaps are addressed.
- **Next:** land `eq`, `ord`, and `show` trait module skeletons with compile-time coverage; then add stable execute-path tests that avoid currently known constructor/float runtime gaps while keeping Tier-0 progress honest.
- 2026-02-27 19:54: Completed trait-module skeleton slice: added `stdlib/eq.kea`, `stdlib/ord.kea`, `stdlib/show.kea` with concrete top-level bootstrap functions (`eq`, `compare`, `show`) so module imports are concrete and compile-time checked. Added execute integration regression `compile_and_execute_real_stdlib_trait_modules_import_exit_code` and validated import resolution for `use Eq`, `use Ord`, `use Show`.
- 2026-02-27 19:54: Closed the module-qualified constructor gap for stdlib enums: `Order.Less` now resolves through module-owned sum types end-to-end (type inference + HIR/MIR lowering + execute path). Added execute regression `compile_and_execute_real_stdlib_order_module_qualified_constructor_exit_code`.
- 2026-02-27 19:54: Added real stdlib float execute-path regression `compile_and_execute_real_stdlib_float_module_exit_code` (`use Float`, `Float.fabs`) and validated it alongside existing real stdlib integration tests. Current repro no longer exhibits the previously observed float execute-path crash.
- 2026-02-27 19:54: Validation checkpoint: `mise run check`, `PKG=kea-infer mise run test-pkg` (608/608), and `PKG=kea mise run test-pkg` (108/108) all pass after this slice.
- 2026-02-27 20:07: Probed further non-list Tier-0 expansion (`Option.is_some/is_none` helpers, `Result.unwrap_or/is_ok/is_err`) and found two runtime gaps: (1) `Option.is_none(None)` currently hits compiled-path codegen failure (`non-unit function returned without value`), and (2) `Result.unwrap_or(Ok(...), fallback)` returns fallback on the execute path (runtime behavior mismatch). Backed out those unstable stdlib additions to keep Tier-0 surface honest and green; keep these as explicit blocked follow-ups instead of shipping incorrect stdlib semantics.
- 2026-02-27 20:07: Re-validated stable real-stdlib execute gates after rollback (`Prelude`, `Option.unwrap_or`, `Text.length`, `Int`, `Float.fabs`, `Order.Less`, trait module imports) with targeted `compile_and_execute_real_stdlib_*` CLI tests passing.
- 2026-02-27 20:10: Landed Int bitwise surface end-to-end for bootstrap Int64: added builtin Int method registration in typeck (`bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shift_left`, `shift_right`, `shift_right_unsigned`), MIR ops (`MirBinaryOp::{BitAnd, BitOr, BitXor, ShiftLeft, ShiftRight, ShiftRightUnsigned}` + `MirUnaryOp::BitNot`), Cranelift lowering (`band/bor/bxor/bnot/ishl/sshr/ushr`), stdlib `int.kea` methods, and execute-path regressions (`42.bit_and(15)=10`, `1.shift_left(3)=8`, `255.bit_not()=-256`, unsigned shift sanity).
- 2026-02-27 20:10: Fixed a real stdlib compile-path regression uncovered by the new Int methods: HIR function lowering now guards against env-derived function type arity drift and rebuilds declaration function types from annotations when arity mismatches declaration parameters. This removed `invalid MIR value %0 referenced in bit_and` on `compile_and_execute_real_stdlib_int_module_exit_code`.
- 2026-02-27 20:17: Closed the previously tracked `Option.is_none(None)` compiled-path failure (`non-unit function returned without value`) by teaching HIR lowering to map `None` literals to constructor tags instead of falling back to raw AST. Added real-stdlib execute regression `compile_and_execute_real_stdlib_option_predicates_exit_code`.
- 2026-02-27 20:17: Added `Option` predicate helpers in `stdlib/option.kea` (`is_some`, `is_none`) using `None` + wildcard branches, which is correct for current mixed Option runtime representation (unit variant immediate tag, payload variant boxed) without relying on unsupported payload-tag fast paths.
- 2026-02-27 20:24: Added `stdlib/result.kea` with Tier-0 helper surface (`unwrap_or`, `is_ok`, `is_err`) and execute-path integration regression `compile_and_execute_real_stdlib_result_helpers_exit_code` (`use Result` from repo stdlib).
- 2026-02-27 20:24: Fixed Result helper runtime divergence by marking `Result`-typed parameters as sum-tag eligible in MIR lowering (`lower_hir_function` param seeding), enabling constructor-tag checks to lower through `SumTagLoad` rewrites for pointer-backed `Result` values while leaving `Option` mixed-representation handling unchanged.
- 2026-02-27 20:47: Added explicit blocked List runtime gate in both docs and tests. New section “Blocked: Tier-0 List Runtime Prerequisites” now defines the exact runtime/codegen requirements for landing `stdlib/list.kea`. Added CLI regression `compile_project_reports_list_module_blocked_until_heap_runtime` that asserts `use List` fails with `module \`List\` not found` until real heap-list support lands (prevents placeholder/fake List modules from silently entering stdlib).
- 2026-02-27 20:50: Expanded `Text` Tier-0 surface with pure helpers in repo stdlib (`Text.is_empty`, `Text.non_empty`) and added execute-path regression `compile_and_execute_real_stdlib_text_helpers_exit_code`.
- 2026-02-27 20:50: Fixed backend external-call ABI conflict surfaced by the Text helper slice: external signature collection now canonicalizes call signatures at Cranelift ABI type level before conflict checks. This allows compatible source-level variants (e.g. `Dynamic` vs `String` for `strlen`) while still rejecting true ABI conflicts.
- 2026-02-27 19:55: Added `Order` helper surface (`is_less`, `is_equal`, `is_greater`, `compare_int`) in `stdlib/order.kea` with execute regression `compile_and_execute_real_stdlib_order_helpers_exit_code`, and fixed the compiled-path SIGSEGV by making codegen `SumTagLoad` treat unit-only sums as immediate-tag values (no heap dereference). Verified with `PKG=kea mise run test-pkg` (131/131) and `mise run check`.
- 2026-02-27 20:09: Unblocked recursive bootstrap List runtime: fixed mixed sum tag handling in codegen (`SumTagLoad` now distinguishes immediate unit tags vs payload pointers for mixed variants) and tightened MIR heap-management classification so only pointer-only sums emit retain/release in bootstrap RC paths.
- 2026-02-27 20:09: Landed `stdlib/list.kea` (linked-list carrier + `is_empty`, `length`, `map`, `filter`, `fold`) and replaced the old blocked-module regression with execute-path integration `compile_and_execute_real_stdlib_list_module_exit_code` (`use List` end-to-end through module loading + codegen).
- **Next:** expand Tier-0 stdlib breadth with execute-path coverage for remaining modules while tightening mixed-sum ownership handling for recursive aggregate paths.
