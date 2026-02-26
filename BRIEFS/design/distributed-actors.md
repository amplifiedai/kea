# Brief: Distributed Actors

**Status:** design
**Priority:** Phase 2-3 (after local actors work, after serialization)
**Depends on:** 0e-runtime-effects (local actor runtime), serialization (Encode/Decode), 0g-advanced-types (GADTs for typed protocols)
**Blocks:** nothing currently

## Motivation

Kea's actor model has the right primitives for distribution:
typed `Ref Msg`, capability effects (`Send`, `Spawn`), the
`Encode`/`Decode` trait system, and GADT-typed protocols. The
effect system gives us something Erlang/OTP doesn't — compile-time
enforcement of serialization boundaries, typed messages, and
effect-tracked network access.

This brief captures the design constraints while the foundational
decisions (capability effects, mailbox configuration, `Ref` typing)
are being made in 0b-0e. Nothing here should be built until local
actors are solid and benchmarked.

## The Competitive Position

Kea can't match BEAM's runtime maturity in v1. The advantage is
the type system:

| Guarantee | Erlang/OTP | Kea |
|-----------|-----------|-----|
| Message type safety | Runtime crash on mismatch | Compile error |
| Serialization boundary | Runtime discovery | `Encode` trait enforced at type level |
| Effect tracking | None | `-[Send]>` tracks network access |
| Protocol typing | Untyped `gen_server:call` → `term()` | GADTs: reply type statically known |
| Pure state transitions | Convention | `fn handle(self, msg) -> Self` — compiler-verified |

## Key Design Decisions

### Send is a runtime transport decision, not a handler swap

`Send` is a capability effect. It compiles to a direct runtime
call. The runtime inspects the `Ref` to determine local vs remote
transport. This is NOT a user handler — it's the runtime choosing
the transport based on `Ref` locality.

- `ref <- msg` — runtime checks ref, dispatches locally or
  serializes + sends over the network
- The effect signature doesn't change (`-[Send]>` either way)
- User handlers for `Send` remain legal for testing/simulation
- The runtime controls serialization, batching, backpressure

This aligns with the capability effect stance: ordinary in types,
direct-call in production, handler-interceptable for tests.

### No distributed refcounting

Remote refs are proxy handles, not refcounted pointers. Erlang
got this right — PIDs are lightweight identifiers, not GC'd
pointers.

- **Local `Ref`:** refcounted pointer to a mailbox (existing model)
- **Remote `Ref`:** `(NodeId, ActorId, Epoch)` proxy handle.
  The local runtime holds the real ref; the remote side holds
  a proxy with a lease or monitor.
- **Liveness:** monitoring, not distributed GC. `Monitor.watch(ref)`
  gives you a `Down` message when the remote actor dies.
- **Ref transfer:** when a `Ref` crosses a `Send` to a remote
  node, the serialization layer wraps it in a proxy. The type
  system ensures the message type satisfies `Encode`.

### Encode constraint at the boundary

When a `Ref` could be remote, the message type must satisfy
`Encode + Decode`. The compiler enforces this:

```kea
-- Local-only actor: no Encode required
fn send_local(_ ref: Ref Msg, _ msg: Msg) -[Send]> Unit
  ref <- msg

-- Remote-capable actor: Encode required
fn send_remote(_ ref: RemoteRef Msg, _ msg: Msg) -[Send]> Unit
  where Msg: Encode, Msg: Decode
  ref <- msg  -- runtime serializes if needed
```

Open question: should `Ref` itself carry a locality marker
(`Ref Msg` vs `RemoteRef Msg`), or should all `Ref` be
potentially remote with `Encode` enforced universally? The
Erlang model (all PIDs are location-transparent) is simpler
but forces `Encode` on all message types.

### Monitoring and links (Erlang-style)

- `Monitor.watch(ref)` → receive `Down(ref, reason)` when the
  actor dies
- `Link.link(ref)` → bidirectional: if either dies, the other
  gets a signal
- Works across node boundaries (monitor messages are sent over
  the network)
- `Down` is a regular message in the actor's `Msg` type (or a
  system message handled by the supervision layer)

### Supervision

Supervision trees transfer directly from Erlang/OTP, but
type-checked:

- `Supervisor` trait with typed child specs
- Restart strategies: `OneForOne`, `OneForAll`, `RestForOne`
- Restart intensity limits (max restarts per time window)
- Partition behavior: what happens when a node becomes
  unreachable? (This is the hardest distributed systems
  question.)

Depends on the supervision trait API design (tracked separately
in INDEX.md).

## What the Effect System Gives Distribution

1. **Serialization safety.** The compiler rejects sending a
   closure or non-`Encode` value to a remote actor. Erlang
   discovers this at runtime.

2. **Network effect tracking.** Functions that do remote sends
   have `-[Send]>` in their signature. Pure functions can't
   accidentally trigger network traffic.

3. **Test isolation.** Handle `Send` in tests to mock remote
   actors locally. The effect system makes this compositional —
   swap the handler, not the code.

4. **Protocol safety via GADTs.** Request-response patterns where
   the reply type is statically known:

   ```kea
   enum Request A where
     GetUser(UserId, Reply User): Request User
     ListUsers(Reply (List User)): Request (List User)
   ```

   The GADT constrains the reply type. A remote `call` returns
   the right type without runtime casting.

## Implementation Path (Sketch)

### Phase 1: Local actors (0e)
- `Ref Msg` as local refcounted mailbox pointer
- `Send.tell` as direct runtime call
- Mailbox configuration (Bounded/Unbounded/Dropping)
- Monitoring within a single node

### Phase 2: Serialization + remote refs
- `Encode`/`Decode` traits (serialization brief)
- `RemoteRef` or location-transparent `Ref`
- Proxy handle with `(NodeId, ActorId, Epoch)`
- Cross-node message delivery (TCP/QUIC transport)
- Remote monitoring (Down messages over network)

### Phase 3: Supervision + clustering
- `Supervisor` trait with typed child specs
- Node discovery and cluster membership
- Partition handling strategy
- Benchmarking: mailbox throughput, cross-node latency,
  supervision restart overhead

## Open Questions

- **Ref locality transparency vs explicit typing.** Should all
  `Ref` be potentially remote (Erlang model: simpler, forces
  `Encode` everywhere) or should local/remote be distinguished
  in the type (`Ref` vs `RemoteRef`: more precise, more ceremony)?
  Proposal: start with explicit `RemoteRef`, consider unification
  later based on usage patterns.

- **Transport protocol.** TCP? QUIC? Both? The runtime should
  abstract this, but the choice affects latency and reliability
  characteristics. Erlang uses a custom TCP-based protocol
  (distribution protocol). QUIC might be better for modern
  deployments.

- **Node identity and discovery.** Static config? DNS? mDNS?
  Consul/etcd? This is ops infrastructure, not language design,
  but the runtime needs a pluggable discovery mechanism.

- **Partition semantics.** What happens when a node becomes
  unreachable? Erlang's `net_kernel` has `connect`/`disconnect`
  semantics and `nodedown` messages. Kea needs equivalent
  semantics. The CAP theorem applies — what trade-offs do we
  make?

- **Hot code loading.** Erlang's killer feature for zero-downtime
  deploys. Not in scope for v1, but the actor model should not
  preclude it. The `fn handle(self, msg) -> Self` pattern is
  compatible — you swap the function, the state carries over.

## Non-Goals (v1)

- Matching BEAM's scheduler maturity (preemptive scheduling,
  reduction counting)
- Distributed ETS/DETS equivalent
- Hot code loading
- Multi-language node interop (Erlang distribution protocol)
