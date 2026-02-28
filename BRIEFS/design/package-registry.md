# Brief: Package Registry

**Status:** design
**Priority:** Phase 0 (Git deps) → Phase 1 (registry MVP) → Phase 2 (policies)
**Depends on:** 0d1 (module system), phase-1a-ffi (for native deps)
**Blocks:** ecosystem growth, third-party packages
**Also read:**
- [Packaging, FFI, comptime](packaging-ffi-comptime.md) — parent design doc
- [Effects as platform](effects-platform-vision.md) — effects as permissions context
- [docs/IDIOMS.md](../../docs/IDIOMS.md) — effect conventions that drive permission model

## Motivation

A package registry is a trust infrastructure. Users download code
written by strangers and run it on their machines. Every package
manager in history has had to learn this the hard way:

- **npm (2016-present):** left-pad (availability), event-stream
  (supply chain), ua-parser-js (account compromise), 500K+ malicious
  packages by 2024. Root cause: install scripts run arbitrary code.
- **PyPI (2017-present):** Typosquatting at scale. `python3-dateutil`
  stealing SSH keys. Root cause: `setup.py` runs arbitrary code.
- **crates.io (2023):** crates-io-index repository compromise scare.
  Mitigated by design (content-addressed), but Rust's `build.rs`
  is the same class of vulnerability as npm install scripts.
- **RubyGems (2019):** Backdoored `rest-client` gem via account
  takeover. Root cause: no MFA enforcement, long-lived API tokens.

Kea has a structural advantage no other language has: the effect
system proves what packages can and cannot do. A pure package
provably cannot phone home, read your filesystem, or exfiltrate
data. This isn't a sandbox or a policy — it's a type error.

But effects alone don't solve every registry problem. Hosting,
naming, immutability, version resolution, governance — these are
infrastructure and social problems that need careful design.

## Phase 0: Git Dependencies (lands with 0d1 module system)

**Zero infrastructure. Works today.**

```toml
# kea.toml
[package]
name = "my-app"
version = "0.1.0"
kea = "0.1"

[dependencies]
http = { git = "https://github.com/kea-lang/http", tag = "v0.1.0" }
json = { git = "https://github.com/kea-lang/json", rev = "abc1234" }
utils = { path = "../my-utils" }
```

```toml
# kea.lock (generated, checked into repo)
[[package]]
name = "http"
source = "git+https://github.com/kea-lang/http?tag=v0.1.0"
rev = "abc1234def5678..."
hash = "sha256:..."

[[package]]
name = "json"
source = "git+https://github.com/kea-lang/json"
rev = "abc1234"
hash = "sha256:..."
```

### How it works

1. `kea pkg add http --git https://github.com/kea-lang/http --tag v0.1.0`
2. Kea clones the repo, checks out the tag/rev
3. Computes content hash of the Kea source (ignoring `.git`, etc.)
4. Writes `kea.lock` with rev + hash
5. On build: fetch if not cached, verify hash, compile

### What this gives us

- **Reproducible builds.** `kea.lock` pins exact revisions and
  content hashes. Same lock file = same source = same build.
- **No registry to operate.** Dependencies are Git repos. GitHub,
  GitLab, Codeberg, self-hosted — anywhere.
- **Path dependencies for local development.** Monorepo and
  multi-repo workflows both work.
- **Transitive dependencies.** Each package has its own `kea.toml`.
  Kea resolves the full dependency graph.

### What this doesn't give us

- Package discovery (no search, no browse)
- Semver resolution (you pin exact revisions)
- Effect metadata (computed locally, not shared)
- Community (no central place to publish/find packages)

That's fine. Early Go didn't have a registry either. Git imports
worked until the community needed more. The module system and
manifest format are the stable foundation — the registry layers
on top without changing how users write `kea.toml`.

## Phase 1: Registry MVP (lands during/after Phase 1)

**A hosted registry with effect-aware metadata.**

### Core features

**1. Publish and fetch packages.**

```bash
kea pkg publish              # publish current package
kea pkg add json             # add dependency from registry
kea pkg add json@0.5         # add specific version
kea pkg update               # update to latest compatible versions
kea pkg search "json parser" # search registry
```

**2. Immutable, content-addressed versions.**

Once published, a version's source cannot change. The registry
stores the content hash (SHA-256 of the source tree). Every
client verifies the hash on fetch. If it doesn't match, the build
fails.

```
Registry stores: (name, version) → (source tarball, sha256 hash)
Client verifies: sha256(fetched source) == hash from registry
```

**3. Effect signatures computed and displayed.**

This is the killer feature. The registry compiles every published
package and extracts the effect signature of every public function.
The registry UI shows:

```
json v0.5.0
├── parse: String -[Fail JsonError]> Value          [PURE + FAIL]
├── stringify: Value -> String                       [PURE]
└── parse_file: String -[IO, Fail JsonError]> Value  [IO + FAIL]

Effects: Fail JsonError, IO (parse_file only)
Unsafe: none
```

Badges on the package page:
- **PURE** — no IO, no Net, no effects beyond Fail
- **IO** — touches filesystem
- **NET** — does networking
- **UNSAFE** — contains `unsafe` blocks

These are compiler-verified, not self-declared.

**4. Effect diff on version bumps.**

When a new version is published, the registry computes the diff
in effect signatures:

```
json v0.5.0 → v0.6.0

ADDED EFFECTS:
  + parse_streaming: added Net effect (was not present in v0.5.0)

REMOVED FUNCTIONS:
  - parse_lenient: removed

UNCHANGED:
  parse: String -[Fail JsonError]> Value  (no change)
  stringify: Value -> String              (no change)
```

If a package that was previously pure adds IO or Net, the registry
flags it prominently. This is an automatic security signal — no
CVE database needed, no human audit.

**5. Transparency log.**

Every publish event is recorded in an append-only, tamper-evident
log (same principle as Go's `sum.golang.org` and Certificate
Transparency).

```
Log entry:
  timestamp: 2027-03-15T14:23:00Z
  action: publish
  package: json
  version: 0.6.0
  hash: sha256:abc123...
  publisher: github:kea-lang (OIDC)
  effects: [Fail JsonError, IO, Net]
  effects_diff: [+Net (parse_streaming)]
```

Anyone can audit the log. Third-party monitors can watch for
suspicious patterns (pure package suddenly adding Net, unknown
publisher taking over a popular package).

**6. Trusted publishing.**

OIDC-based authentication from CI environments (GitHub Actions,
GitLab CI). No long-lived API tokens.

```yaml
# .github/workflows/publish.yml
- uses: kea-lang/publish-action@v1
  with:
    # No token! Uses GitHub's OIDC identity
    registry: https://registry.kea-lang.org
```

The registry trusts the CI provider's identity assertion. The
publish is tied to a specific repo + workflow + commit. Stolen
credentials are useless because there are no credentials to steal.

**7. Lockfile verification.**

```toml
# kea.lock
[[package]]
name = "json"
version = "0.5.0"
source = "registry+https://registry.kea-lang.org"
hash = "sha256:abc123..."
effects = ["Fail JsonError"]
```

`kea build` verifies:
- Content hash matches
- Effect signature matches (defence in depth — the compiler also
  checks, but failing early is better)

### What this defers

- Effect policies (Phase 2)
- Fine-grained effect permissions
- Package namespacing decision (see Open Questions)
- Native dependency management
- Mirror/federation protocol

## Phase 2: Effect Policies (lands Phase 2+)

**Project-level effect budgets enforced by the compiler.**

```toml
# kea.toml
[policy]
# Only these effects are allowed from dependencies
allow = ["Fail"]

# These are explicitly denied (even transitively)
deny = ["Net", "Spawn"]

# Warn but don't fail on these
warn = ["IO"]

# No unsafe code in dependencies
deny_unsafe = true

# Exceptions (trusted packages that need more permissions)
[policy.exceptions]
http = { allow = ["Net", "IO"] }
sqlite = { allow = ["IO"], allow_unsafe = true }
```

### How it works

1. `kea build` resolves all dependencies
2. For each dependency, checks its effect signature against the policy
3. If a dependency's effects exceed the policy, it's a compile error:

```
error[E0801]: Dependency `analytics` violates effect policy
  ┌─ kea.toml:12:1
  │
  │ [policy]
  │ deny = ["Net"]
  │
  │ Package `analytics` v1.2.0 uses effect `Net`:
  │   analytics::track_event -[Net, Fail AnalyticsError]> Unit
  │
  = help: add an exception: [policy.exceptions]
  =        analytics = { allow = ["Net"] }
  = note: this package was previously pure (v1.1.0 had no Net effect)
```

### Effect budget for CI/audit

```bash
kea pkg audit                    # show all dependency effects
kea pkg audit --deny Net         # fail if any dep uses Net
kea pkg audit --diff v1.1.0      # show effect changes since v1.1.0
```

Output:
```
Dependency effect audit:
  json v0.5.0          [PURE + FAIL]  ✓
  http v1.2.0          [NET, IO, FAIL] ✓ (exception)
  analytics v1.2.0     [NET, FAIL]    ✗ DENIED
  crypto v2.0.0        [PURE]         ✓
  sqlite v0.3.0        [IO, FAIL]     ⚠ WARNING (IO)
    └── contains unsafe  ✓ (exception)

2 pure, 1 excepted, 1 warning, 1 denied
```

This is `npm audit` but machine-verified, not advisory-based. The
compiler proves the effects; the policy gates them. No false
positives, no CVE lag.

## Open Questions

### 1. Naming: Flat vs Namespaced

**Flat (crates.io model):**
```toml
[dependencies]
http = "1.0"
json = "0.5"
```
- Simple, clean imports
- Name squatting is a real problem (crates.io has thousands of
  squatted names)
- Requires active moderation or name reservation policy

**Namespaced (npm scopes model):**
```toml
[dependencies]
"@kea-lang/http" = "1.0"
"@chris/json" = "0.5"
```
- No squatting — you own your namespace
- Uglier imports, more typing
- Discoverability harder (which `json` package is the right one?)

**Go model (no central namespace):**
```toml
[dependencies]
"github.com/kea-lang/http" = "1.0"
```
- No registry needed for naming
- URLs are ugly but unambiguous
- Tied to hosting provider (what if GitHub goes away?)

**Hybrid proposal: flat with verified publishers.**

```toml
[dependencies]
http = "1.0"           # from verified publisher kea-lang
json = "0.5"           # from verified publisher chris
```

Registry UI shows verified publisher. `kea pkg info http` shows
who owns it. Popular names require verification (linked GitHub
org, domain ownership, etc.). This is roughly what crates.io is
moving toward with namespaces RFC (2025).

### 2. Hosting and Operations

**Who runs the registry?**

Options:
- **Foundation model (crates.io, hex.pm):** A non-profit runs it,
  funded by corporate sponsors and donations. Requires a legal
  entity and ongoing fundraising.
- **Company model (npm/GitHub):** A company runs it, funded by
  commercial offerings. Risk: acqui-hired, enshittified, or
  abandoned.
- **Federated model (Go):** No single registry. Proxies cache
  packages. A central index provides discovery and checksums.
  Lowest operational burden but hardest to get right.
- **Cloud-hosted with CDN:** Static file hosting (S3 + CloudFront
  or equivalent). The registry is just a tarball store + metadata
  API. Low cost, high availability.

**Practical starting point:** Static hosting. The registry is an
API that serves tarballs and metadata. No dynamic computation
needed for fetches (effect computation happens at publish time).
Host on commodity cloud storage. The transparency log can be a
Git repo (like Go's `sum.golang.org` started).

Cost estimate for a small ecosystem (1000 packages, 100 versions
each, average 50KB source):
- Storage: ~5GB → negligible ($0.12/month on S3)
- Bandwidth: dominated by CDN caching → $10-50/month
- Compute: publish-time compilation for effect extraction → a few
  minutes per publish, run on CI or a small server

This is fundable by one person with a credit card. It doesn't need
a foundation until the ecosystem is large enough to justify one.

### 3. Immutability and Yanking

**Hard immutability:** Once published, a version never changes and
never disappears. Builds are reproducible forever.

**Problem:** What about security vulnerabilities? What about
accidentally published secrets?

**Go's approach (recommended):**
- Versions are immutable in the content-addressed store
- Yanking marks a version as "retracted" in metadata
- Existing lockfiles that pin a retracted version still build
  (with a warning)
- New dependency resolution skips retracted versions
- The transparency log records the retraction

**For leaked secrets:** The content is out there (Git history,
caches, mirrors). Yanking the version is hygiene, not security.
The real fix is rotating the secret. The registry can flag
"this version was retracted for security — rotate any secrets
that may have been exposed."

**For legal takedowns:** Content removal is sometimes legally
required. The transparency log records the removal. The hash
entry stays (so builds that had the package can detect something
changed). The content is gone.

### 4. Version Resolution Strategy

**Minimal version selection (Go) vs maximal (Cargo/npm).**

Minimal: if you depend on `json >= 0.5`, you get exactly `0.5.0`
(the minimum version that satisfies the constraint). Reproducible
without a lockfile. Conservative — you don't get patches unless
you explicitly update.

Maximal: if you depend on `json >= 0.5` and `0.5.3` exists, you
get `0.5.3`. You get patches automatically. Less reproducible
without a lockfile. Can break if a "patch" introduces a bug.

**Recommendation: minimal version selection.** Go proved this
works. The lockfile adds an explicit update step (`kea pkg update`).
Security patches are handled by `kea pkg audit` flagging outdated
versions with known issues.

### 5. Unsafe Audit Trail

Packages containing `unsafe` blocks should have additional
scrutiny:

- **Prominent badge:** `UNSAFE` badge on registry page
- **Unsafe census:** `kea pkg audit --unsafe` lists all transitive
  dependencies with `unsafe`, showing the specific functions
- **Unsafe diff:** version bumps that add new `unsafe` blocks are
  flagged (similar to effect diff)
- **Optional policy:** `deny_unsafe = true` in `kea.toml`

This doesn't prevent `unsafe` — it's necessary for FFI and
performance-critical data structures. But it makes it visible
and auditable.

### 6. What About Native Dependencies?

Packages that depend on C libraries (via FFI) are the hardest
problem. The Kea compiler can build Kea source, but it can't
build C source.

Options:
- **System dependency declaration.** Package declares "requires
  libsqlite3" in `kea.toml`. User must install it. `kea build`
  checks for it and gives a clear error if missing.
- **Vendored source.** Package includes C source and a build
  recipe. But "build recipe" is dangerously close to build.rs.
- **Prebuilt binaries.** Package provides precompiled `.a` files
  for supported platforms. Safe (no build-time code execution)
  but limits platform support.

**Recommendation:** System dependency declaration for Phase 1.
It's honest about the dependency and doesn't introduce build-time
code execution. Vendored source and prebuilt binaries are Phase 2
features that need careful design to avoid reintroducing the
build.rs problem.

## What Effects Cannot Solve

Honesty section. Effects are powerful but not omniscient.

**Logic bugs in pure code.** A pure crypto library that uses a
weak algorithm or has a subtle implementation flaw is still pure.
Effects prove absence of IO, not correctness of computation.

**Resource exhaustion.** A pure function can loop forever or
allocate unbounded memory. Effects don't track computational
complexity. (An `Alloc` effect could bound allocation, but this
is Phase 3+ territory.)

**Unsafe escape hatches.** Code inside `unsafe` blocks can do
anything — raw memory access, inline assembly, direct syscalls.
The `unsafe` keyword makes this visible but doesn't prevent it.
The audit trail helps; it's not a proof.

**Coarse granularity.** `Net` means "does networking" but not
"connects to api.example.com on port 443." Finer effects are
possible (`Net("api.example.com")`) but add complexity. Start
coarse, refine if the ecosystem demands it.

**Social attacks.** Maintainer burnout, hostile takeovers, social
engineering. These are people problems. The transparency log and
OIDC publishing help (no tokens to steal, all actions logged) but
can't prevent a legitimate maintainer from going rogue within
their existing effect budget.

## Decisions to Lock Down

Before implementation, resolve:

1. **Flat vs namespaced naming** — affects every import in every
   Kea program forever. Hard to change later.
2. **Minimal vs maximal version resolution** — affects
   reproducibility guarantees.
3. **Registry hosting model** — who operates it, who pays.
4. **Native dependency story** — system deps vs vendored vs
   prebuilt.

## Implementation Sketch

### Phase 0 deliverables
- `kea.toml` manifest format (parser, schema)
- `kea.lock` lockfile format (generator, verifier)
- `kea pkg add --git <url>` command
- `kea pkg update` command
- Git dependency resolution (clone, checkout, hash, cache)
- Transitive dependency resolution
- Path dependency support

### Phase 1 deliverables
- Registry API (publish, fetch, search, metadata)
- `kea pkg publish` command with OIDC auth
- `kea pkg add <name>` from registry
- Effect extraction at publish time
- Effect badges on registry UI
- Effect diff on version bumps
- Transparency log
- Content-addressed storage with hash verification
- Yank/retract support

### Phase 2 deliverables
- `[policy]` section in `kea.toml`
- `kea pkg audit` command
- Effect policy enforcement at build time
- Unsafe audit trail
- Mirror/proxy protocol (for air-gapped environments)
- Native dependency declaration
