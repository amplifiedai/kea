# Brief: Algorithm Gallery

**Status:** ready (grows incrementally per phase)
**Priority:** v1 (parallel track)
**Depends on:** each algorithm depends on specific phase capabilities
**Blocks:** nothing (validation, not critical path)
**Also read before implementing:**
- [KERNEL §1.1](../../docs/spec/KERNEL.md) — numeric types, bitwise ops, overflow semantics
- [KERNEL §10.7-10.8](../../docs/spec/KERNEL.md) — while loops, @tailrec
- [stdlib-bootstrap](../in-progress/stdlib-bootstrap.md) — stdlib tiers and availability
- [0f-memory-model](0f-memory-model.md) — Unique, Ptr, @unboxed, fixed-width integers
- [performance-backend-strategy](../design/performance-backend-strategy.md) — benchmark targets

## Motivation

The algorithm gallery is a curated corpus of classic algorithms
implemented in Kea. It serves three purposes:

1. **Language validation.** Each algorithm exercises specific
   language features. If quicksort can't be written cleanly, the
   memory model has a gap. If FNV-1a hash is slow, bitwise ops
   need work. The gallery is a structured integration test for
   the language itself.

2. **Performance benchmarking.** Every algorithm has a benchmark
   alongside its implementation. These run in CI and establish
   performance baselines that track compiler improvements and
   catch regressions across phases.

3. **Exemplary code.** The gallery is how people learn Kea idioms.
   Every implementation should be the code you'd put in a textbook:
   clear, well-documented, idiomatic. Not golfed, not over-abstracted.
   Doc comments explain the algorithm, not just the code.

## Structure

```
tests/algorithms/
  welford.kea           -- online statistics (mean, variance)
  fnv1a.kea             -- FNV-1a hash function
  binary_search.kea     -- binary search on sorted Vector
  insertion_sort.kea     -- in-place insertion sort
  merge_sort.kea        -- functional merge sort (List-based)
  quicksort.kea         -- in-place quicksort (Vector + Unique)
  hamt.kea              -- hash array mapped trie (Map internals)
  ring_buffer.kea       -- fixed-capacity ring buffer
  priority_queue.kea    -- binary heap priority queue
  matrix_multiply.kea   -- dense matrix multiplication
  dot_product.kea       -- vector dot product
  utf8_validate.kea     -- UTF-8 byte sequence validation
  string_find.kea       -- substring search (naive + KMP)
  lru_cache.kea         -- LRU cache (Map + doubly-linked list)
```

Each file contains:
- `--|` doc comments explaining the algorithm and its complexity
- The implementation
- `test` blocks exercising correctness
- A benchmark function callable from `kea-bench`

### Example structure

```kea
--| Welford's online algorithm for computing running mean and
--| variance in a single pass. Numerically stable — avoids the
--| catastrophic cancellation of naive sum-of-squares.
--|
--| Complexity: O(n) time, O(1) space.

fn welford(xs: List) -> (Float, Float)
  welford_step(xs, 0, 0.0, 0.0)

fn welford_step(xs: List, n: Int, mean: Float, m2: Float) -> (Float, Float)
  case xs
    Nil ->
      if n < 2
        (mean, 0.0)
      else
        (mean, m2 / Int.to_float(n - 1))
    Cons(x_int, rest) ->
      let x = Int.to_float(x_int)
      let n1 = n + 1
      let delta = x - mean
      let new_mean = mean + delta / Int.to_float(n1)
      let delta2 = x - new_mean
      let new_m2 = m2 + delta * delta2
      @tailrec welford_step(rest, n1, new_mean, new_m2)

test "welford empty list"
  let result = welford(Nil)
  assert fst(result) == 0.0

test "welford single element"
  let result = welford(Cons(5, Nil))
  assert fst(result) == 5.0

test "welford known dataset"
  let xs = Cons(2, Cons(4, Cons(4, Cons(4, Cons(5, Cons(5, Cons(7, Cons(9, Nil))))))))
  let result = welford(xs)
  -- mean = 5.0, variance = 4.0
  assert fst(result) == 5.0
```

## Benchmarking

Each algorithm has a corresponding benchmark in `kea-bench`.
Benchmarks use the same compiled path as `kea run` — JIT via
Cranelift, same optimization passes, same runtime.

```rust
// In crates/kea-bench/benches/algorithms.rs
#[bench]
fn bench_merge_sort_10k(bencher: Bencher) {
    // compile once, run many
    let compiled = kea::compile_file("tests/algorithms/merge_sort.kea");
    bencher.iter(|| compiled.call("sort_random_10k"))
}
```

CI integration:
- Algorithm benchmarks run in the existing Stage B lane
- Thresholds in `benchmarks/baselines/algorithm-thresholds.csv`
- Non-blocking initially — baselines established, regressions
  flagged but not gating until numbers stabilize
- Variance summaries generated alongside microbenchmark variance

**Cross-language comparison (stretch goal):** For algorithms where
equivalent Rust implementations exist (sort, hash, search), include
the Rust version in `benchmarks/programs/` and report Kea/Rust
ratios. Not a performance target — a progress tracker. The ratio
should improve as optimization passes land.

## Phase Roadmap

### Now (0e): Welford's statistics

Only algorithm writable today with minimal extensions. Needs
`Int.to_float` and `Float.sqrt` intrinsics in stdlib (which are
already planned for `float.kea`). Pure, recursive, exercises
`@tailrec`, List pattern matching, and Float arithmetic.

**Ship this as the first gallery entry to establish the pattern.**

### 0f early: Hash functions, merge sort

When fixed-width integers and bitwise ops land in codegen:

- **FNV-1a hash** — exercises `wrapping_mul`, `bit_xor`, hex
  literals (`0xFF`), `UInt64`. The simplest non-trivial bitwise
  algorithm. ~15 lines.
- **Merge sort (functional)** — List-based, pure, recursive.
  Exercises List splitting, merging, `@tailrec`. No mutation
  needed. Good comparison point against Vector-based sorts later.

### 0f mid: Sorted data structures, search

When Vector and Unique land:

- **Binary search** — exercises Vector indexed access, Unique
  for in-place partitioning of search space. Classic algorithm
  that validates O(1) random access works.
- **Insertion sort** — in-place on Unique Vector. Simple mutation
  pattern. Good baseline for sort performance.
- **HAMT** — this IS stdlib Map/Set internals. Exercises popcount,
  bitwise masking, Ptr, @unsafe. If HAMT can't be written, 0f
  has a gap. (Also lives in `stdlib/map.kea` — the gallery
  version is the teaching implementation with verbose comments.)

### 0f late: Performance-intensive algorithms

When the full 0f toolkit is available (Unique + @unboxed +
fixed-width + Ptr):

- **Quicksort** — in-place on Unique Vector. Exercises partition,
  swap, Unique mutation. The benchmark everyone looks at.
- **Ring buffer** — fixed-capacity, power-of-2 masking with
  `bit_and` instead of modulo. Exercises Unique + fixed-width.
- **Priority queue** — binary heap on Unique Vector. Exercises
  indexed swap, sift-up/sift-down.
- **Matrix multiply** — dense, nested loops (via while + State
  or Unique indexed access). Exercises @unboxed for the matrix
  type, Float arithmetic.
- **Dot product** — Vector of Float, accumulation loop. Simple
  but reveals vectorization opportunities for future SIMD work.

### 0g: Pattern-heavy algorithms

When GADTs and advanced pattern matching land:

- **UTF-8 validation** — byte-level pattern matching on UInt8
  sequences. Exercises fixed-width integers, bitwise ops, and
  complex multi-branch patterns.
- **String find (KMP)** — failure function construction +
  matching. Exercises Vector mutation (failure table) and
  String.char_at.
- **LRU cache** — Map + doubly-linked list (or Vector-based).
  Exercises multiple data structure composition, Unique mutation.

## Code Quality Standards

Gallery code is exemplary. It's what people read to learn Kea.

- Every file has a module-level `--|` doc comment explaining
  the algorithm, its complexity, and when you'd use it.
- Every function has a `--|` doc comment.
- Variable names are descriptive, not single-letter (except
  conventional: `n` for count, `i` for index, `xs` for list).
- Prefer clarity over conciseness. Three clear lines over one
  clever line.
- Use `@tailrec` on every tail-recursive call.
- Use `while` where it reads more naturally than explicit
  recursion (especially in Unique/mutation-heavy code).
- Include edge case tests: empty input, single element, already
  sorted, reverse sorted, duplicates.
- Doc comment examples show realistic usage, not just the
  trivial case.

## Definition of Done

Per-phase, not all-at-once:

- **0e:** Welford's statistics implemented, tested, benchmarked,
  CI baseline established.
- **0f early:** FNV-1a and merge sort added.
- **0f mid:** Binary search, insertion sort, HAMT teaching version.
- **0f late:** Quicksort, ring buffer, priority queue, matrix
  multiply, dot product.
- **0g:** UTF-8 validation, string find, LRU cache.

Each entry ships with: implementation, test blocks, benchmark,
doc comments, CI threshold.
