# ADR-0023 — Algorithmic efficiency: the proved/tested/assumed tiering and the prevention net

- Status: Accepted
- Date: 2026-06-13

## Context

[ADR-0004](ADR-0004-verified-kernel-tcb-boundary.md) sets a three-way coverage
mandate for *correctness*: prove inside the kernel, test the I/O shell, carry
the rest as an explicit assumption. Efficiency has no equivalent. AGENTS.md
("Maintain algorithmic efficiency as a principle") states the intent in prose —
work proportional to input, no accidental quadratics — but gives it no coverage
tier and no enforcement. The result: superlinear command paths
(`O(N²)`/`O(N³)`) missed the vision's "comfortable at thousands of ops" scale
target and shipped unnoticed. The cause was one class, not scattered bugs,
behind two gaps:

1. **No structural cost guarantee.** The kernel proves what its functions
   *compute* (ADR-0004) but says nothing about how much *work* they do.
   `effectiveStatus` recomputing `presentIssues` per call, `ready` multiplying
   an insertion sort by uncached weight calls, cycle diagnostics running a
   closure per node — each correct, each superlinear, none flagged.
2. **A vacuous regression net.** The perf suite asserted wall-clock under a
   fixed floor, which cannot distinguish `O(N)` from `O(N²)` at small N, so a
   quadratic passed green. There was no end-to-end binary-latency test, and
   in-process profiles mispredicted the binary's wall-clock — the dominant
   warm-read cost was the cache decode, not the in-process view work, and
   interpreted `lean --run` numbers run several-fold off the compiled binary.
   A net that measures the wrong path certifies "fast" while the class
   regresses.

This ADR records efficiency as a first-class property with the same tiering
discipline ADR-0004 gives correctness, plus the prevention mechanism the
prose principle lacked. The *mechanism* that makes the proved tier achievable
— the indexed-view substrate and its bridge obligation — is
[ADR-0024](ADR-0024-indexed-views-bridge.md); this ADR is the discipline and
cites it.

## Decision

### 1. Efficiency is tiered like correctness (the ADR-0004 analogue)

Every performance-relevant property has a home in one of three tiers; "it's
just performance" never licenses leaving a hot path uncovered, exactly as
"it's outside the TCB" never licenses untested shell code (ADR-0004).

- **Proved — structural cost invariants, where the kernel allows.** The
  kernel proves the *structural* facts that pin the complexity class — not a
  literal operation count (the project has no cost monad or instrumented
  semantics and deliberately does not add one). The provable shape is "each
  node is evaluated once per query" (`rollupVisit_find_hit` — the memo-hit
  short-circuit returns a completed node without re-descending), "the
  reachability closure saturates at its first fixed point rather than burning
  `|present|` iterations" (`reachFix` / `iterateN_of_fixed`), "the batched
  fold equals the iterated fold" (`foldFast` / `joinFast`). These are
  invariants about the *algorithm's shape*. The efficient form *is* the
  production code and the theorems are proved about it — directly where that is
  cheapest, or through a refinement bridge to a reference where the bridge is
  the easier proof (AGENTS.md Code rules: "whichever proves cheapest"). A
  reference, when kept, is proof-only scaffolding, never a shipped slow path; a
  slow implementation the fast form supersedes is retired, not carried as a
  runtime fallback. What is *not* proved is the wall-clock: that stays in the
  tested tier.

- **Tested — op-counts pin the class, end-to-end latency pins the cost.** Two
  distinct obligations, because each catches what the other cannot:
  - **Operation-count assertions** over synthetic logs of growing size,
    asserting the *growth ratio* (e.g. "×4 ops ⇒ ≤ ~×4 work," not "< Xms").
    A class regression is a ratio that jumps; an op-count is deterministic
    where a clock is not.
  - **End-to-end latency of the compiled binary.** Op-counts pin the
    in-process class but not the real cost — the decode-dominates finding
    shows an in-process profile can mispredict the binary by a large factor,
    and interpreted measurement is unreliable for absolutes. So the net must
    time `./.lake/build/bin/tl` on a scaled repo, not an in-process harness.

- **Assumed — constant factors and the platform.** Cache locality, allocator
  behaviour, the constant in front of the `O(N)`, the wall-clock of a
  syscall. These are neither proved nor pinned by a ratio test; they are the
  efficiency analogue of ADR-0004's tier-3 carried assumptions, and an
  accepted constant-factor compromise is recorded explicitly (an ADR or a
  tracked task), never silently.

### 2. The regression net's required shape

A perf test that asserts only a wall-clock floor is not coverage; it is the
vacuous net this ADR retires.

- **Ratio, not threshold.** Assertions are on the growth ratio across at
  least two sizes (e.g. 1000 / 2000 / 4000), so the *class* is pinned
  independent of the machine.
- **No floor-masking.** A row whose smaller size sits under the timing floor
  proves nothing; either both sizes clear the floor, or the row is an
  op-count row, not a wall-clock row.
- **End-to-end is mandatory.** At least one row times the compiled binary on
  a scaled repo, because the in-process class is not the binary's cost (the
  decode-dominates lesson).
- **Coupled to the fix.** De-floor-masking a row and the fix that makes it
  pass land together; you cannot honestly un-mask a still-quadratic path
  without going red, so the net's honesty is *coupled* to the optimizations —
  the prevention net is a keystone, closed as the paths it measures are
  fixed, not before.

### 3. Command paths read the indexed view; raw per-element accessors are a smell, gated by lint

The dominant cost class is "an `O(N)` accessor in a per-element loop" —
`AMap.find` (a linear assoc-list scan) or `OrSet.Present` (a linear
membership test) called once per issue across `N` issues, i.e. `O(N²)`. The
standing rule: a command path consumes the once-built indexed view
([ADR-0024](ADR-0024-indexed-views-bridge.md)), never re-derives a lookup per
element.

This is **discipline backed by a lint, not a by-construction guarantee** —
and the distinction is deliberate, because an ADR whose thesis is "an
unenforced prose principle let quadratics ship" must not itself assert an
unenforced invariant. Today the raw accessors are public and callable from a
command path; the per-row render path still calls `issueData`/`effStatusWith`
once per rendered row (a tracked, open violation). The enforcement mechanism
is therefore a CI lint, in the spirit of the existing "no task-ID leakage"
gate (AGENTS.md): flag `AMap.find` / `presentElements` / `OrSet.Present`
reached from a per-element loop on a command path (`Tl/Cli`, and the
fast-path kernel modules). The stronger, type-level form — command paths
receive only a `View` exposing hashed accessors, with the raw `State`
accessors out of scope — is the eventual target; until the lint and that
discipline exist, "by construction" overstates it, and the rule lives as
convention plus the open per-row task.

### 4. "Memoized" must mean indexed-memoized

A memo whose container costs `O(N)` per operation does not remove the
quadratic; it relocates it. The trap is concrete: a "memoized" rollup that
caches completed statuses in an `AMap` is still `O(N²)`, because every
`AMap.insert`/`find` is a linear scan. A memo on a command path is backed by a
hashed container (ADR-0024) or it does not count as memoized. This is a
corollary of §3, called out because "I memoized it" can read as done while the
container is still linear.

## Consequences

- **Untested-for-cost is a defect, like untested shell code.** A new hot path
  ships with its op-count ratio row in the same change, exactly as shell code
  ships with its branch tests (ADR-0004). A lint may guard the accessor
  class, but a lint does not excuse a missing per-change ratio row.
- **The proved tier is honest about its reach.** "Proved efficient" means the
  structural invariant is proved (visited-once, saturation,
  fold-equivalence); the binary's wall-clock is tested, never claimed proved.
  No cost calculus is introduced, so the kernel's proof burden does not
  balloon.
- **Slow forms are scaffolding, not fallbacks.** Prefer proving the fast form
  and retiring the slow one; the equivalence-bridge route is fine where it is
  the cheaper proof, but the reference it bridges to stays proof-only. This is
  about slow *algorithm* twins, not the canonical *data* representation — the
  `List`/`AMap` is the persisted source of truth (read once to build an index,
  ADR-0024), not a slow algorithm to delete. Residual: a few fast forms still
  fall back to the slow spec at runtime for absent/dangling ids
  (`effStatusWith`'s `getD (effectiveStatus …)` and the cycle-diagnostic
  analogues) — reachable only off the hot path, tracked for retirement by
  proving the fast form total over those inputs, not permanent.
- **The net is coupled, not parallel.** The end-to-end suite is a keystone
  closed as the paths converge; it cannot be completed ahead of the
  optimizations it measures without re-masking.
- **Relationship to the corpus.** This is the efficiency analogue of
  ADR-0004 (correctness tiering); it reconciles with
  [ADR-0009](ADR-0009-proof-dependencies.md) (the List-modeled substrate that
  *causes* the `O(N)`-accessor class — see ADR-0024 for why the fix is a
  bridged view, not a substrate swap); it generalizes the per-primitive
  bridge rule of [ADR-0018](ADR-0018-hand-rolled-sha256.md) (an optimized
  SHA-256 ships only with a proved `fast = spec` bridge) into a standing
  discipline; and [ADR-0022](ADR-0022-materialization-fold-cache.md)'s fold
  cache is one instance of incremental materialization under this regime. It
  supersedes nothing; it makes AGENTS.md's efficiency bullet enforceable and
  gives it a recorded rationale.

## Alternatives considered

- **Leave efficiency as a prose principle.** Rejected — the unenforced status
  quo that let the class ship; a principle without a tier or a lint is not
  coverage.
- **Introduce a cost monad / instrumented semantics to *prove* runtime
  bounds.** Rejected as disproportionate for a kernel this size (ADR-0009's
  small-footprint stance): the structural invariants pin the class and the
  ratio tests pin the cost, at a fraction of the proof burden a literal cost
  calculus would impose. Revisit only if a path's class cannot be captured by
  a structural invariant.
- **Wall-clock-threshold regression tests.** Rejected — the vacuous net that
  masked the regression: a threshold is machine-dependent and floor-masks
  small N, where the growth *ratio* is the invariant.
