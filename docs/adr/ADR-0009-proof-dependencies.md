# ADR-0009 — Proof dependencies: batteries over Mathlib

- Status: Accepted
- Date: 2026-05-31

## Context

`tl` is a Lean 4 project; we must choose the proof/library baseline. Mathlib
is powerful (Finset, the order/lattice typeclass hierarchy, extensive
automation) but heavy: it dominates cold build time and enlarges the
dependency surface and CI minutes. The `tl` verified kernel is *small*
(ADR-0004: a few convergence theorems + a handful of tracker theorems over
List-shaped state), and the project prioritizes fast iteration and a small
footprint.

## Decision

Default to Lean core + `batteries` (std4); do not depend on Mathlib unless
a specific proof genuinely needs it.

Implications of staying off Mathlib:

- Model collections without `Finset`. State (the issue/edge OR-Sets, the
  per-issue field maps) is modeled over `List` with explicit
  nodup/dedup reasoning, or `batteries` structures with functional specs —
  not `Finset` (a Mathlib type).
- Prove the CRDT laws directly. Commutativity / associativity /
  idempotence of the join (ADR-0004 theorems 1–2) are proved by hand rather
  than by instantiating Mathlib's `SemilatticeSup`/order hierarchy. These
  proofs are elementary; the typeclass convenience is not worth the
  dependency.
- Tactics: follow the inherited proof discipline (recorded in
  `AGENTS.md`) — explicit `calc`, `cases`/`match`, named lemmas,
  `simp only [...]` with explicit lists; avoid `omega`, `decide`,
  `aesop`, and bare `simp` as closers. Core + `batteries` tactics suffice
  for a kernel this size.

Escape hatch: adding Mathlib is a deliberate one-line `lakefile.toml`
change, taken *only* if a proof genuinely needs it (e.g. nontrivial algebra)
and recorded (a superseding note here). It is not banned — it is not the
default.

### Superseding note (Mathlib adopted, scoped) — 2026

Mathlib is now a pinned dependency (`mathlib4 @ v4.30.0`, matching the
toolchain), taken under the escape hatch above for a genuine need: the
remaining tracker theorems — honest liveness (ADR-0004 thm 5), cycle-diagnostic
correctness (thm 6), `why`/`unblocks` correctness (thm 10), and epic-rollup
fuel-adequacy (ADR-0003) — all rest on finite-graph **reachability and
cardinality** arguments (transitive-closure saturation, "shortest path ≤
node-count" / pigeonhole, well-foundedness of the readiness relation on a finite
set). These are exactly the `Finset` / `Relation.ReflTransGen` cardinality facts
Mathlib makes routine and that are disproportionately painful to rebuild by hand
over `List` with `batteries` alone.

Scope discipline preserved: the dependency is confined to the proof files that
need it. The whole CRDT layer (`Tl/Crdt/*`) and the kernel's *definitions* and
already-proved convergence/frame/close theorems (`State`/`Op`/`Apply`/`Rollup`/
`Ready`/`Cycles`/`Theorems`/`Frame`/`CloseMono`) remain Mathlib-free and continue
to build fast off `batteries`; only the reachability-correctness proof modules
`import Mathlib`. The tactic discipline (explicit `calc`/`cases`/named lemmas;
avoid `omega`/`decide`/`aesop`/bare-`simp` closers) still applies — Mathlib is
used for its *lemmas*, not to license heavy automation.

## Toolchain and test harness (pinned)

- Pinned toolchain. A committed `lean-toolchain` pins an exact
  `leanprover/lean4` release; `lakefile.toml` requires `batteries` (std4) at a
  pinned git rev (an immutable commit, not a branch/tag); `lake-manifest.json`
  is checked in. CI installs that exact toolchain via `elan` on every target.
  Bumping any pin is a deliberate, reviewed change (recorded by a note here).
  This is what makes "a green `lake build` proves the theorems" reproducible, and
  it is the floor for the reproducible-build goal (ADR-0006). *(The concrete
  version/rev strings are set when the project is scaffolded; the policy is fixed
  here.)*
- Test harness, off Mathlib. Tests live under `Tests/` on a
  dependency-free, in-repo harness — a thin assertion runner plus
  deterministic, seeded `List`-based generators for property tests — rather
  than a generator framework `tl` would have to pin and track. Seeds are fixed
  constants, so property runs are reproducible; the same harness backs the three
  tiers (round-trip, differential import, and the compiled-kernel-vs-spec
  property cross-check; AGENTS.md / ADR-0004). A heavier framework, if ever
  wanted, is pinned by rev like `batteries` and must stay off Mathlib.

## Consequences

- Fast cold builds and small CI — the main motivation; keeps the
  edit-build-prove loop tight, which matters for a small tool.
- Some proofs are more manual (no `Finset` API, no lattice typeclasses).
  Acceptable at this kernel size, and the well-founded-recursion obligations
  (`effectiveStatus`/cycle detection, ADR-0003) are core-Lean concerns
  anyway.
- Reversible. If proofs balloon or the manual collection reasoning
  becomes a tax, adopting Mathlib is cheap and isolated.

## Alternatives considered

- Mathlib from the start. Rejected as the default: disproportionate
  build/CI weight for a small kernel; reconsider if the proof burden grows.
- Lean core only, no `batteries`. Rejected: `batteries` provides
  essential `List`/`Array`/`Option` lemmas and structures cheaply, with none
  of Mathlib's weight.
