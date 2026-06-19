# ADR-0024 — Indexed views: accelerating proved collections behind an equality bridge

- Status: Accepted
- Date: 2026-06-13

## Context

[ADR-0009](ADR-0009-proof-dependencies.md) models the kernel's collections
over `List`/association-lists, not `Finset` or `HashMap`: the CRDT join laws
(ADR-0004 theorems 1–2) prove cleanly by hand over lists, and the on-disk
canonical form is list-ordered (deterministic serialization and merge). A
performance cost is baked into that representation: `AMap.find` is a linear
assoc-list scan and `OrSet.Present` is a linear membership test, so any
lookup performed once per element across `N` elements is `O(N²)` — the
dominant command-path cost class
([ADR-0023](ADR-0023-efficiency-tiering-and-prevention.md)).

The obvious "fix" — make the map a `HashMap` — is wrong, and a future
contributor will propose it, so the answer is recorded here. The canonical
form needs a deterministic order for serialization and merge, which a
`HashMap` (no canonical equality) and a `Finset` (unordered) do not provide;
swapping the substrate would change the on-disk form and re-open the settled
convergence proofs (ADR-0004), and rewrite the elementary by-hand join laws
onto heavier machinery — all to buy what a per-query view buys with one bridge
lemma. This is not an aversion to Mathlib: ADR-0009 adopts it where it earns
its keep (the reachability/cardinality proofs) and the door stays open
case-by-case; a wholesale substrate swap simply is not such a case. The list
*is* the semantic, canonical, proved representation; it stays.

The pattern that resolves the tension is already established and load-bearing
— used by the ready queue, the cycle diagnostics, the CLI's per-row
projections, and the O(V+E) reachability/path engines `reachBFS`
(`Std.HashSet` visited) and `parentSweepH` (`Std.HashSet` visited +
`Std.HashMap` parent/depth) — and it deserves a recorded contract because every
new fast path now incurs it. The reach/path engines are an instance of §4 (the
recursion itself is indexed): they carry the visited-set↔list and HashMap↔AMap
equalities as engine-scale `*_eq` refinements (`reachBFS_eq_reachBFSL`,
`parentSweepH_eq`) rather than a per-row accessor lemma.

## Decision

### 1. The dual representation

A proved collection has two representations with distinct, non-overlapping
jobs:

- The **canonical representation** — the `List`/`AMap`/`OrSet` — is the
  semantic source of truth. The join laws, the fold, the serialization, and
  every spec theorem are stated over it (ADR-0004/0009). It is persisted; it
  is in the trust boundary; it is never fast.
- The **indexed view** — a hash structure built *once per query* from the
  canonical form — is an ephemeral acceleration index. It is never persisted,
  never merged, never part of the trust boundary; it is rebuilt each command
  and discarded. It exists only to make per-element reads `O(1)`-amortized.

This is the materialized-index pattern: the index must be *provably
consistent* with the base data, and that consistency is a proof obligation,
not a test (§3).

### 2. The substrate: three views, three bridges (`HashMapView`)

`Tl/Kernel/HashMapView.lean` provides the three index shapes the command
paths need, each with the lemma that makes it pointwise equal to the list
form:

- `hashAssoc : List (Id × V) → Std.HashMap Id V` — a hash copy of an assoc
  list (e.g. the rollup map's `toList`), bridged by `getElem?_hashAssoc_amap`
  (`(hashAssoc m.toList)[k]? = m.find k`).
- `hashSetOf : List Id → Std.HashSet Id` — a list's membership as a set,
  bridged by `contains_hashSetOf_present`
  (`(hashSetOf s.presentIssues).contains j = decide (s.hasIssue j)`).
- `bucketBy : List (Id × Id) → Std.HashMap Id (List Id)` — adjacency
  bucketed by key (the kids/blockers of each node), bridged by `getD_bucketBy`
  (`((bucketBy l)[k]?.getD []).reverse = (l.filter (·.1 == k)).map (·.2)`).

It is "indexed *views*," not "a hashed map": the set and adjacency shapes
carry the same weight as the map shape, and a fast path typically composes
all three (the ready filter reads the rollup through `hashAssoc`, presence
through `hashSetOf`, and blockers/kids through `bucketBy`, all hoisted once).

### 3. The bridge obligation

**A fast view ships with a proved bridge to its canonical form, or it is a
defect** — the efficiency analogue of the ADR-0004 rule that shell code ships
with its tests. The bridge is a pointwise-equality lemma (`fast probe = spec
accessor`), and it is what lets the fast path inherit the spec theorems with
*zero re-proof*: because the view is proved-equal to the canonical accessor, a
refinement lemma rewrites the fast form to the spec form (`isReadyFastH_eq` ⟶
`isReadyFast_eq`; `effStatusAll_find`; `readyFast_eq`), and `ready`
soundness/completeness/ordering, rollup correctness, and the cycle
diagnostics transfer untouched. The fast path is not *trusted* to match; it is
*proved* to match.

This **generalizes [ADR-0018](ADR-0018-hand-rolled-sha256.md)**, which
already requires that an optimized SHA-256 ship only with a proved
`fast = spec` bridge. ADR-0018 is that rule for one primitive; this ADR is the
rule for any accelerated view of any proved structure. They are the same
discipline at different scope.

### 4. The standing engineering rules

- **Build once, read many.** The view is hoisted at the top of a query (in
  `loadView`, or once inside a fast kernel function), never rebuilt per
  element. Building it inside the per-element loop reintroduces the cost it
  removes.
- **The view never escapes its query.** It is not stored on `State`, not
  serialized, not merged — it is a local of the command. Persisting it would
  put an unproved structure in the trust boundary (and `Std.HashMap` has no
  canonical equality to merge on). The one structure worth persisting, the
  folded state, is handled by the fold cache
  ([ADR-0022](ADR-0022-materialization-fold-cache.md)) with a content-keyed
  validity proof, not by persisting a view.
- **`getElem?_insert` is `==`, not `=`.** `Std.HashMap`'s lemmas condition on
  `BEq` (`if k == a`) where the `AMap` analogues use propositional `=`;
  bridge with `beq_iff_eq` (ids are `LawfulBEq`). This is the one recurring
  friction point, called out so it is not rediscovered each time.
- **When the recursion itself must be indexed, carry the equality.** A
  well-founded recursion whose termination measure is stated over the list
  (e.g. a bucketed-kids walk) carries the index↔list equality
  (`bucket = bucketBy pe`) as an ordinary hypothesis parameter and discharges
  the measure obligation through the bridge — the index accelerates the
  *runtime* probe while the *measure* stays on the canonical list. That is
  the technique for making an indexed walk near-linear without re-deriving its
  termination.

## Consequences

- **Every new fast view is a small proof, not just code.** The cost is one
  pointwise-equality lemma per view; the payoff is that all downstream spec
  theorems transfer free. A fast view without its bridge does not ship.
- **The bridge lemmas are the reusable surface.** `getElem?_hashAssoc_amap` /
  `contains_hashSetOf_present` / `getD_bucketBy` are written once in
  `HashMapView` and reused by every consumer; a new index shape adds one
  bridge there.
- **No substrate churn, no convergence re-proof.** Because the list stays
  canonical, ADR-0004's join/convergence theorems and ADR-0009's by-hand
  proofs are untouched; performance is bought entirely in the ephemeral
  layer.
- **It composes with the certificate-checker pattern.** Where even an indexed
  walk is too intricate to verify directly, the alternative is an unverified
  fast routine validated by a proved checker with a proved fallback (the SCC
  diagnostics, `SccFast`) — a different point on the same "fast path, proved
  correct" spectrum, chosen when a behavioral bridge is harder than a
  certificate check. A checker is *not* always available: it fits a spec that
  a local certificate pins down (reachability, SCC membership), but not one
  with a non-unique fixpoint — the rollup's cycle⇒`Open` rule (ADR-0003) is a
  fixpoint *selection* a local recurrence check cannot distinguish (an
  all-`Done` live cycle satisfies the recurrence yet is wrong), so the rollup
  takes the bridged-view road, not a checker.
- **Relationship to the corpus.** Realizes the "proved" tier of
  [ADR-0023](ADR-0023-efficiency-tiering-and-prevention.md); reconciles the
  cost of [ADR-0009](ADR-0009-proof-dependencies.md)'s list modeling without
  abandoning it; generalizes [ADR-0018](ADR-0018-hand-rolled-sha256.md)'s
  per-primitive bridge rule.

## Alternatives considered

- **Swap the substrate to `HashMap`/`Finset`.** Rejected — it changes the
  canonical on-disk ordering and re-opens settled convergence proofs (a
  `HashMap` has no canonical equality, a `Finset` no order, to serialize and
  merge against), and rewrites the by-hand join laws for no gain — to buy what
  a per-query view buys with one bridge lemma and no substrate change. Not an
  aversion to Mathlib (ADR-0009 adopts it where it helps); the swap just is not
  where it helps.
- **Persist the index.** Rejected — it would enter the trust boundary
  unproved and would have to be kept consistent across merges (`Std.HashMap`
  has no canonical equality); the fold cache (ADR-0022) already persists the
  one structure worth persisting, the folded state, with a content-keyed
  validity proof.
- **Trust the fast view, test it against the spec.** Rejected for kernel
  paths — the equality is provable, and a test only samples it; that is
  exactly the ADR-0004 line ("a test is not a substitute for a provable
  property"). Shell-only projections outside the kernel are tested per the
  shell tier; the kernel fast paths are bridged.
