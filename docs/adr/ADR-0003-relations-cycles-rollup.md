# ADR-0003 — Relations, cycles, and rollup

- Status: Accepted
- Date: 2026-06-04

## Context

A dependency graph "should" be acyclic, an epic "should" be done only when its
children are, an issue's parent "should" be single. Under a single writer these
could be hard invariants — reject the offending write. `tl` cannot, because of
the CRDT (ADR-0001/0002): a merge must not reject anything, or convergence
breaks. Two replicas can each add a locally-legal edge that together form a
cycle (or a second parent); the illegal-looking state is runtime-reachable.

So this ADR fixes one rule for every cross-entity graph property, and the three
relation kinds, cycle diagnostics, epic rollup, and the readiness-deadlock
relation that follow from it.

## The unifying principle

> In a CRDT world, every cross-entity rule is derived (true by construction)
> or reported (flagged after the fact) — never enforced at write time.

A rule a merge could violate must be a total function of the materialized
state, which is exactly what makes it provable (ADR-0004). `blocked` is
derived, acyclicity and multi-parent are reported, epic-`done` is derived.

## Decision

### 1. Edges are typed

The dependency-edge OR-Set (ADR-0002) carries a kind. Three, and no more
without a superseding ADR:

| Kind | Direction | Drives | Acyclic? |
|---|---|---|---|
| `blocks` | directed (A blocks B) | `ready`, `why`, `unblocks`, `dep critical` | intended; reported |
| `parent` | directed (epic → child) | epic done-rollup, subtask views | intended; reported |
| `related` | symmetric | nothing (frame lemma) | n/a |

The kind is part of the OR-Set element key `(from, to, kind)`; for the symmetric
`related` kind the shell canonicalizes endpoints (lexicographically-least id
as `from`) before forming the key, so `relate A B` and `relate B A` are the same
element and `unrelate` removes it. (`related` links are navigation-only —
surfaced inline by `tl show` and in the `dependencies` array — and drive no
theorem.) `blocks`/`parent` stay directed.

CLI direction is pinned (and the inverse of the edge order): `tl dep add A B`
means *A is blocked by B* — A is the dependent, B the prerequisite — i.e. it adds
the edge `from=B, to=A`. This matches `tl create A --blocked-by B`
(subject-first, blocker-second). Because the command is named after `blocks` yet
the args read "blocked-by", the CLI always echoes the result in words ("A is
now blocked by B") and `--help` names the positionals `<id> <blocked-by>`. A
leaf may carry both a `parent` and `blocks` edges — the two graphs are
independent (a subtask can be blocked by a sibling), and `dep cycles` /
`ready`/`list` surface the cycle/blocked conditions across both.

### 2. Acyclicity is reported; `ready` is total on cyclic graphs

The edge OR-Set may contain a cycle after a merge — allowed and expected.
`ready` is defined and proved total over arbitrary (cyclic, dangling) graphs
(ADR-0004): an issue trapped in an unresolved cycle is simply not ready, and
`tl dep cycles` reports the cycle so an agent breaks it with `dep remove` (a
normal operation, not error recovery). A *local courtesy* check may warn when a
single replica's own `dep add` would obviously close a cycle, but it cannot be
the guarantee — merges bypass it. `dep cycles` reports per kind: a `blocks`
cycle (mutual blocking — nothing in it is ready) and a `parent` cycle (an epic
that is its own ancestor) are distinct, separately-reported conditions, plus the
mixed-kind `≺` readiness deadlocks (Theorem additions); `related` is symmetric,
so cycles there are meaningless.

### 3. Epic done-ness is derived (`effectiveStatus`), with a manual-cancel guard

An issue with `parent`-children is an epic, excluded from being directly
worked. Epic-ness is dynamic and merge-reachable — an issue becomes an epic
the moment a `parent` edge naming it as parent is folded in (including for an
`open`/`in_progress`/claimed issue, and via a *merge* from another replica);
this is intended (rollup, not a stored flag, is the source of truth), so the
issue silently leaves `ready` and is governed by rollup, and a local courtesy
guard / `doctor` may surface the transition, but no merge can prevent it. Its
done-ness is not a stored value you guard:

> `effectiveStatus(e) =`
> `  if stored status = cancelled then cancelled`
> `  else if every child is closed (done ∨ cancelled) then done`
> `  else open` (or, if a `parent` cycle traps it, not-done + reported)

For a non-epic, `effectiveStatus = status`. You cannot manually mark an epic
done (the CLI refuses `close <epic> --as done` as a local courtesy guard —
the `not-closeable` error, ADR-0008 — merges can't enforce it, like the cycle
check; `--as cancelled` is allowed); it
becomes done when its last child closes and reverts if a child
reopens — so "epic closed only if all tasks closed" holds by construction and
converges for free. A manual cancel takes precedence (an explicit "abandon
this epic" is never silently overridden by children happening to close).
Cancelling an epic does not cascade to its children (they become
reparentable). (A `--cascade` flag to also cancel open children was considered
and **cut** — it was the only read-snapshot-then-fan-out write in tl's single-op
model; loop `close` per child instead.)
`effectiveStatus` is total by well-founded recursion on a finite visited-set
over the `parent` graph (a cycle-trapped epic falls back to not-done, reported).

**The rollup recursion shape.** The fuel form (`effStatusAux` with
present-issue-count fuel) is the *spec*; the shipped read path is the memoized
shape `effectiveStatus (visiting, memo) i` (`Tl/Kernel/RollupFast.lean`), where
`visiting` is the *current recursion path* — it detects a parent cycle at the
exact node, and must not be a global visited set, which would mistake shared
DAG children for cycles — and `memo` caches completed statuses so each node is
evaluated once per query (an unmemoized descent would re-evaluate shared
descendants per parent on diamond-shaped parent DAGs). Semantics are identical
to the spec: manual `Cancelled` precedence, a cycle-trapped epic falls back
conservatively (never `Done`), dangling children stay inert. The proof
obligations are discharged via the characterization route: the recurrence is
proved *unconditionally* (`RollupSat.effectiveStatus_recurrence`, fuel
saturation by an ascending-chain pigeonhole — no acyclicity hypothesis), the
path cutoff is proved *exact* (a re-encountered node is on a live cycle, hence
`Open` — `effStatusAux_open_on_liveCycle`), and the refinement bridge
(`effStatusWith_eq`) makes the fast form pointwise equal to the spec, so the
acyclic-exactness and never-`Done` theorems transfer rather than being
re-proved. The once-per-query property (an id, once in `memo`, is never
recomputed) is itself a proved theorem (`rollupVisit_find_hit`) — the
recommended form of the performance claim; wall-clock of the compiled binary
stays tested, never proved. No unmemoized version ships (a reference function
is admissible proof scaffolding, not a shipped fallback).

### 4. Multi-parent is the third reported condition

`parent` is an add-wins OR-Set edge, so concurrent reparenting converges to
two surviving `parent` edges. Like a cycle, this is never rejected — it is
reported (a `multiParent` diagnostic). For display/rollup a canonical
parent is derived deterministically, ranking the candidate parents by the
lexicographic pair **(greatest live add-tag of the surviving `parent` edge,
parentId)** and taking the maximum. The tag is the greatest *live*
(untombstoned) add-tag of the edge — the surviving tag add-wins presence rests
on, never a tombstoned one (an edge kept present only by a low surviving tag
must not rank by a higher tag a `dep remove` already retired). The parentId is
the explicit tie-break, applied when two edges share a maximal live tag (a stamp
collision), so the pick is total and independent of enumeration order with no
distinct-stamps hypothesis; it mirrors the LWW equal-stamp *value* tie-break
(`tmax` on `Stamp × V`, ADR-0002). "Single parent" stays true for display while
the store stays honest. (An LWW *parent field* was rejected: it breaks the
all-relations-are-edges model and ADR-0002's two-construction minimality.)

This projection is proved in the kernel (`Tl/Kernel/CanonParent.lean`,
`State.canonicalParent`): the winner is the `from` of a present `parent` edge
into the child (edge presence only — the parent id may be dangling), its
`(liveTag, parentId)` pair dominates every candidate's, the selection is
enumeration-order-invariant, and it is `some` exactly when a present parent edge
into the child exists. The production accessor (`Tl.Cli.canonicalParentE`, over
hoisted `Edge`-keyed tag/tombstone hashes) is proved equal to the spec for a
present child (`canonicalParentE_eq`, the ADR-0024 §3 bridge).

The reparent surface is `tl parent set <child> <parent>` (a courtesy *replace*:
tombstone the child's other parent edges, add the target — so a single replica
stays single-parented, while a concurrent merge can still produce the
multi-parent that `multiParent` reports) and `tl parent remove <child> <parent>`
(detach). A direct self-parent is a local courtesy refusal; longer cycles stay
reported by `dep cycles`, never write-rejected (the CRDT rule).

**Why a dedicated verb pair, not `update --parent`.** The whole argument
reduces to one fact: *a parent is an edge, not a scalar* (this §4 — an LWW parent
*field* was rejected). `update` is the **scalar** verb (title/priority/
description/notes/slug); the edge verbs are `dep`/`relate`/`parent`. Everything
else follows:

- **`update` already excludes every edge flag.** It mirrors `create`'s *scalar*
  flags but not `--blocked-by`/`--blocks`/`--related` — those edits go through
  `dep`/`relate`. So `--parent` on `update` would be the lone edge flag of the
  four, *less* consistent, not more; true symmetry would mean duplicating the
  edge verbs into `update` and reviving the add/remove/replace ambiguity the
  split exists to avoid.
- **The flag spelling would hide a multiplicity flip.** `create --parent` is
  *additive* (repeatable — `--parent A --parent B` is a legitimate two-parent
  birth); the reparent *move* is *replace-all*. A symmetric `update --parent`
  either matches `create` (additive → it adds a second parent instead of moving,
  instant `multiParent`) or does the move (replace) — making one spelling mean
  *add* on `create` and *replace* on `update`. `parent set` names "replace"
  honestly, where `--parent` everywhere else means "add".
- **No clean detach.** A single value flag has no unambiguous "make this a root"
  (`--parent ""`? null-vs-absent, ADR-0002); `parent remove` does.

A parent *displays* as single (the canonical-by-stamp rule above), which is what
makes `update --parent` tempting — but that is a display convenience over a
multi-valued edge set, not a scalar field. (`dep --kind parent` was likewise
rejected: `dep` is the *dependency* surface, and a parent edge is not a
dependency.)

### 5. Dangling endpoints are read-time inert

An order-insensitive fold can apply a `depAdd` before its endpoint's `create`
(or the `create` may never arrive), so a dangling edge is reachable. Therefore
endpoint-existence is not an `Invariant` (ADR-0004 theorem 3) for any kind: a
`blocks`/`parent` edge to a nonexistent id is inert (no live blocker / no
child — treated as already-discharged, like `related` soft-refs), so dangling
edges never make an issue spuriously not-ready. The difference is only in
*reporting*: `related` dangling refs are silent; a dangling `blocks`/`parent` is
surfaced as a diagnostic (it usually means a missing `create`), and may be a
local courtesy check at write time. (Issues are never removed — ADR-0002 — so a
reference, once its endpoint exists, never becomes dangling later.)

## Theorem additions (ADR-0004)

- `ready` discharge via `effectiveStatus`: a blocker counts as discharged
  when `closed (effectiveStatus s b)` (not stored status) — so an epic blocker
  discharges its dependents exactly when it has rolled up. `ready` walks only
  `blocks` edges and excludes epics from being ready themselves.
- `effectiveStatus` totality + epic-rollup correctness, guarded by manual
  cancel (above), total on the `parent` graph including cycles.
- Readiness-deadlock (`≺`) relation + diagnostic. An issue waits on its
  `blocks`-blockers that are not `closed (effectiveStatus)`, and an epic
  additionally waits on its own not-closed children; an unclosed epic blocker
  therefore makes its dependents wait transitively on the epic's open
  descendants, recursing through nested epics by the same `parent`-graph
  walk `effectiveStatus` uses. Formally `j ≺ i` iff `j` is a `blocks`-blocker
  of `i` with `¬ closed (effectiveStatus j)`, or `i` is an epic and `j` is
  a child of `i` with `¬ closed (effectiveStatus j)`. Honest deadlock-freedom
  (ADR-0004 theorem 5) is stated over `≺`; `tl dep cycles` reports per-kind
  structural cycles and `≺`-cycles (pure-`blocks` or mixed blocks+parent,
  possibly threading several epic levels), so a stuck live set — including one
  created only by nested epics — is never undiagnosed. Each is one canonical
  witness per cyclic SCC.
- Frame lemma: adding/removing a `related` edge, any `metaSet` write, any
  `labelAdd`/`labelRemove` (ADR-0002), and the per-op `actor` provenance field
  (ADR-0008/0013) change neither `ready` nor `effectiveStatus` — the structural
  guard isolating the side-channels (and provenance) from the verified core.
- Invariant covers only valid-status; no edge kind's endpoint-existence and
  no acyclicity are part of it.

## JSON read projection (edges as fields, output only)

Relationships are edges in the model but consumers read them as issue fields, so
the CLI/Format shell projects the edge set into `--json` as a read-only view
(no theorem changes): a single `dependencies` array of
`{ "type": "blocks"|"parent"|"related", "from": <id>, "to": <id> }` — one entry
per edge. Direction is fixed: for `blocks`, `from` blocks `to`; for `parent`,
`from` is the parent. A convenience `parent` scalar emits the canonical parent
(§4). Writes never go through this array (`dep add/remove`, `relate/unrelate`,
`parent set/remove` mutate edges); there is deliberately no `update --dependencies`.

The issue object itself is pinned here too (the `--json` `data` is an
additive-only forever-contract, ADR-0008), so every consumer reads one
canonical shape:

- Scalar LWW fields by their field-table names: `id`, `title`, `status`
  (the stored enum), `priority`, `assignee`, `slug`, `description`, `notes`,
  `deferUntil`, `closeResolution`.
- Provenance projections `createdAt`/`updatedAt`/`closedAt`/`claimedAt`
  (fold-time, ADR-0008); the `labels` array; the `meta` object; the
  `dependencies` array (above) with the convenience `parent` scalar.
- Derived projections (camelCase, reflecting effective state at the query's
  `now`): `effectiveStatus` (`open`/`in_progress`/`done`/`cancelled` — distinct
  from stored `status`), and the booleans `isEpic`, `ready`, `blocked`,
  `deferred`.
- Provenance/trust (derived, drives no theorem — frame-lemma-safe): a
  `provenance` object `{ "source": "native"|"imported", "createdBy": <actor>|null,
  "replica": <replica-id> }`, so a consumer can lower trust on imported or
  foreign-authored content. `createdBy` projects the `create` op's envelope
  `actor` (ADR-0008/0013); since every op carries its `actor`, per-field /
  `updatedBy` authorship is a clean future additive projection.
  All free-form content (`title`/`description`/`notes`/`labels`/`assignee`/`slug`)
  is untrusted data; the render-time sanitization/fencing of these fields — and
  the schema-level statement that content is untrusted — are defined at the
  consumption boundary (ADR-0011 / ADR-0014), not in the kernel.
- Claim outcome (on `show` and the `claim` verb):
  `claim: { "outcome": ..., "currentAssignee": <assignee>|null }` — an
  `ok: true` data outcome, *not* an error. The `claim` verb's own echo is
  binary: `"won"` iff BOTH winning register entries are the claim's exact
  stamped writes — `status = (stamp, in_progress)` and `assignee =
  (stamp, actor)`, the kernel `ClaimWon` — else `"superseded"` (including
  the partial survival where only the assignee write held). `show`'s block
  carries the same two values plus a third, `"ended"`: this replica's own
  claim ran its course by the claimant's own successor write with no lost race
  hidden underneath. Three conditions (ADR-0013): (a) *no contest* — no `claim`
  op the claimant did not author is stamped above the surfaced own claim
  (scanned in the op log, since a register winner cannot carry contest history —
  the claimant's own later close or reopen buries the losing claim); (b) the
  winning *status* write is the claimant's own; (c) the *assignee* winner is the
  claimant's value or a clear the claimant authored (a reopen). So an
  interleaved foreign claim buried under the claimant's own later close **or
  reopen** stays `"superseded"`, and another actor's close on a shared replica
  does too. Authorship is the envelope `actor` only — an actor-less op (or an
  absent origin under compaction) cannot be attributed, so it resolves toward
  `"superseded"`; the replica id is **not** an authorship proxy (the
  shared-replica footgun), which means even an actor-less *own* close reads
  `"superseded"` (the honest "can't prove it was you" reading). `show`'s
  `"won"` also covers a later claim by the same actor that currently holds both
  registers at one stamp (a re-claim after reopen, from any replica). The human `show` renders the same verdict as a
  `claim: <outcome>` provenance entry (surface parity). The `"ended"` growth
  and re-mapping shipped as `schemaVersion: 2` (ADR-0008 §ledger).
  `currentAssignee` reports the converged winning
  `assignee` value, whoever that is — on a partial survival it can name you
  even though the outcome reads `superseded`. An existing target that is not
  in `ready s now` is refused before writing as the `not-claimable` error
  (ADR-0008), with structured reasons: closed, already `in_progress` / claimed,
  epic, deferred-until, or the direct unclosed blocker set (`tl why` gives the
  transitive set — ADR-0020). A nonexistent id
  stays `not-found`. See ADR-0013.

`ready`/`list`/`stats`/`why` reuse these same names — defining the shape
once here keeps every `--json` consumer contract additive-only.

## Consequences

- Typed edges ripple into every dep util — each is parameterized by the
  kinds it traverses; the frame lemma makes "treat all edges alike" a proof
  obligation, not a latent bug.
- Decomposition is ergonomic and correct — `create … --parent E` + auto
  rollup, no manual closure bookkeeping.
- More to report, nothing more to enforce — cycles (two kinds + `≺`),
  multi-parent, and rollup are all derived/reported, so convergence is untouched.
- The honest liveness story distinguishes "blocked by a tool bug" (never)
  from "blocked by a cycle the merge introduced — here it is" (actionable).

## Alternatives considered

- Enforce a DAG / single parent at write time. Impossible under merge; kept
  only as a local courtesy check.
- Auto-break cycles on merge (drop an edge). Rejected: silently dropping a
  user-affirmed dependency loses information; report + explicit `dep remove`
  keeps control. Could be an opt-in later.
- Refuse to materialize a cyclic/multi-parent state. Rejected: turns a
  reachable, convergent state into a runtime failure — the escape-hatch
  anti-pattern this ADR exists to avoid.
- An untyped single `blocks` relation (the original). Rejected: hierarchy
  with a closure constraint and free-form "related" links both need a kind.
