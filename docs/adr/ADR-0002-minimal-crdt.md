# ADR-0002 — Minimal CRDT: OR-Set collections + LWW-register fields

- Status: Accepted
- Date: 2026-05-31

## Context

ADR-0001 makes state a fold over an unordered, possibly-duplicated multiset
of operations. For that fold to converge — same operations observed ⇒ same
state, regardless of order or duplication — the state must form a
join-semilattice and each operation must contribute monotonically (a join
with a delta). This is the CRDT obligation.

CRDTs are also where scope explodes: sequence CRDTs (RGA, Logoot) for
collaborative text, causal trees, etc. We want the *smallest* set of
constructions that correctly models a task tracker — and no more.

`dep remove` (a first-class command) is the forcing function: the set of
dependency edges must support removal that converges under concurrency. A
grow-only set cannot remove; a naive remove (delete the element) does not
converge against a concurrent add. This is precisely what an OR-Set
(observed-remove set) is for.

## Decision

Model state with two base CRDT constructions (OR-Set and LWW-register),
plus a third structure — the per-issue metadata map — that is not a new
construction but the LWW-register *lifted pointwise over a key map*, so it
reuses the same join law:

1. OR-Set for the two *collections*:
   - the set of issues, keyed by issue id;
   - the set of dependency edges, each keyed by `(from, to, kind)` — edges
     are typed (`blocks` / `parent` / `related`, ADR-0003); the kind is
     part of the element key and does not change the CRDT machinery. For the
     symmetric `related` kind the shell canonicalizes endpoints
     (lexicographically-least id as `from`) before forming the key, so
     `relate A B` and `relate B A` are the *same* element and `unrelate`
     tombstones it; `blocks`/`parent` stay directed.

   An OR-Set tags every add with a unique token — which is just the op's
   existing `(hlc, replica, nonce)` envelope identity (canonical string form
   pinned in ADR-0008), not a separately generated value (ADR-0007/0008) — and
   a remove tombstones only the tokens it has *observed*, carried in the remove
   op's `observed` field and recorded *at the removed element's own key*: the
   tombstone store is a per-element map mirroring the add-tag map, so a remove
   is element-scoped by construction and can never affect any other element's
   presence, whatever its `observed` payload contains (the concrete payload
   schema is in ADR-0008). Concurrent add/remove therefore resolves add-wins:
   an add the remove never saw survives. Proved in `Tl.Crdt.OrSet`: add-wins
   as `present_addWins` and re-add as `present_readd` (each with
   stamp-freshness as an explicit hypothesis, discharged by the carried
   nonce-uniqueness assumption — overview Trusted), and removal
   effectiveness — a remove that observed every add-tag makes the element
   absent — as `not_present_mergeTombstonesAt_of_observed_all`,
   unconditionally. This gives `tl create` / `tl dep add` / `tl dep remove`
   convergent add and remove.

2. LWW-register (last-writer-wins) for every *scalar field* of an
   issue — status, title, priority, assignee, description, notes, and the
   like. Each write carries the op's `(HLC-timestamp, replica-id, nonce)`;
   the register keeps the write that is greatest in the total order on
   that triple.

   `labels` (categorical tags) are an OR-Set per (1) and drive no theorem.

   Optional fields are `Option`, with an explicit clear. Every nullable
   scalar register (`assignee`, `slug`, `description`, `notes`, `deferUntil`,
   `closeResolution`) holds an `Option`. A clear (`undefer`, `reopen`
   dropping `closeResolution`, clearing `assignee`) is a *timestamped LWW write
   of `none`* — a tombstone carrying its own `(HLC, replica, nonce)` — not
   key-absence. So "cleared" (a real write of `none`) and "never written" (no
   register yet) are distinct, and a clear arbitrates against a concurrent set
   by the ordinary LWW order (a later set wins; an earlier set loses). On the
   wire a written `none` is an explicit JSON `null`, distinct from an absent key,
   and the round-trip preserves the distinction (ADR-0008). The `create` op's
   seeded defaults (`status = open` and `priority = 2`) are likewise ordinary LWW writes at the
   create op's triple — not privileged — so a pre-`create` `update` arbitrates
   against the seed by HLC like any other write.

   Closed-domain scalars use the tightest type. `status` is the closed enum;
   `priority` is `Fin 5` (0–4, 0 = highest) — illegal values are unrepresentable
   in state. The I/O shell maps an out-of-range or non-integer priority on
   parse/import to the nearest valid value with disclosure (clamp, not
   silent, never `now()`-style nondeterminism), keeping the fold total
   (ADR-0008/0005).

3. Metadata map (per-issue `key → value`) — a map of per-key
   LWW-registers, i.e. construction (2) lifted pointwise over a key map
   (its join is the register join applied key-wise; convergence follows from
   (2) by a one-line lift, no new theory). It carries opaque, uninterpreted
   text values that `tl` does not model as first-class fields: an
   `ext:<system>` reference back to a source/parallel tracker (`ext:jira`,
   `ext:gh`, … — preserved on import, ADR-0005), an opaque `due_at`,
   imported comments, and any future per-key machine state. An earlier draft
   cut this for lack of a use case; imports and cross-tracker integration are
   that use case. It is a side-channel: no theorem depends on it (a frame
   lemma isolates it, ADR-0004/0003), exactly like `labels`. Keys are
   free-form text; `tl` reserves a namespace (e.g. `ext:*`, `import:*`) for
   its own keys by convention — a local courtesy guard, never merge-enforced.
   Reserved side-channel prefixes are ASCII-lowercase and case-folded for
   matching: `type:*` / `waiting:*` for labels, `ext:*` / `import:*` for meta.
   Stored text is preserved for display; only prefix interpretation is
   normalized.

That is the entire CRDT surface. State is the product lattice of these
pieces; `apply op` is a join with the op's delta; convergence (ADR-0004,
theorems 1–2) follows from join being commutative, associative, and
idempotent.

Issue-local writes are keyed by id, independently of issue existence. Each
issue's field-register map, `labels` OR-Set, and metadata map live in
per-id-keyed structures that a write *creates-or-updates regardless of whether
that issue's `create` has been folded yet*. So an `update` / `labelAdd` /
`metaSet` folded before the issue's `create` is retained, not ignored —
exactly as a pre-`create` `depAdd` is (ADR-0003) — which is precisely what
keeps the fold permutation-insensitive: the result cannot depend on whether
`create` was seen before or after the field write (the writes are arbitrated by
LWW on their own HLCs, not by arrival order relative to `create`). An issue
materializes for *reads* — `show`/`list`, and driving `ready` — only once
its `create` is in the issue OR-Set; until then its accumulated registers sit
inert (and an orphan whose `create` never arrives stays inert forever, like an
orphan edge). `create` carries identity + optional initial scalars and never
"gates" later folds.

### Issues are resolved, not removed

OR-Set *removal* is used for edges (`dep remove` / `unrelate`) and labels
(`label remove`). An issue is never removed from the issue OR-Set — there
is no hard delete (vision). To retire an issue, `close --as cancelled` sets
a terminal status; the issue stays in the set. This sidesteps the concurrent
delete-vs-edit hazard (one replica deletes an issue while another adds a
blocker pointing at it → a *resurrected* issue with no fields). Note the
no-delete rule prevents an endpoint from *disappearing*, but it does not
make endpoint-existence a stepwise invariant — an order-insensitive fold can
still apply a `depAdd` before its `create` (or never see the `create` at
all), so a dangling edge is reachable regardless. Endpoint-existence is
therefore not an `apply` invariant; dangling edges are tolerated as inert at
read time (ADR-0004 theorem 3). What no-delete *does* buy is that a
reference, once its endpoint exists, never becomes dangling later.
Tombstoned/deleted issues on *import* (ADR-0005) are simply skipped, not
represented.

### Explicitly excluded

- No sequence / text CRDT. Descriptions and comments are whole-field
  LWW values. Concurrent edits to the same description resolve last-writer-
  wins (one wins wholesale); they do not merge character-by-character.
  Collaborative text editing is not a task-tracker need and would dominate
  the proof effort.
- No counters; no nested CRDT maps beyond the flat per-key-LWW metadata
  map — its values are opaque text, not recursively-merged structures
  (encode structure as a string and parse in the shell if ever needed).

### The tie-break is mandatory

LWW must order writes by `(HLC-timestamp, replica-id, nonce)`, a total
order. If two concurrent writes to the same field carried equal keys with no
tie-break, `merge` would not be a well-defined function and convergence
would fail. The mutation lock (ADR-0015) serializes same-working-copy writes, so
on the normal local path the HLC strictly advances and two writes never tie on
`(HLC, replica-id)`. A tie can still arise off that path — a duplicated
replica-id (a byte-copied working copy, ADR-0007), a lock-less or network
filesystem where serialization does not hold (ADR-0015), or import's
deterministic per-op nonce (single-writer, by construction) — so the per-op
nonce (freshly random per op, ADR-0007) is the final tie-break and
defense-in-depth: not a nicety, it is what keeps the key total and the register a
CRDT in every case. This obligation is discharged in the kernel proof (LWW join
is a function because the key order is total).

Implementation note (kernel realization). To make the register join an
*unconditional* total commutative/associative/idempotent function — provable
with no nonce-uniqueness side condition — the kernel orders register entries by
the 4-tuple `(HLC, replica-id, nonce, value)`: the value order is appended as a
final tie-break below the nonce. Under the nonce-uniqueness assumption this last
level never fires (no two distinct writes tie on the triple), so observable
behaviour is exactly the triple-keyed spec above and the genuine-last-writer
guarantee is unchanged; the value tie-break only ever decides the (assumed-away)
equal-triple case, where the spec makes no value guarantee anyway. So the carried
nonce-uniqueness assumption (overview Trusted / ADR-0007) governs *which write
wins*, never *whether the join is well-defined* — the kernel theorem
(`Tl.Crdt.Reg.merge_comm/assoc/idem`) holds outright.

## Consequences

- `dep remove` converges. Removing an edge tombstones the observed add —
  observing every add-tag genuinely deletes the edge
  (`OrSet.not_present_mergeTombstonesAt_of_observed_all`); a concurrent,
  unobserved add of the same edge survives (add-wins,
  `OrSet.present_addWins`).
- Add-wins is the decided bias, and it is conservative for blockers. On
  a concurrent "remove this blocker" + "add this blocker", add-wins keeps the
  edge, so the dependent stays blocked rather than becoming spuriously
  ready — erring toward not starting work prematurely, the safer default,
  and the natural OR-Set semantics (least proof burden). The accepted cost:
  a `dep remove` can be overridden by a concurrent stale add; this is
  surfaced rather than hidden — `dep cycles`/`show` expose the current edge
  set, and a re-`remove` settles it. (Should real use show add-wins is the
  wrong call, switching to remove-wins is a localized superseding change.)
- Deletes are tombstones, and tombstones accumulate. OR-Set removal
  retains metadata; this feeds the same unbounded log growth that only destructive
  GC would bound (deferred, ADR-0001/0008).
- Equal-timestamp ties resolve deterministically by the `(replica-id,
  nonce)` suffix of the order key (above), so two replicas never disagree on a
  field's value once they have seen the same writes.

## Alternatives considered

- Grow-only set for edges (no remove). Rejected: `dep remove` is in
  scope; a grow-only set cannot model it.
- Remove-by-value (2P-set / naive delete). Rejected: does not converge
  against concurrent re-add, and a removed element can never be re-added
  (2P-set), which breaks legitimate re-add of a dependency — the OR-Set's
  re-add is a theorem (`OrSet.present_readd`).
- Sequence CRDT for descriptions/comments. Rejected as scope creep
  (see vision non-goals).
- Vector-clock LWW instead of HLC. Deferred: HLC keeps timestamps
  scalar and human-comparable; vector clocks add per-replica metadata to
  every field write. Revisit only if causal anomalies in LWW prove painful.
