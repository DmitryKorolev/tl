# ADR-0004 — The verified kernel and the TCB boundary

- Status: Accepted
- Date: 2026-05-31

## Context

"Verified" has to mean something precise, or it means nothing. This ADR
fixes what `tl` proves, what it tests, and where the line between them
falls — the trusted computing base (TCB).

The governing discipline: prove inside the kernel, test outside it. A
test is not an acceptable substitute for a property that can be stated and
proved; and a property that is structurally unprovable in-kernel (I/O,
clocks, git, the external file format) is covered by tests, never asserted.

## Decision

### The kernel (proved, Lean)

A pure core with no I/O:

- `State` — the product CRDT: an OR-Set of issues (each a record of
  LWW-registers, an OR-Set of `labels`, and a per-key-LWW metadata map,
  ADR-0002), an OR-Set of dependency edges. Illegal *intra-issue* states
  (e.g. an unreachable status) are made unrepresentable by the types. The
  metadata map is a side-channel: no theorem depends on it (the frame lemma,
  ADR-0003). Each issue's registers/labels/meta are keyed by id
  independently of OR-Set membership, so a field/label/meta write folded
  before that issue's `create` is *retained and inert* (it materializes when
  `create` lands) — the same order-insensitive treatment dangling edges get
  (ADR-0002/0003), and what makes theorem 2 hold for issue-local writes, not
  just edges.
- `Op` — the inductive type of operations: one constructor per distinct
  state-delta, not per CLI verb. Seven deltas — `create`, `setFields` (an
  LWW write to one or more scalar fields), `metaSet` (a per-key-LWW metadata
  write, ADR-0002), `edgeAdd`, `edgeRemove`, `labelAdd`, `labelRemove`. The
  readable CLI verbs (`claim`, `close`, `reopen`, `defer`, `dep add`,
  `relate`, …) are decoupled wire op-kinds that the tested shell maps
  onto these deltas (the verb→delta table and the on-disk `op` enum live in
  ADR-0008); e.g. `close --as done` ⇒ a `setFields` setting
  `status` + `closeResolution` (the `closedAt` provenance is then the fold-time
  projection of this op's HLC, not a stored field — ADR-0008). Every mutation is one of the seven
  deltas; there is exactly one mutation path, so a new verb adds no kernel
  constructor and no new theorem.
- `apply : State → Op → State` — total, defined as a join with the op's
  delta. The single reducer.
- `fold : List Op → State` — materialization, `List.foldl apply ∅`.
- `ready : State → Now → List IssueId` — total, cycle-aware (`Now` injected,
  ADR-0010).
- `cycles : State → List Cycle` — the cycle diagnostic.

#### Theorems

Lattice layer (convergence):

1. Join-semilattice. `merge` (= the state join underlying `apply`) is
   commutative, associative, and idempotent over the whole product — issues
   OR-Set, edges OR-Set, per-issue `labels` OR-Set, scalar LWW-registers,
   and the per-key-LWW metadata map (whose join is the register join
   lifted pointwise over keys, ADR-0002 — proved by reusing the register
   lemma, no new theory). The LWW-register join is a well-defined function
   because `(HLC, replicaId, nonce)` is a *total* order (ADR-0002/0007 — the
   nonce is required: same-replica concurrent writes can tie on
   `(HLC, replicaId)`).
2. Order/duplicate insensitivity of the fold. For any permutation `π`
   and any duplication, `fold (π ops) = fold ops` and
   `fold (ops ++ ops) = fold ops`. Corollary — strong eventual
   convergence: replicas that have observed the same op multiset
   materialize identical state. (This is the only correctness obligation
   git-as-transport imposes; ADR-0001.)

Tracker layer (over materialized state):

3. Invariant preservation. `Invariant s → Invariant (apply s op)`,
   proved once over `apply`, inherited by every command. `Invariant` =
   *every status is a valid enum value* (plus intra-issue type-level
   invariants) — `status` is a total field defaulting to `open` at
   materialization (`create` seeds it unless an initial status is carried), so
   it is never absent and theorem 4's `status i = open` is well-defined on
   every materialized issue. (`priority`, a non-`Option` `Fin 5`, is likewise
   total — seeded to `2` at `create` unless an initial value is carried — so the
   ready-ordering key #1 is well-defined on every materialized issue; its validity
   is a type-level intra-issue invariant.) That is deliberately *all* it asserts. Three things are
   not part of `Invariant`, each for the same reason — an order-insensitive
   fold (theorem 2) cannot maintain them stepwise, and a CRDT merge cannot
   reject a write:
   - Acyclicity (ADR-0003) — reported, not enforced.
   - Reference-validity of `blocks`/`parent` endpoints. Under an
     order-insensitive fold a `depAdd` may be applied before its endpoint's
     `create` (IDs are free-form op data, ADR-0007), so a dangling edge is
     a reachable state — and for an orphan `depAdd` whose `create` never
     arrives, a *final* state the CRDT cannot prevent. So, exactly like
     acyclicity, endpoint-existence is dropped from `Invariant` and
     tolerated at read time: a `blocks`/`parent` edge to a nonexistent
     id is inert (contributes no live blocker / no child — treated as
     already-discharged, the same tolerant reading `related` soft-refs get,
     ADR-0003). Endpoints *should* exist — a local courtesy check at write
     time, and dangling `blocks`/`parent` are surfaced as a diagnostic since
     they usually mean a missing `create` — but the kernel guarantees only
     that a dangling edge is inert, never that one cannot exist.
   - Status transition legality (e.g. `open → in_progress → done`) —
     under LWW the status field holds the latest *value*, not its path, so
     transition rules are a local courtesy guard, not a merge-enforced
     property. The kernel guarantees only that the value is a valid status.
4. `ready` soundness + completeness, total on cyclic/dangling graphs.
   `ready : State → Now → List Id` (the `Now` parameter is injected, ADR-0010;
   it is the canonical signature, matching codebase-map.md and overview.md):
   `i ∈ ready s now ↔ (status i = open ∧ ¬isEpic s i ∧ (deferUntil i).all (· ≤ now) ∧
   ∀ b ∈ blockers s i, closed (effectiveStatus s b))`,
   where `closed = done ∨ cancelled` and `blockers` walks only `blocks`
   edges (ADR-0003). A blocker is discharged by its `effectiveStatus`, not
   its stored status — so an epic blocker whose children have all closed
   (effectively `done`, though its stored status is never set to `done`,
   ADR-0003) correctly discharges its dependents, and a stored-`done` issue
   later given open children (now effectively `open`) correctly re-blocks
   them; for a non-epic `effectiveStatus s b = status b`, so this reduces to
   the stored status in the common case. The recursion is one-directional and
   layered — `ready` calls `effectiveStatus`, which recurses only over the
   `parent` graph (ADR-0003) and never back into `ready`/`blockers` — so
   totality composes from the epic-rollup totality theorem (ADR-0003). No
   issue with an unclosed blocker (effectiveStatus not in
   `{done, cancelled}` — note this includes `in_progress`, not just `open`)
   is ever returned; every open, non-deferred, fully-unblocked leaf is. A
   `blocks` edge to a nonexistent id is inert (no live blocker; theorem
   3), so dangling edges never make an issue spuriously not-ready. Holds with
   no acyclicity precondition and total on dangling graphs.

   The relation-typing theorems (epic-rollup correctness *and its totality*,
   the frame lemma — which covers `related` edges, the metadata map,
   `labels`, and the per-op `actor` provenance field (ADR-0008/0013): none changes `ready` or `effectiveStatus` — and the read-time
   treatment of dangling endpoints) are specified in ADR-0003 and join
   this list. (The per-kind cycle diagnostic is theorem 6 above.)

   Ready ordering is a total order. The `ready` ranking
   (priority, then critical-path weight, then `createdAt`, then `id`;
   vision) terminates in the unique `id`, so it is a *total* order on issues.
   The second key, critical-path weight, is pinned as a total kernel
   function: `weight s i = |reach⁺_blocks s i|`, the cardinality of the set of
   distinct issues reachable from `i` over `blocks` edges (transitive,
   excluding `i`). Scope is pinned: it counts every *existing* reachable
   issue regardless of status (closed nodes included — a structural metric,
   like `dep critical`), and a `blocks` edge to a nonexistent id contributes
   no node (dangling = inert, theorem 3); so `weight` is a pure function of the
   graph shape, independent of `now` and of closure. It is computed by the same well-founded recursion on a
   finite visited-set as cycle detection, so it is total on cyclic graphs
   (a `blocks` cycle yields a finite reachable set, not nontermination) — a
   real totality obligation, discharged, not assumed. Hence the `ready` order is
   unique and deterministic across replicas given the same state and the same
   `now` — a stable, reproducible ranked queue an agent or orchestrator chooses
   from. There is no atomic "take the top" primitive: items are claimed explicitly
   (`claim`), and cross-replica claim exclusion is LWW + the superseded signal
   (ADR-0013/vision), not a distributed lock, so two replicas may claim the same
   item (the loser is told, not silently lost).
5. Liveness (honest deadlock-freedom). The earlier biconditional ("empty
   `ready` ⟺ every open issue is cycle-blocked") is *false* — `ready` excludes
   an issue for four reasons (not-open, epic, deferred, unclosed-blocker), and
   an open task blocked by an `in_progress` task gives empty `ready` with no
   cycle and no defer. The correct statement is one-directional and scoped to
   the live working set:
   > Define the readiness-dependency relation `≺` on open, non-deferred
   > issues. `i` *waits on* `j` (written `j ≺ i`) when `j` is something `i`
   > still needs closed:
   > - `j` is a `blocks`-blocker of `i` with `¬ closed (effectiveStatus s j)`
   >   (a non-epic blocker counts by its own status; an epic blocker counts
   >   until it has rolled up), or
   > - `i` is itself an epic and `j` is a child of `i` with
   >   `¬ closed (effectiveStatus s j)` (rollup-wait: an epic discharges only as
   >   its children close).
   > An unclosed epic re-enters via the second clause, so `≺` descends through
   > epic-of-epic by the same `parent`-graph recursion `effectiveStatus`
   > uses — the wait is transitive over nested epics, not a single level. An
   > open, non-epic, non-deferred issue with no `≺`-predecessor is ready.
   > Contrapositive: among the live set (open issues that all carry an unclosed
   > blocker) if none is ready then `≺` over it — together with the epic nodes
   > it reaches — contains a cycle; an acyclic `≺` always exposes a
   > `≺`-minimal, fully-dischargeable open leaf. `≺` is total (finite
   > visited-set over `blocks` + `parent`, the same machinery as
   > `effectiveStatus` and cycle detection).

   The `blocks` subgraph alone is not the right relation: discharge is by
   `closed (effectiveStatus s b)` (theorem 4), so an epic blocker's discharge
   runs over the `parent` graph, and a stall can be a mixed blocks+parent
   loop (`E blocks A`, `A blocks C`, `E parent C`) that is acyclic in *each*
   kind separately yet a genuine deadlock. The interesting content (ADR-0003)
   survives over `≺`: a `≺`-cycle is the only *tool-pathological* stuck
   state. Every other empty-`ready`-with-open-work case has an actionable
   definitional reason — work the `in_progress` blocker, wait out the defer —
   not a deadlock.
6. Cycle-diagnostic correctness. Per kind `k ∈ {blocks, parent}`,
   `cycles s k` returns one canonical simple-cycle witness for each
   strongly-connected component of the kind-`k` edge graph that contains a
   cycle (canonical = the lexicographically-least simple cycle, by id-sequence,
   through the SCC's least-`id` node — so it is a deterministic *pure function
   of the state*, identical on replicas with the same state; dedup is by the
   SCC partition). Correctness: `cycles s k` lists a witness for exactly
   the cyclic SCCs of kind `k` — every cyclic SCC reported, no acyclic part —
   the decidable, polynomial, total statement. (Enumerating *all* simple cycles
   is exponential and unnecessary: one witness per SCC is what an agent needs
   to break it with `dep remove`; `dep path` walks a full cycle on demand.)
   `cycles s` additionally reports `≺`-cycles — the *readiness deadlocks*
   of theorem 5, which may be pure-`blocks` or mixed blocks+parent-rollup —
   reported as one canonical witness per cyclic SCC of `≺` (same least-id-rooted
   rule, a pure function of state), so `dep cycles` never says "no cycles"
   while the live set is stuck. A mixed
   `≺`-cycle is broken by removing one of its `blocks` edges or by
   closing/reparenting the epic's trapped child.
7. Close-monotonicity. A single `close` (one `setFields` to a terminal
   status) only unblocks:
   `ready (apply s (close i)) now ⊇ ready s now \ {i}`. Forward progress is
   structural. (`--cascade` epic-cancel, ADR-0003, is *several* such ops — each
   individually monotonic, so the whole command is too; the theorem is about
   the single op, not the cascade command.) Through the rollup channel:
   closing `i` can change an ancestor epic `E`'s `effectiveStatus`, so the proof
   carries a lemma — *closing is monotone on every ancestor's `effectiveStatus`*:
   a child going closed moves `E` only toward `done` (a not-all-closed epic stays
   open; the last child flips it to done) and never toward open, and a
   manually-cancelled epic is unaffected. So no third party is newly blocked by
   `i`'s close, and `ready` stays monotone non-decreasing modulo `{i}` —
   including dangling / cyclic-parent cases (an unresolved parent cycle keeps `E`
   not-done either way, so closing a child cannot reduce readiness).

Robustness additions (reuse existing machinery — 8 strengthens the lattice layer;
9–10 the tracker layer):

8. CvRDT inflation (monotonicity) + idempotent re-delivery. Every op only
   moves state *up* the lattice — `s ≤ apply s o` for all `s, o` (the delta is a
   join and `s ≤ s ⊔ d`) — so the fold is monotone under op-set inclusion:
   `ops ⊆ ops' → fold ops ≤ fold ops'`. A replica that has observed a superset is
   never below one that has not; a merge never loses acknowledged information.
   With order/duplicate-insensitivity (theorem 2) this is the full state-CvRDT
   pair (inflation + SEC). Op-granular corollary of join idempotence:
   `apply (apply s o) o = apply s o`, so at-least-once delivery — the segment
   union and the worktree local-leg re-delivering a line (ADR-0001/0016) — is safe
   per op, not only under full duplication.
9. `ready` time-monotonicity. `now` enters `ready` only through the defer
   conjunct `(deferUntil i).all (· ≤ now)`, which is monotone in `now`, so for a
   fixed state `now ≤ now' → ready s now ⊆ ready s now'`. The passage of time alone
   never removes a workable item — a deferred task only ever resurfaces. The
   defer-dual of close-monotonicity (theorem 7).
10. `why` / `unblocks` correctness. Both are total kernel diagnostics; agents act
    on them, so they are proved, not shell-tested (AGENTS.md tier 1).

    `why s i` is computed by the same finite-visited-set `blocks`-reachability
    recursion as the critical-path weight (theorem 4) and cycle detection
    (theorem 6), hence total on cyclic/dangling graphs. Soundness + completeness:
    `j ∈ why s i ↔ j` is `blocks`-reachable from `i` through *live* (present,
    unclosed) blockers — the transitive *unclosed* blockers of `i`.

    `unblocks s i` is the issues that closing `i` newly makes ready. It is **defined
    as the exact set difference** `ready (withClosed s i) \ ready s`, where
    `withClosed s i` is `s` with `i`'s materialized status forced to `Cancelled` —
    the *full* effect of closing `i`, including the epic-rollup ripple. Soundness
    *and* completeness are then **unconditional** and definitional
    (`mem_unblocks_iff`): `j ∈ unblocks s i ↔ j ∈ ready (withClosed s i) ∧ j ∉ ready s`.
    `ready_withClosed_eq_cancel` grounds the projection in the real op — the
    force-closed state agrees with `apply s (cancelOp i st)` on `ready` whenever that
    close actually takes effect (its stamp wins LWW), so `withClosed` is exactly
    "what if `i` were closed", not an approximation.

    *Why a local definition would be incomplete (the epic-ripple gap).* An earlier
    formulation listed `j` only when every blocker of `j` was *either `i` itself or
    already discharged* — a cheap, local check. But "unblocking" is **non-local**:
    closing `i` can discharge a *different* blocker of `j` by rolling up an epic
    ancestor of `i`. Concretely — epic `E` has children `i` (open) and `k` (done),
    and `E` blocks `j`; since `i` is open, `effectiveStatus E = Open`, so `j` is
    blocked and not ready. Closing `i` makes all of `E`'s children closed, so `E`
    rolls up to `Done`, discharging `E` and readying `j`. Yet `i` is **not** a direct
    blocker of `j` (`E` is), so the local check would never list `j` — it under-reports.
    This is unavoidable structurally: a CRDT merge can always produce an epic that
    blocks something and has `i` as a child (cross-entity rules are *reported, never
    enforced* — ADR-0002), so the gap cannot be *prevented*; the fix is to *define*
    `unblocks` as the exact ready-diff, which re-derives readiness in the closed world
    and so captures the ripple by construction.

This is the whole spec: the convergence theorems (1–2, with the inflation
strengthening 8) and the tracker theorems (3–7 and 9–10), plus the rollup / frame
theorems of ADR-0003 — the per-kind cycle diagnostic is theorem 6 above, not a
separate ADR-0003 theorem. Theorems 8–10 add no new state and no new CRDT theory;
they reuse the existing lattice and reachability machinery.

### The shell (tested, not proved) — the TCB

Everything that touches the world is outside the kernel and outside the
proof:

- beads import (ADR-0005) — reads `.beads/*.jsonl`, maps to seed `Op`s.
  Covered by a differential test against real `.beads` fixtures.
- op-log serialization — parse/render of the JSONL log. Covered by a
  round-trip property test (`parse ∘ render = id` on owned fields;
  unknown fields preserved).
- logical-clock + replica-id generation — HLC stamping at write time.
  Clocks are *data* fed into ops; the kernel reads no clock (ADR-0001).
- git invocation — fetch/merge/push. Pure byte transport; correctness
  is theorem 2, not git's behavior.
- CLI — argument parsing, the verb→delta mapping (each readable wire
  op-kind → one of the seven kernel deltas, ADR-0008), output formatting,
  exit codes.
- A kernel property test is an *outside-TCB* concern, despite touching
  kernel functions: it samples whether the *compiled/extracted* binary still
  agrees with the proved spec (does the toolchain preserve the theorems?).
  It is a regression net on the executable, phrased like the round-trip and
  differential checks above — explicitly not part of the kernel's
  correctness obligation and never a substitute for the theorems (AGENTS.md
  tier 1; the "a test is not a substitute for a provable property" rule).

The TCB is therefore: the Lean kernel (and its checker), the file/JSONL
I/O, git, and the system clock. Nothing else is trusted.

## Consequences

- One reducer, one preservation proof. Every command is one of the seven
  `Op` deltas (a new verb is a shell-level mapping, not a new constructor);
  all deltas inherit theorem 3 by construction, so adding a command cannot
  silently break the invariant. (The "route every mutation through one
  proved-total function" pattern.)
- `ready` is honest under concurrency. Because totality is proved
  without a DAG assumption, the runtime-reachable cyclic case is covered,
  not excused.
- The proof effort is bounded and small — on the order of a few hundred
  lines: a few lattice theorems plus a handful of tracker theorems (those here
  and ADR-0003's rollup / frame additions), no sequence-CRDT machinery
  (ADR-0002).
- Convergence is independent of git. We do not trust git to merge
  "correctly" beyond concatenating bytes; theorem 2 makes any byte order
  fold to the same state.

## Alternatives considered

- Prove the I/O too (verified parser, verified git). Rejected as
  disproportionate: serialization correctness is well-covered by round-trip
  tests, and verifying git is out of any reasonable scope. The boundary is
  drawn where proof stops paying for itself.
- Skip the convergence proof, test merges instead. Rejected: merge
  convergence is the central correctness claim of a CRDT and is exactly the
  kind of property that is provable and that tests sample rather than
  guarantee. It belongs inside the kernel.
