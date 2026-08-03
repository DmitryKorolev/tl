# Overview — what tl proves, tests, and trusts

> Implementation underway. This is the claim table: what the verified core
> proves, what tests cover, and what is trusted at the boundary. The kernel
> (`Tl/Crdt/`, `Tl/Kernel/`) is fully defined and total, and the stated theorem
> set is proved; the **Proof status** subsection below records each theorem
> (and the closed-residual history — the one remaining discharge is carried as
> a tier-3 assumption, never downgraded to a test, per AGENTS.md
> Definition-of-Done #5).
> The Stage-1 tested I/O shell is built, each piece with its tests in
> `Tests/`: `Tl/Format` (Crockford, the record envelope, the record↔Op codec
> over the full v1 verb enum, the ISO-8601 instant codec, ids), `Tl/Hash`
> (SHA-256), `Tl/Store` (the ADR-0019 native shim + discovery, segments,
> materialize, the locked write path, clock/replica recovery), `Tl/Clock`,
> and `Tl/Cli` (the stage-1 verbs with `--json`, dispatch, init incl. its IO
> tests). `Tl/Sync` is built — the `refs/tl/log` plumbing, the complete-line
> union merge, the local-first worktree leg (`tl sync`), the read-time refresh,
> the remote fetch/union/push leg, and **auto-sync** (ADR-0021: the best-effort
> local-leg publish after every write, plus the symmetric pre-transact absorb
> *before* a write's guards — ADR-0016 write-path freshness) are done and tested.
> `Tl/Import` is built and tested — the ADR-0005 one-shot deterministic bulk
> importer (JSONL records → a seed op-log under a deterministic single-writer
> import replica; ids and nonces derive from the source via SHA-256, fallback
> timestamps from a fixed base plus a per-record ordinal, causality-clamped —
> so re-import is byte-stable; dangling edge endpoints are skipped and
> disclosed), covered by the differential import test.

The discipline: prove inside the TCB, test outside it
([ADR-0004](adr/ADR-0004-verified-kernel-tcb-boundary.md)). A claim is
either a Lean theorem about the kernel, a test about the I/O shell, or a
carried assumption (the Trusted section below) — never a vibe.

## Proved (kernel theorems)

| Claim | Statement (shape) | ADR |
|---|---|---|
| CRDT convergence | the state join (issues/edges/labels OR-Sets, scalar LWW-registers, and the per-key-LWW `meta` map) is commutative, associative, idempotent ⇒ replicas with the same op-set materialize identical state | 0002, 0004 |
| Fold order/dup-insensitivity | `fold (π ops) = fold ops`; `fold (ops ++ ops) = fold ops` (the git-concat requirement) | 0001, 0004 |
| `ready` soundness + completeness | `i ∈ ready s now ↔ open ∧ ¬epic ∧ (deferUntil).all (·≤now) ∧ every blocker's effectiveStatus ∈ {done,cancelled}` (epic blockers discharge by rollup, not stored status) | 0004, 0003, 0010 |
| Totality on cyclic/dangling graphs | `ready` / `apply` / `effectiveStatus` / cycle detection total with no acyclicity precondition; dangling edges inert | 0003, 0004 |
| Honest liveness (deadlock-freedom) | one-directional: an open non-epic non-deferred issue with all blockers closed ⇒ `ready` non-empty; a stuck live working set ⇒ a cycle in the readiness-dependency relation `≺` (blocks edges + epic-rollup-on-open-children; pure or mixed-kind) — the only tool-pathological stall | 0003, 0004 |
| Cycle diagnostic correctness | `cycles s kind` = one **node-set** witness per cyclic SCC of that kind (the SCC's members, sorted — *not* a single simple-cycle path), proved exactly one witness per SCC (`sccWitnesses_same_witness_iff`); `cycles s` also reports readiness-deadlock `≺`-cycles (mixed blocks+parent) so a stuck live set is never undiagnosed (exactly the cyclic SCCs + `≺`-cycles; polynomial, total) | 0003, 0004 |
| Epic rollup | unless manually cancelled, `effectiveStatus e = done ↔ all children closed`; cancel takes precedence; total incl. parent-cycles — a cycle-trapped epic falls back *conservatively* to not-done (`Open`, never its stored status / merge-injected `Done`; `effStatusAux_epic_zero_ne_done`), matching ADR-0003 | 0003 |
| Invariant preservation | one `apply` preserves valid-status; inherited by every `Op` (endpoint-existence & acyclicity deliberately not invariants — tolerated at read time) | 0004 |
| Close-monotonicity | a `close` op only unblocks: `ready (close s i) ⊇ ready s \ {i}` | 0004 |
| Ready ordering is total | rank ends in the unique `id` ⇒ the `ready` order is unique and deterministic given the same state and `now` (a stable ranked queue to choose from; no atomic take-the-top); the critical-path-weight key is a total function on cyclic graphs | 0004 |
| frame lemma | `relate`/`unrelate`, any `meta` write, any `labels` write, and the per-op `actor` provenance field change neither `ready` nor rollup (the side-channels stay out of the verified core) | 0003, 0008, 0013 |
| CvRDT inflation / monotonicity | `s ≤ apply s o` (each op only moves up the lattice) ⇒ `ops ⊆ ops' → fold ops ≤ fold ops'` (a merge never loses information); with fold-dup-insensitivity, the full state-CvRDT pair. Op-granular: `apply (apply s o) o = apply s o` (at-least-once delivery safe) | 0002, 0004 |
| `ready` time-monotonicity | `now ≤ now' → ready s now ⊆ ready s now'` — time alone never un-readies an item (the defer-dual of close-monotonicity) | 0010, 0004 |
| `why` / `unblocks` correctness | `why s i` = exactly the transitive *unclosed* `blocks`-blockers of `i` (reach⁺ machinery, total on cyclic/dangling); `unblocks s i` = exactly the set closing `i` newly readies, *defined* as the ready-set diff `ready (withClosed s i) \ ready s` so soundness+completeness are unconditional (captures the epic-rollup ripple) | 0003, 0004 |
| claim outcome | `ClaimWon d st actor ↔ status = (st, in_progress) ∧ assignee = (st, actor)` (both registers, stamp- and value-exact; decidable `claimWonB` is what the CLI branches on): a fresh-stamped claim establishes it, the register join arbitrates it exactly across any merge (an iff, so merges never blur won into superseded or back; supersession is stable), and a partial win (assignee kept, status lost) is distinguishable and never `won` | 0013, 0004 |

### Proof status (current)

What is **proved** in `Tl/Kernel/Theorems.lean` (and the layer files). The
`#print axioms`-clean claim below (only `propext` / `Classical.choice` /
`Quot.sound`) is not a remembered spot-check: the Lean executable
`lake exe tlverify` re-derives it from compiled environments on every CI run
and fails otherwise ([ADR-0026](adr/ADR-0026-continuous-integration.md)). It
checks production (`Tl` + `Main`), tests (including a hostile initializer
fixture), its own verifier modules, and executable Lean tooling. For each scope
it compares the current filesystem inventory exactly with Lean's actual
imported-module graph, classifies additional first-party imports by their
resolved project-build `.olean` provenance, examines declaration ownership and transitive axioms,
and independently replays each stored safe, total declaration plus its complete
cross-package dependency cone from an empty environment through Lean's kernel.
Audited module initializers are never executed. Lean deliberately excludes
unsafe/partial executable definitions from replay; those cannot justify a safe theorem.
Replay is the semantic backstop for unchecked insertion or a disabled kernel
check: a declaration that was accepted only by bypassing the compiler's normal
check is rejected when replayed. Because inventory is read at runtime, a
stale local `.lake` artifacts cannot hide a newly unimported source file. A source in
a top-level location no scope claims is refused outright. Directory and root
source entries carry their owning scope, and those same typed entries derive
both the top-level claims and that scope's expected-module set, so naming a new
location as claimed cannot hide it from inspection. `lakefile.lean` remains a
distinct fixed configuration exemption because Lake elaborates it before the
gate exists.

The verifier is outside the TCB, and its tier is split. Its *verdict logic* —
the pure functions turning already-collected evidence into a pass/fail
decision — is **proved** in `Verify/Proofs.lean`: `analyze` and the run-wide
assembly above it are characterised as if-and-only-ifs against a `GateClean`
structure that enumerates every condition a scope can be reported for, and the
ADR-0009 import audit is characterised both for silence and for emitting one
finding per rejected edge. Stored-body axiom propagation is proved in both
directions — the axioms filed under a declaration are exactly those reachable
from it along stored-body edges — which matters because that function
reimplements Lean's `collectAxioms` rather than trusting summaries the audited
compilation produced, so its failure mode is a green run with an axiom
unreported. It refuses rather than answering when its bound is exhausted, since
a truncated map would satisfy soundness while missing the axiom that mattered.
The supervision status rule, the import-allowance case split, and the replay
dependency step carry one-directional implications only. The rest of the
*collection* — declaration selection, the replay closure walk, filesystem
inventory, process supervision — stays **tested**, and the propagation
theorems are relative to the constants they are handed: exact over that map,
silent on whether it is the right one.
Neither half is one of the product's proved claims, so neither appears in the
table above and neither gets a landmark; that split and its reasoning are
recorded in [ADR-0026](adr/ADR-0026-continuous-integration.md) and
[the codebase map](codebase-map.md).
Required evidence is typed rather than accumulated in optional clean
arrays: import audit, replay, expected landmarks, six named scope reports,
inventory findings, typed source-scope ownership, and unclaimed sources must all
reach the verdict.
`Tests/VerifyTests.lean` covers each report branch's message and remedy, the
cleanliness of its own base fixture, source inventory
and symlink refusal, the pinned direct-dependency policy and its violation
findings, the scope-claim check, stored-body axiom propagation, an ill-typed
theorem that kernel replay must reject, and the supervision decision driven
against real worker processes. `Tests/VerifyLoadedTests.lean`, on the ordinary
toolchain CI legs, loads the real environment without initializers and covers
module/declaration selection, artifact provenance, stored import rows, a
cross-package replay closure, transitive-axiom observation wiring, and injected
import/replay findings. Empty test groups fail globally; the binary-only
git-floor job produces one skip row, decided by the group itself from the
observed absence of a Lean sysroot rather than from a caller-supplied flag. A
scope
that imports modules but selects no declarations, replays nothing, or reads no
import edges is itself a finding:
the semantic arms are silent when empty, so the gate must not read that as
success. Every live verifier run also loads a hostile exit initializer as
an end-to-end no-execution/provenance/ownership canary. CI
invokes a minimal Lean supervisor, which requires the audited worker's fixed
end-of-run marker as well as status zero. This catches unmarked accidental early
exits; it does not authenticate the worker against code deliberately forging its
own public marker. The worker root, launcher, and workflow are therefore an
explicit review and branch-protection bootstrap, as for every CI gate.

The verifier also pins a landmark theorem for every row of the table above
(except totality, which is definitional and has no named theorem) and for the
named proved anchors of the tested tier below — the `*Fast`/reference bridges,
skew convergence, `ascending_of_sorted`, and the CLI read-facet algebra
(`applyFacets_eq_filter` and the membership, sublist, facet-predicate and
ready-non-widening laws that follow from it). `Tl.Verify.landmarkTheorems` is
the authority on the exact set; this sentence names the groups. That guards the
*names*: a claim here cannot be silently renamed away or downgraded to a
non-theorem. It does not read what a theorem states, nor check the definitions
it quantifies over. The list is itself pinned by `Tests/VerifyTests.lean`, so
retiring a claim takes a deliberate edit in both places rather than one
deletion.

- **Thm 1 — join-semilattice.** `State.merge_comm/assoc/idem` over the whole
  product, composed from the per-layer laws (`AMap`, `FinSet`, `Reg`/`MetaMap`,
  `OrSet`, `IssueData`). `AMap.ext` is axiom-free.
- **Thm 2 — order/duplicate insensitivity.** `fold_eq_of_mem_iff` (same op-set ⇒
  identical state — strong eventual convergence), `fold_perm`, `fold_append_self`.
- **Thm 3 — invariant preservation.** `invariant_apply` (valid status is
  type-level; the enum/`Fin 5` make illegal values unrepresentable).
- **Thm 4 — `ready` soundness + completeness.** `mem_ready_iff`: membership in the
  ranked queue is exactly the readiness predicate (`rankSort_perm` shows the sort
  filters nothing). *Totality* is discharged by `ready`/`effectiveStatus`/`weight`/
  `cycles` being total Lean definitions (fuel / bounded `iterateN`), no `sorry`.
- **Thm 8 — CvRDT inflation + idempotent re-delivery.** `le_apply`,
  `fold_le_of_subset`, and `apply_idem`.
- **Thm 6 — cycle-diagnostic correctness** (`Tl/Kernel/Reach.lean`).
  `onCycle_kindSucc_iff` / `onCycle_precSucc_iff`: a node is flagged on a (kind-`k`
  structural, or `≺` readiness-deadlock) cycle iff a successor reaches it back.
  Both ride on `mem_reachClosure_iff` — that `reachClosure` computes the exact
  transitive closure (soundness `batteries`-only; completeness is the Mathlib
  finite-graph saturation argument, ADR-0009 note). `kindSucc` now filters dangling
  targets (ADR-0003 §5), keeping reachability present-bounded.
- **Thm 10 — `why` correctness** (`Tl/Kernel/Reach.lean`). `mem_why_iff`: `j ∈ why
  s i` iff `j` is reachable from a direct live blocker through live blockers —
  exactly the transitive *unclosed* blockers. Total on cyclic/dangling.
- **Thm 7 — close-monotonicity** (`Tl/Kernel/CloseMono.lean`, cancel case).
  `close_cancel_monotone`: closing `i` never removes another ready item. The crux
  `effStatusAux_mono` (a status moving toward closed moves any ancestor epic's
  rollup only toward done) is proved by induction on the rollup fuel; the
  `--as done` case is the same argument restricted to non-epics.
- **Thm 5 — honest liveness** (`Tl/Kernel/Reach.lean`, both directions). `liveness`:
  an open, non-epic, non-deferred, materialized issue with no `≺`-predecessor is
  ready. `deadlock_exists`: a *stuck* nonempty live set (every member has a
  `≺`-successor inside it) contains a `≺`-cycle, so `precCycles` always diagnoses
  it (pigeonhole on iterates of a chosen-successor function).
- **Thm 9 — `ready` time-monotonicity.** `ready_time_mono` (via `deferOk_mono`).
- **Epic-rollup correctness** (`Tl/Kernel/RollupSpec.lean`, `Tl/Kernel/RollupAcyclic.lean`).
  `effectiveStatus` meets its ADR-0003 spec: manual-cancel precedence and non-epic =
  stored status unconditionally; and, on an acyclic parent graph (`ParentAcyclic`), an
  epic that is not manually cancelled is `Done` iff every present child is effectively
  closed (`effectiveStatus_epic`), via fuel-irrelevance above the descendant count
  (`effStatusAux_stable`, strong induction on the descendant-closure cardinality).
- **The rollup recurrence, unconditional** (`Tl/Kernel/RollupSat.lean`; ADR-0003
  rollup recursion shape). With no acyclicity hypothesis, `effectiveStatus i` = cancel ▸
  `Cancelled` | childless ▸ stored | `Done` iff every present child effectively
  closed (`effectiveStatus_recurrence`): closed-ness at fuel `f` is an ascending
  Bool chain (`closedAt_le_succ`), a present-frozen fuel freezes all later fuels
  (`closedAt_freeze_present`, propagated to every later fuel by
  `closedAt_frozen_upto`), and a chain on `M+1` present issues freezes by fuel
  `M` (`exists_closedSet_freeze`, cardinality pigeonhole). Companion: live-cycle
  conservatism (`RollupSpec.effStatusAux_open_on_liveCycle`) — every member of a
  cycle of non-cancelled epics is `Open` at every fuel.
- **The fast-rollup refinement bridge** (`Tl/Kernel/RollupFast.lean`; ADR-0003
  rollup recursion shape). The shipped memoized walk (`effStatusAll` — visiting-path cycle
  detection + memo over a hoisted parent-edge view, `kidsOfEdges_parentEdges`)
  is pointwise equal to the spec: `rollupVisit_sound`/`rollupKids_sound` (mutual
  induction on the walk's own well-founded structure; the path cutoff is exact by
  live-cycle conservatism, the epic step folds against the recurrence), hence
  `effStatusAll_find`, and total agreement `effStatusWith_eq` / `effClosedWith_eq`
  / `isReadyWith_eq` — every spec theorem transfers to the shipped path with no
  re-proof. Once-per-pass: `rollupVisit_find_hit` (a memoized node is never
  recomputed). Decode-side canonicality for the walk's collaborators:
  `AssocList.sorted_of_ascending`/`ascending_of_sorted` (`Tl/Crdt/Map.lean`).
- **The fast-queue refinement bridge** (`Tl/Kernel/ReadyFast.lean`). The shipped
  `ready`/`unblocks`/`why` forms — hoisted present/edge views, rollups through the
  batched map, one cached `RankKey` per candidate, and the O(V+E) frontier closure
  `reachBFS` (proved list-equal to the spec `reachClosure`, `reachBFS_eq`, on the
  nodup adjacency/singleton seeds) —
  are pointwise equal to the spec (`readyFast_eq`/`unblocksFast_eq`/`whyFast_eq`,
  composed from `weightFast_eq`, `isReadyFast_eq`, `keyLe_keyOf_eq`, and the
  sort-map commutation `rankSortK_map`), so ready soundness/completeness/ordering
  and `unblocks`/`why` exactness transfer to the shipped path with no re-proof.
- **The fast-diagnostics refinement bridge** (`Tl/Kernel/CyclesFast.lean`,
  `Tl/Kernel/SccFast.lean`, `Tl/Kernel/Tarjan.lean`). The shipped
  `cycles`/`precCycles`/`hasCycle`/`hasDeadlock` run a checked-certificate SCC
  path: an *unverified* fuel-total Tarjan proposes the partition, the *proved*
  checker `sccCertOk` validates it (coverage, condensation-order monotonicity,
  per-component two-way BFS connectivity — the only reachability input is
  `bfsGo`'s, itself proved, `bfsGo_sound`), and an accepted certificate answers
  `onCycle`/`sameSCC` by component-index equality (`cert_onCycle`/`cert_sameSCC`)
  over hash-hoisted successor views. A rejected certificate falls back to the
  proved cached-closure path, so the result is *unconditionally* pointwise equal
  to the spec (`cyclesFast_eq`/`precCyclesFast_eq`/`hasCycleFast_eq`/
  `hasDeadlockFast_eq`) and the SCC-witness theorems transfer untouched.
  Correctness never depends on the Tarjan core; only speed does — that the
  certificate *accepts* real runs is pinned by tests (`Tests/CrossTests.lean`
  fixtures + random multisets), per the ADR-0004 tiering.
- **SCC-witness enumeration** (`Tl/Kernel/SccProps.lean`). `sccWitnesses` partitions the
  cyclic nodes by SCC exactly: `sameSCC` is an equivalence on present nodes, the
  witnesses cover exactly the present on-cycle nodes (`mem_flatten_sccWitnesses_iff`),
  two cyclic nodes share a witness iff `sameSCC` (`sccWitnesses_same_witness_iff`),
  and each witness is nonempty and absorbs any cyclic node `sameSCC` to a member
  (`sccWitnesses_ne_nil`, `mem_sccWitness_of_sameSCC`).
  Specialised to `cycles k` and `precCycles` (the `dep cycles` / deadlock reports).
- **Cycle-repair termination** (`Tl/Kernel/CycleRepair.lean`). The
  `dep cycles` → `dep remove` loop is proved sound and terminating in the
  edge-count form: an `edgeRemove` (any observed set) never creates a kind-`k`
  cycle and every surviving cyclic SCC refines a prior witness
  (`onCycle_edgeRemove`/`hasCycle_edgeRemove`/`cycles_edgeRemove_refine`); a
  well-formed remove of a present kind-`k` edge strictly decreases the present
  kind-`k` edge count (`kindEdgeCount_repairStep_lt`); every reported witness
  is nonempty and holds a present in-witness edge, so a state with no
  effective step left is already cycle-free (`cycles_witness_edge_exists`,
  `hasCycle_eq_false_of_no_effectiveStep`); and no chain of effective repair
  steps exceeds the in-witness present-edge count, with an explicit run — and
  every *maximal* run — ending at `hasCycle = false` within that bound
  (`effectiveChain_length_le`, `repair_terminates`,
  `effectiveChain_maximal_terminates`). The proved hypothesis regime is
  *remove-only*: the chain folds well-formed removes (`observed` = the edge's
  full tag set, the CLI's `dep remove` shape) with **nothing** else
  interleaved — kind-`k`-add-freedom alone is not sufficient, since a
  concurrent `create` can materialize a dangling endpoint and activate inert
  kind-`k` edges into a brand-new cycle. Total on cyclic and dangling graphs.
  The `≤ #SCCs` bound of the every-SCC-is-one-simple-cycle special case is
  deliberately excluded, not deferred: the general edge-count bound is the
  contract.
- **Canonical display parent** (`Tl/Kernel/CanonParent.lean`, ADR-0003 §4).
  Concurrent reparenting leaves several surviving `parent` edges (reported, never
  rejected); `State.canonicalParent` derives the display parent by ranking the
  candidates lexicographically by `(greatest live add-tag, parentId)` and taking
  the maximum (`maxOpt`). *Live* is the corrected tag universe — `liveTagsOf`
  drops the tombstoned tags, so an edge kept present only by a low surviving tag
  never ranks by a higher tag a `dep remove` retired. Proved, total on
  cyclic/dangling graphs (edge presence only; the parent id may be dangling):
  the winner is the `from` of a `Present` parent edge (`canonicalParent_present`);
  its `(maxLiveTag, id)` pair dominates every candidate's
  (`canonicalParent_maximal`); the selection is enumeration-order-invariant,
  unconditional (`canonParentSelect_perm`, the id tie-break mirroring the LWW
  equal-stamp value tie-break); it is `some` exactly when a present parent edge
  into the child exists (`canonicalParent_isSome_iff`); and `maxLiveTag` is
  `some` iff the edge is `Present` (`maxLiveTag_isSome_iff_present`). The pick
  logic lives once in the shared `canonParentSelect`; the CLI's hoisted accessor
  (`Tl.Cli.canonicalParentE`, over `Edge`-keyed tag/tombstone hashes) is proved
  equal to the spec for a present child (`canonicalParentE_eq`, ADR-0024 §3
  bridge) via a new `Edge`-keyed hash probe (`getElem?_hashAssocK_amap`) and the
  parent-bucket bridge (`View.parents_eq`, whose `hasIssue` hypothesis closes the
  child-present candidate-set gap).
- **`unblocks` correctness — exact & unconditional** (`Tl/Kernel/Unblocks.lean`).
  `unblocks` is *defined* as the ready-set diff `ready (withClosed s i) \ ready s`
  (`withClosed` forces `i`'s status to `Cancelled`, the full close effect incl. the
  epic-rollup ripple), so `mem_unblocks_iff` gives soundness *and* completeness with no
  side condition: `j ∈ unblocks s i ↔ j ∈ ready (withClosed s i) ∧ j ∉ ready s`.
  `ready_withClosed_eq_cancel` grounds the projection in the real op (it agrees with
  `apply s (cancelOp i st)` on `ready` when the close wins LWW), giving the operational
  `mem_unblocks_iff_cancel`. (This replaced an earlier *local* `unblocks` that
  under-reported indirect unblocks through an epic ancestor — ADR-0004 thm 10.)
- **Frame lemma** (`Tl/Kernel/Frame.lean`). `effectiveStatus` and `ready` are
  congruences over `(issues, edges, status/priority/defer registers)`, and a
  `metaSet`/`labelAdd`/`labelRemove`/`noteAdd`/`noteRemove` delta fixes all of
  those, so those side-channel writes change neither (`effectiveStatus_*`,
  `ready_*` — the notes journal drives only `updatedAt`, ADR-0027, and no
  scheduling or graph read). The
  `relate` (`related` `edgeAdd`) and `unrelate` (`related` `edgeRemove`) cases
  are both proved **unconditionally** (`effectiveStatus_relate`/`ready_relate`,
  `effectiveStatus_unrelate`/`ready_unrelate`): a second family of congruences
  keyed on the `Blocks`/`Parent` *views* (`childrenOf`/`blockersOf`/
  `dependentsOf`) rather than full `edges` equality (`*_congr_view`), discharged
  by a pair of OR-Set key-filter workhorses
  (`OrSet.presentElements_mergeAdd_filter`,
  `OrSet.presentElements_mergeTombstonesAt_filter`) showing that an add of a
  `Related` element — and a tombstone delta keyed at one — is invisible to any
  `Blocks`/`Parent` filter. The removal side carries no side condition because
  OR-Set tombstones are *element-scoped* (`removed` is a per-element map
  mirroring `adds`, and the edge kind is part of the element key): an `unrelate`
  can only change its own `Related` element's presence, for **any** observed
  payload — malformed or adversarial included — not just under honest stamp
  uniqueness. The `actor` case is not a kernel `Op` field at all.
- **OR-Set add-wins, re-add & removal effectiveness** (`Tl/Crdt/OrSet.lean`).
  ADR-0002's remove semantics as theorems over the element-scoped shape:
  `present_addWins` — an add whose tag a concurrent remove did not observe
  keeps the element present; `present_readd` — after a remove, including one
  that observed every prior tag, a fresh-tag add makes the element present
  again (the OR-Set is not a 2P-set); and
  `not_present_mergeTombstonesAt_of_observed_all` — a remove that observed
  all of an element's add-tags makes it absent, so a degenerate `Present`
  that ignored tombstones cannot satisfy the set. Stamp-freshness reliance in
  the first two is an explicit hypothesis (`st ∉ obs`, `st ∉ removedOf e`),
  discharged in a live system by the Trusted nonce-uniqueness assumption;
  effectiveness carries no such hypothesis.
- **Notes journal** (`Tl/Crdt/Journal.lean`, `Tl/Kernel/NotesInvariant.lean`;
  ADR-0027). Notes are an append-only journal of immutable entries — an OR-Set
  whose element *is* the add-tag, plus a tag-keyed payload map — so the join
  laws (`Journal.merge_comm`/`_assoc`/`_idem`, both legs) reuse the OR-Set
  lemmas and the payload semilattice (`NotePayload.join_*`, lexicographic max
  over the decoded `(text, handle, actor)` tuple, `none` actor below every
  string). Proved: concurrent adds all retained
  (`visible_both_concurrent_adds`); a remove hides its entry in either delivery
  order, by tag value (`not_visible_removeDelta_then_addDelta`); remove-exactness
  unconditional off the observed set (`visible_merge_removeDelta_iff_of_not_mem`)
  and payload non-interference (`payloads_merge_removeDelta`); no resurrection
  over the whole future (`not_visible_merge_of_tombstoned` + `tombstone_mono`);
  and deterministic rendering — the visible entries are strictly stamp-ascending
  (`visibleEntries_pairwise_lt`, canonical-form order with no tie-break levels)
  with a membership characterization (`mem_visibleEntries`) and merge-commutation
  (`visibleEntries_merge_comm`). The two structural hypotheses these carry —
  `SelfTagged` (an element's tags are its own stamp) and `PayloadTotal` (every
  visible entry has a payload, so the render skip case is unreachable) — are
  invariants of the fold, discharged for every materialized state (and the
  shipped cold path via `foldFast_eq_fold`) by `selfTagged_fold` /
  `payloadTotal_fold`. `updatedAt` is the pinned pure-state projection
  (`IssueData.updatedAtStamp`): max over the scalar registers' stamps and the
  journal's add-tags — a `noteAdd` bumps it, a `noteRemove` never does.

**Residual history** — each was defined and total in the kernel with its
soundness/completeness proof outstanding; all are now resolved. Three were
proved as stated (struck through below); the fourth — the `unrelate` frame
discharge, formerly a live tier-3 carried assumption — was *retired
structurally* rather than proved in its old form: OR-Set tombstones became
element-scoped, making `effectiveStatus_unrelate`/`ready_unrelate`
unconditional theorems with nothing left to assume. None was downgraded to a
test (Definition-of-Done #5):

- ~~**Ready-queue sortedness (ADR-0004 thm 4).**~~ **Now proved** (`Tl/Kernel/Ranking.lean`).
  Beyond determinism (free — `rankSort` is a pure function), `ready_sorted` shows the
  queue is genuinely `readyLe`-sorted (`List.Pairwise`): `readyLe` is a total order
  (`readyLe_total` + `readyLe_trans`, the lexicographic cascade priority↑/weight↓/
  createdAt↑/`id`, via a per-level characterization), and insertion sort produces a
  sorted list (`rankInsert_sorted`/`rankSort_sorted`, reusing `rankInsert_perm` for
  membership). Mathlib-free.
- ~~**Epic rollup correctness (ADR-0003).**~~ **Now proved.** The unconditional
  branches are in `Tl/Kernel/RollupSpec.lean` (`effStatusAux_cancelled` — manual-cancel
  precedence; `effStatusAux_nonEpic` — non-epic equals stored status; `effStatusAux_fuel_congr`
  — one-step fuel congruence). The fuel-adequacy step is in `Tl/Kernel/RollupAcyclic.lean`:
  on an acyclic parent graph (`ParentAcyclic` — no present child reaches its own parent)
  the rollup is fuel-irrelevant above an issue's descendant count (`effStatusAux_stable`,
  by strong induction on the descendant-closure cardinality — a child's descendant set is
  a strict subset of its parent's), so `effectiveStatus_epic` gives the full spec (an epic,
  not manually cancelled, is Done iff every present child is effectively closed). A parent
  *cycle* exhausts the fuel and falls back *conservatively* (matching ADR-0003): a manual
  `Cancelled` is honoured, a non-epic reads its stored status, and an epic falls back to
  `Open` — never its (possibly merge-injected `Done`) stored status (`effStatusAux_epic_zero_ne_done`),
  so a cycle-trapped epic never spuriously discharges a blocker; `dep cycles` also reports it.
- ~~**Thm 6/10 — SCC-witness enumeration & `unblocks`.**~~ **Now proved.** *(a)*
  `Tl/Kernel/SccProps.lean`: `sameSCC` is an equivalence on present nodes
  (`sameSCC_refl/symm/trans`, via the `reachClosure` characterization), the witnesses
  cover exactly the cyclic present nodes (`mem_flatten_sccWitnesses_iff`), and two
  cyclic nodes share a witness iff they are `sameSCC` (`sccWitnesses_same_witness_iff`)
  — i.e. exactly one witness per cyclic SCC. Instantiated for the real diagnostics
  (`mem_flatten_cycles_iff` / `cycles_same_witness_iff` and the `precCycles` pair) via
  the proved `kindSucc`/`precSucc` ⊆ `presentIssues` lemmas. *(b)* `unblocks` is now
  **exact and unconditional** (`Tl/Kernel/Unblocks.lean`): redefined as the ready-set
  diff `ready (withClosed s i) \ ready s`, so `mem_unblocks_iff` is soundness *and*
  completeness with no side condition (the force-closed projection captures the
  epic-rollup ripple a local check missed), and `ready_withClosed_eq_cancel` /
  `mem_unblocks_iff_cancel` ground it in the real `cancelOp` when the close wins LWW.

Reserved (proved when its feature is built). The destructive-GC set, pinned
with the compaction design (ADR-0008): *fold-preservation* —
`fold ops = snapshot(F) ⊕ fold(ops above F)` for a causally-stable
version-vector frontier `F` (discharge path: filter-partition +
`fold_perm`/`fold_append`); *overlap tolerance* — continuing the fold from `snapshot(stateAt F)` over
any retained superset of the above-`F` ops still yields `fold allOps`
(line-set equality closes it via `fold_append` + `fold_eq_of_mem_iff`),
which makes keep-everything unions and crash-regrowth state-harmless; and
*frontier join* — below-`F` of the pointwise-max of two frontiers is the
union of their below-`F` sets. Causal stability of `F` itself joins the
Trusted section as a tier-3 carried assumption when built. The
non-destructive snapshot needs no reserved theorem: it is the
content-keyed fold cache, already anchored by the proved `fold_append`/`fold_perm`
(ADR-0022), and it discards nothing — so any `tl log --since` cursor stays
serviceable (ADR-0025).

## Tested (I/O shell, outside the TCB)

| Claim | How |
|---|---|
| Serialization round-trip | `parse (render m) = m` over the typed-`Op`+`unknown` model (canonical render); `render (parse l) = l` on canonical lines; preserve-unknown (0008). Covered: the envelope `Record` model (`Tests/RecordTests.lean`) and the record↔Op codec — a pinned canonical line per wire verb, the escape-class bytes, one fail-closed row per decoder branch (`Tests/CodecTests.lean`). The two notes-journal record kinds (`noteAdd`/`noteRemove`, ADR-0027) ride the same battery at `v: 2`: canonical lines round-trip, and a `v: 1` note record, a missing text/handle/observed, and a malformed note handle each fail closed; the retired legacy `notes` key on a `create`/`update` routes to the preserve-unknown bag (never materialized) — pinned in `Tests/StoreTests.lean` |
| bulk import fidelity | **Built + tested** (`cliImportTests`, `Tests/CliTests.lean`): the differential test imports the committed `Tests/fixtures/import-sample.jsonl` and asserts each record materializes to its fields/status/edges (provenance `source: "imported"`) and that `ready` matches the unblocked set the graph implies; plus determinism (re-import yields a byte-identical seed segment), the two safety gates (`--force` clobber, `--allow-large`/`--max` bounds), and fail-closed malformed-line rows for invalid JSON, a missing title, an unknown status, and a duplicate source id. The **granular resource bounds** (`cliImportBoundsTests`; `checkBounds`/`checkSeedSize`, ADR-0005) get their own suite: the per-field byte/count boundaries (at-bound passes, one over fails) with the machine `context` list, the collect-all `violationCount`, the no-`.tl/`-on-refusal ordering, the `--allow-large` verbatim arm (differential: an over-bound label count survives storage uncapped), the `--max`-raises-bytes / granular-net-stays-armed split, the parent-chain depth bound, the cycle-is-a-disclosure rule (cross-checked against `dep cycles`), and the derived-seed and pre-parse per-line backstops — the remaining malformed-line classes (missing id, ill-typed per-field values, an unknown `closeResolution`, unparseable `deferUntil`, the closeResolution–status contradiction) are not yet row-per-class covered, a recorded coverage gap (0005). The JSONL `notes` field lowers to one synthetic `noteAdd` journal entry (ADR-0027/0005) — a deterministic-stamp entry with a minted handle — pinned by a notes-bearing fixture record and its `note list` / `show --json` differential rows |
| HLC clock implementation | clock-file parse/render, the local-event update rule, backward-clock and overflow cases, and the recovery branches — present-clock floor by the own-segment max (monotonicity + crash/`init`-zero recovery), absent-clock reseed from `max(all within-window segments, now())` (a one-time recovery seed); pure last-writer-wins across transport (a within-window foreign op may win; no fold-time observe-remote causal merge), corrupt-clock fail-closed (0007). The **skew window** (ADR-0007): a FOREIGN op dated beyond `now + 24h` (UTC epoch ms, so DST-immune; 24h tolerates a local-time-as-UTC misconfig) is deferred from the fold *and* from the reseed max (own segment exempt; own-id-unknown defers nothing), so a future-dated HLC can neither win LWW nor inflate the clock toward saturation; it folds once wall-clock passes it (eventually consistent), and `doctor`'s `clockSkew` check warns with the real lead. Covered: deterministic defer/fold/own-exempt + maxHlc exclusion + own-unknown + refused-suppresses-deferred (`Tests/StoreTests.lean`), the reseed-no-inflation case, the read + write disclosures, and the doctor warning (`Tests/CliTests.lean`). Convergence-safety of deferral (admission monotone-in-`now` ⇒ eventual; past-threshold the filter is the identity, composing with `fold_eq_of_mem_iff` ⇒ replicas converge) is **proved** in `Tl/Clock/Skew.lean` + `Tl/Clock/SkewConverge.lean` (`#print axioms`-clean — standard allowances only), about the exact `admittedB` predicate the fold branches on; holds for any window and regardless of clock accuracy. Real durable monotonic persistence remains Trusted below |
| SHA-256 / id mint | NIST CAVP short-message vectors + padding-boundary lengths (0/1/55/56/63/64/65 bytes, multi-block) + one worked end-to-end `(replica, hlc, nonce)` → digest → leftmost-80-bits → 16-char-id vector (0018); import-path vectors ride the differential fixtures (0005) |
| native shim (fsync, no-follow open, fd lock, entropy) | per-branch tests: symlink refusal at final and intermediate components, `O_EXCL` collision, append+sync round-trips, lock contention, hostile fixtures at the Store layer (0019/0015) |
| encoding order-preservation | the kernel proves the LWW/OR-Set order over the *decoded* `(hlc, replica, nonce)` integer triple (`Tl.Crdt.Stamp`) and delegates to the shell that the canonical wire strings (16-hex / 13 / 26 Crockford chars) compare bytewise/lexicographically in the *same* order — the linchpin that ties the proved kernel order to the on-disk bytes. Covered: all pairs of seeded + crafted near-tie triples (`Tests/CrossTests.lean`); the compiled-kernel-vs-spec property cross-check rides the same file (0007/0008, 0004) |
| CLI contract | exit codes, JSON envelope (`schemaVersion`/`ok`/`data`\|`error`), command dispatch, the verb→delta mapping (0008). The notes journal verbs (`note add`/`note list`/`note remove`, ADR-0027) are covered end-to-end in `Tests/CliTests.lean`: the add echo (the `{id, tag, time, actor, text}` entry object), the oldest-first list with `show --json` parity, prefix-handle removal carrying the no-secure-deletion disclosure, `--all` removed-placeholders (text hidden), the canonical-tag `<note-id>` fallback, a handle-collision refusal listing the colliding tags, and the retired `update --notes`/`--append-notes` usage errors that teach `tl note add`. The shared read-filter facet algebra (`Tl/Cli/Commands.lean`) is the exception in this row: it is a pure total fold, so it is **proved** rather than sampled. One characterization carries it — `applyFacets_eq_filter`: the fold is exactly a `List.filter` by the conjunction of every *active* facet's predicate. ADR-0020's "different facets compose with AND" and the `ListFacet` reading that an absent/empty flag is a no-op rather than a false-matching filter are then corollaries (`mem_applyFacets_iff`; `applyFacets_eq_self_of_inactive` at list-identity strength, instantiated at `ready`'s own facet pair by `applyFacets_readyFacets_nil`), as are order and multiplicity preservation (`applyFacets_sublist` — the characterization is what additionally rules out a fold that dropped duplicate survivors, which the sublist law alone permits) and independence from the facet list's order (`applyFacets_of_perm`). The other half of the composition rule, how a *repeated* facet composes with itself, is `labelFacet_pred_eq_true_iff` (AND, exact membership — an issue carries many labels) and `assigneeFacet_pred_eq_true_iff` (OR over the single held value, with `assigneeFacet_pred_unassigned` for the unassigned case), with `labelFacet_active_iff`/`assigneeFacet_active_iff` as the dual that a *supplied* flag is in play at all, and `mem_readyFacets_iff` composing the pair into one statement; the list-only `--status`/`--priority` facets are inline literals in `cmdList` and stay sampled. The cross-layer bound is stated at the named expression `cmdReady` evaluates (`readyRanked`), not at a copy of its derivation, and it is a characterization rather than a one-way bound: `mem_readyRanked_iff` says a row is on the queue exactly when the kernel calls it ready and every supplied facet accepts it, which rules out under-reporting as well as over-reporting — the narrowing laws alone are all satisfied by a queue that returned nothing. `readyRanked_cannot_widen` is its forward half, composing the fold laws with the kernel bridge `State.readyFast_eq` so no facet can surface a row outside the proved `ready` set (`readyFacets_isReady` reads it through `mem_ready_iff`); `readyRanked_sorted` carries `ready_sorted` through the filter so the survivors are still ranked. `--limit` is inside the perimeter too: the cap is the named `readyPage`, and `readyPage_prefix` makes `items` a prefix of that filtered ranked list whose length is `count` — including the uncapped `--limit 0` branch, which a bare `take` law does not reach — with `mem_readyPage_ready` and `readyPage_sorted` carrying the bound and the ranking to the rendered page. `facetsBypassGate_eq_true_iff` pins the closed-gate stand-down to an *active* bypassing facet — which `labelFacet_no_bypass`/`assigneeFacet_no_bypass` discharge per facet, so sharing the two with `list` (the only surface that consults the gate, and one whose facet list holds five more of its own) cannot introduce a bypass; `readyFacets_bypassGate_false` is the corollary at `ready`'s pair. The bound needs the view's `rollup` to be the batched rollup of the view's own state; that is no longer an inspection over three hand-copied construction blocks but a property of the single pure constructor production builds through (`View.ofLoaded` / `View.rollup_ofLoaded`, with `View.issueData_ofLoaded` for the indexed field the facet predicates read), so `readyRanked_cannot_widen_ofLoaded` states the bound with its hypothesis discharged. `View` keeps a public structure constructor — the test suite builds views field-by-field — so "one constructor" is a property of the production call graph, not of the type. The `cliReadyFacetTests`/`cliListFacetComposeTests` rows remain as end-to-end wiring checks over the compiled binary — that the flags reach these functions at all — and `readyRankedTests` pins the compiled `readyRanked`/`View.ofLoaded` in-process, neither being the evidence for the algebra |
| ref sync transport | **Built + tested** (`Tests/SyncTests.lean`, `Tests/CliTests.lean`): `refs/tl/log` plumbing (read/write, CAS, parent-chaining, byte-faithful non-UTF-8 blob round-trip), the complete-line union merge, the local-first worktree leg (`syncLocal` — publish the own segment with CAS-retry and no churn commit, absorb siblings via atomic rename, never the own segment), and the **read-time refresh** (`refreshFromRef` — an O(1) ref-OID trigger against the `.tl/local/ref-mark` that materializes a sibling's published change before a fold; best-effort and lock-free, degrading on a read-only FS without ever failing the read). Covered branches: no-ref skip, moved-materialize, unchanged-skip, read-only degrade, and a read absorbing a sibling end-to-end; proven with two linked worktrees sharing one ref (0001/0016). The **remote leg** (`syncRemote`, ADR-0001 §5) is also built + tested: remote resolution (`tl.remote`/branch-upstream/`origin`, detached-HEAD), `fetch → union → push` with a merge commit parented on both tips (fast-forward), non-fast-forward rejection detection, retry-once-then-`push-rejected`, and `no-upstream` (reported, not fatal). Covered against a bare remote: push-to-fresh, a second clone pulling, converged no-op, divergence recovery (fetch+union+re-push), the single non-fast-forward `pushRefLog` rejection signal, the retry-exhaustion `push-rejected` *throw* (an injected push that signals non-fast-forward on every attempt drives `reconcileRemote` through both attempts to its fuel-0 arm — the real fetch/union/CAS legs still run — asserting the `push-rejected` code, exit 10, and the "moved during the push … run `tl sync` again" message), and that a hook/policy decline is not misreported as `push-rejected` (`Tests/SyncTests.lean`). **Auto-sync** (ADR-0021) is built + tested: a write verb publishes the own segment into `refs/tl/log` after `transact` when `tl.autosync` is on (best-effort — a publish failure is a non-fatal `notes` entry, never failing the write; off by default, on for a linked worktree at `init`), and every write first absorbs the ref *before* its guards (the pre-transact local absorb, ADR-0016 write-path freshness — a directed write by id is never staler than a read). Covered: off/on/publish-failure-disclosed/no-git, and a directed close finding a sibling-only task (`Tests/CliTests.lean`) |
| "superseded by …" signal | the outcome verdict is kernel-derived: the CLI branches on the decidable `claimWonB` (`Tl/Kernel/Claim.lean`) — a claim holds iff BOTH the `status` and `assignee` winning entries are its exact stamped writes (the assignee alone would misreport a concurrent close as a win). `tl claim`'s echo stays binary won/superseded; the `ended` reading is `show`-only, on both its surfaces (the JSON claim block and the human `claim:` provenance entry, one derivation — parity): `won` for the actor's *current* claim (a same-actor cross-replica re-claim is not a loss); `ended` when the claim ran its course by the claimant's own successor write with no lost race underneath — three conditions checked only off the won path: no `status`/`assignee` write the claimant did not author — a foreign `claim`/`close`/`reopen`/`create` (the ops that touch either register) — is stamped above the surfaced own claim (a *contest scan* of the op log, because a register winner cannot carry contest history — the claimant's own later close or reopen buries a losing write, claim *or* close alike), the winning status write is the claimant's, and the assignee winner is the claimant's value or a clear the claimant authored; `superseded` otherwise. Authorship is the envelope `actor` **only** (one predicate; the contest scan is its negation) — an actor-less op, or an absent origin under compaction, is unattributable ⇒ conservative `superseded`; the replica id is not an authorship proxy (the shared-replica footgun), so even an actor-less *own* close reads `superseded`, the honest "can't prove it was you" reading (own ops carrying the actor — the `TL_ACTOR` convention — read `ended`). What stays shell and replica-relative is *which* claim is this replica's latest own `claim` op (0013). The enum growth/re-mapping shipped as `schemaVersion: 2` (0008 §ledger). Covered: a foreign claim at a later HLC supersedes the local one; a foreign close outstamping a fresh claim supersedes it; the partial win (assignee kept, status lost) reads superseded through both `claim` and `show` with an explanatory, per-status self-consistent human line; own-close and own-reopen endings (own actor present) read `ended` (JSON block + pinned human `claim: ended` line); the masking repros — a foreign claim buried under the claimant's own later close *and* under an own reopen, a foreign *close* buried under the claimant's own reopen, and an actor-less foreign claim above the own claim — stay superseded, as do another actor's close on a shared replica and an actor-less own close; the same actor's cross-replica re-claim reads `won` and its own close afterwards `ended`; a nil-claim issue emits neither surface; the `opAuthoredByOwn` / `stampAuthoredByOwn` branches (envelope-actor / actor-less / foreign / absent) are unit-pinned; an exhaustive pin holds the outcome set to exactly {won, ended, superseded} (`Tests/CliTests.lean`). **Close-side mirror** (same discipline, CLI-only — value semantics need no kernel predicate): `tl close`'s `--json` carries an additive `close: {outcome, resolution}` block, `outcome` = `won` iff terminal *as requested* (winning `closeResolution` == requested, and for `--as duplicate` the winning `duplicate-of` == requested), else `superseded` — so a concurrent foreign close with a different resolution that outstamps the local write reads `superseded` (naming the winner) instead of the old terminality-only "Closed as `<losing-resolution>`" lie; human and JSON agree; typed `CloseOutcome` at the wire boundary; additive field ⇒ no `schemaVersion` bump. Covered: a different-resolution foreign close (terminal, superseded, winner named), the duplicate-target mismatch, the not-closed reopen supersession, and a clean close (`won`) (`Tests/CliTests.lean`) |
| performance scaling | **Built + tested** (`Tests/PerfTests.lean`): every covered command path (cold batched fold, warm cached materialize, batched rollup, ready queue, cycle-diagnostics SCC machinery, provenance map, sync line-union) is ratio-asserted in CI — ×4 synthetic ops may grow ≤ ×12 (quadratic is ×16), with floors against timer noise. Native `String` equality and order both route through core comparators. The cold fold is near-linear: `Tl.Kernel.foldFast` builds each component map by batched canonical construction (mergeSort + adjacent collapse, O(N log N)) and is proved equal to the per-op `fold` (`foldFast_eq_fold`), so it ships on the cache-miss path with every fold theorem intact; the ready queue merge-sorts cached keys, and the cycle diagnostics run the checked-certificate Tarjan path (near-linear machinery, ratio-asserted on an acyclic fixture *and* a giant-SCC blocks ring; the certificate-accepted branch is itself test-pinned). The OR-Set `presentElements` view scan is near-linear on any log, tombstone-heavy included. Two sorted merge-joins retire the two quadratics: the *cross-element* tombstone probe co-traverses the add map and the per-element tombstone map (`AssocList.zipLookup`, O(#adds + #removed) — retiring the per-entry `removedOf` find), and the *within-element* liveness test co-traverses one entry's tag list against its own tombstone set (`AssocList.anyNotIn`, O(#tags + #tombstones) — retiring the per-tag membership scan, the residual an element re-added and removed n times would otherwise cost Θ(n²)). Each ships with a proved reference bridge to its per-`find`/per-tag form (`presentElements_eq_ref`, `entryLive_eq_ref`), so the enumeration and journal-liveness theorems transfer unchanged, and each is ratio-pinned by a fixture that would fail quadratically on a revert — a cross-element one (`tombstoneOps`, n edges with n/2 removed) and a within-element one (`repeatReAddOps`, one edge re-added and removed n times). The one accepted superlinear residual is SCC witness *grouping*, Θ(cyclic-nodes × cycle-components) — zero on healthy graphs, quadratic only when the cyclic set shatters into many components; an explicitly accepted cost compromise per the ADR-0023 discipline, not open work. The full diagnostics command path stays pinned by an explicit absolute-ceiling row (a backstop over that accepted residual) rather than a ratio. The human tree render shares nodes (a multi-parent diamond expands once; later encounters and re-encountered roots are marked; a parent cycle keeps its distinct "↺" marker) — pinned by the diamond, cycle, and shared-root fixtures (`Tests/CliTests.lean`) |
| materialization fold cache | **Built + tested** (`Tests/CacheTests.lean`, 0022): `.tl/local/cache` holds the folded `State` keyed per segment on `(byteLen, checksum(prefix), lineCount, refused, deferredLines)` (the checksum is the non-crypto `ByteArray.hash`, not a security digest); valid ⇒ reads/writes fold only appended suffixes plus newly-admissible skew-deferred lines on top (anchored on the **proved** `fold_append` + `fold_perm`/`fold_eq_of_mem_iff`; `AMap.ofAscList?` re-establishes canonical sortedness on decode, with `ascending_of_sorted` proving an encode is never rejected); anything stale/absent/corrupt/**wrong-version** (`cacheVersion` is now **5** — the notes-journal retype, ADR-0027, moved both the fold semantics and the codec's `notes` leg to the two-leg journal encoding) rebuilds from the segments, never repairs — including *value* corruption: the file is a non-crypto checksum line (`ByteArray.hash`; the cache is a discardable rot-check, not a security surface — tampering is the segments' trust domain, ADR-0014) over its payload, so a shape-preserving flipped digit rebuilds too. Everything a command discloses (`ops`, refusals, skips, deferrals, HLC maxima, warnings) is recomputed live per invocation — the cache changes how the state is computed, never what is reported. Covered: codec round-trip + one fail-closed row per corrupt-input shape (incl. checksum-caught value flips); every validity branch with the path taken observed directly (a marker poisoned into the cache survives iff the cache was used) — unchanged/append/new-segment/shrink/same-length-rewrite/suffix-refusal/refused-at-snapshot/deferral-admission/backwards-clock/skew-off; a seeded property pinning `materializeCached ≡ materialize` across random prefix splits and `now` advances; file lifecycle (transact warms it, corrupt caches heal on persisted reads, doctor's `persist := false` mutates nothing, `--skip-bad` bypasses, symlinked cache names refused on read and replaced—not followed—on write) |

## Trusted (carried assumptions)

This section is the home for carried assumptions — properties relied on
but neither proved in-kernel nor fully testable (AGENTS.md tier 3). Any such
property must be listed here explicitly, never relied on silently. Current
entries: verifier-bootstrap integrity — protected review ensures
`Verify/Main.lean`, `Verify/Launcher.lean`, and the CI invocation execute the
reviewed checks and do not deliberately forge the public completion marker; a
process cannot authenticate which of its own initializers printed an in-band
string, so the marker detects accidental unmarked early exits rather than
self-authenticating the gate (ADR-0026); replica-id uniqueness (scoped: holds absent a sub-git byte-copy
of `.tl/local/` — `cp -r`, an image snapshot, a CI cache; the nonce keeps LWW
total even then, so this guards segment-ownership, not convergence, ADR-0007;
minting draws from the ADR-0019 shim's OS CSPRNG — the earlier `IO.rand`
defect is closed);
the deterministic import replica-id is explicitly scoped out of live
replica ownership and used only for one-shot seed logs (ADR-0005);
issue-id uniqueness (negligible ~4e-13 birthday collision at 80-bit
SHA-256, sibling to the above, ADR-0007); nonce uniqueness within a `(HLC, replica-id)` (128-bit CSPRNG, negligible collision in that tiny space, ADR-0007) — equivalently, per-op `Stamp` (OR-Set add-tag) uniqueness: issue-id derivation hashes the stamp, and add-wins *distinctness* (two concurrent adds of one element staying distinct live tags) rests on it (`Tl/Crdt/OrSet.lean`); it no longer backs any frame lemma — the `unrelate` case is proved unconditionally now that tombstones are element-scoped; HLC monotonic persistence (its recovery path is pinned so a reseed cannot break it: an absent clock file reseeds, under the mutation lock, from `max(max HLC over all local segments, now())`, a corrupt one fails closed — ADR-0007) — and the read-time skew window (ADR-0007) rests on this same system-clock assumption for its *timeliness* (how promptly a future-dated foreign op becomes visible), but **not** for convergence, which is clock-independent: deferral is monotone in `now`, so every replica converges as its clock advances regardless of the clock's accuracy;
git ref transport (`tl sync` moves the `refs/tl/log` bytes; the old
branch-tracked history-rewrite hazard — force-push/amend dropping log ops — is
moot now that the log lives in its own ref, not the user's commits,
ADR-0001; inherited repository-routing, config-injection, and
config-relocation variables — `GIT_DIR`, the `GIT_CONFIG_*` family,
`XDG_CONFIG_HOME` — are scrubbed from every spawn, so they cannot repoint the
transport at another repository, ADR-0012/ADR-0014 T7. **Two variables are
trusted and can still repoint it:** `PATH`/`GIT_EXEC_PATH` choose the git
binary itself, and `HOME` — which `tl` cannot unset without breaking
`~/.gitconfig`, `~/.git-credentials`, and `~/.ssh` — can send a push to another
repository two ways: a `url.*.insteadOf`/`pushInsteadOf` rewrite, or wholesale
injection of the remote configuration itself (`tl.remote`,
`branch.<b>.remote`, `remote.<n>.url`/`pushurl`). Neither requires the other: a
`HOME`-only override suffices, so this is a carried assumption, not a corollary
of the trusted-binary one. It is disclosed rather than prevented — `tl
doctor`'s `gitRouting` check reports both a push-URL rewrite (raw target vs
`remote get-url --push --all`) and any push-destination key sourced from the
global scope (`externalPushConfig`) — and it misplaces the log
without losing it: the local segments survive and a later clean sync publishes
them);
fold-cache checksum adequacy (ADR-0022): cache validity concludes "the live
segment still carries the cached prefix byte-for-byte" from core's
non-crypto `ByteArray.hash`, and the cache file's own checksum line guards
its values the same way — the cache carries no crypto assumption, only that
an *accidental* corruption colliding the hash is negligible; adversarially
it is moot inside `.tl/` (anyone who can rewrite a segment is already a
trusted writer, and the cache is a discardable rot-check, not a security
surface, ADR-0014); worst case is bounded — a wrong *cache*, never wrong
log bytes, discarded by any later rebuild;
clocks/IDs/actor entering as data — each discharged by a test or trusted by
construction when implementation begins.

On the efficiency axis (ADR-0023/0024), the analogous tier-3 carried assumption is
**constant factors and the per-operation → wall-clock gap**: cache locality,
allocator behaviour, the constant in front of an `O(N)`, `Std.HashSet`/`HashMap`
amortized-O(1) (hash distribution, resizing), and per-syscall wall-clock are
neither proved nor pinned by the ratio tests (which bound growth, not absolutes).
For the shared reachability engine the operation *structure* is now proved, not
merely tested: `Tl/Kernel/ReachFrontier.lean` shows the BFS frontiers partition
the reachable set — pairwise disjoint, union = the closure, each ⊆ `presentIssues`
— so every reachable node lands in exactly one frontier. That partition
characterizes any correct engine's output, so the guard against an
output-changing regression is the pre-existing `reachBFSgo_eq`. The *work-shape*
tooth on top is over the engine's actual per-round `flatMap succ` input list:
`reachExpandTrace_eq` proves it equals those disjoint frontiers for the
list-reference engine, and `reachBFSgoTrace_flatten_nodup` carries the same to the
shipped `reachBFSgo` (instrumenting its real recursion, early-exit and all) — the
fold inputs of the engine that runs flatten to a duplicate-free list, so each
node's out-edges fold exactly once (≤ E / ≤ V). A whole-accumulator re-scan
(Θ(V·E)) recursion folds over the entire `reachClosure k` each round, so its
faithful trace is the nested closures, not the fresh layers, and these proofs fail
to compile — regressing the engine's recursion to one breaks the build, not just a
perf row (`reachBFSgo_eq` is output-only and would not catch it). What remains
carried is only the step from that per-operation count to wall-clock — the
amortized-O(1) hash primitives above. An accepted constant-factor
compromise is recorded explicitly — an ADR or a tracked task — never silently.

The trust boundary and threat model (who may read/write, and the threats
accepted or carried) are recorded in ADR-0014. Its tier-3 carried
assumptions: git access-control is `tl`'s only access control (a CRDT cannot
reject a write, so any party git lets push the ref is a trusted writer; any
reader sees all state and history); supply-chain integrity rests on the
release/signing identity and the Lean TCB (reproducibility binds binary→source,
not source→correctness); and agent-side prompt-injection resistance is the
consuming harness's job — `tl` fences content in human output, sanitizes bytes,
bounds size, and discloses provenance (untrusted-ness is stated in the schema
docs and skill, ADR-0014/0020), but cannot guarantee an LLM resists fenced data.
One bounded residual under the import bounds net (ADR-0005/0014 T6): the granular
per-field bounds are measured *after* JSON parsing, and a single input line under
the pre-parse per-line byte cap (2 MiB) can still nest brackets deeply enough to
stress `Lean.Json.parse`'s recursion before any field bound applies. It is
gated by the same total-input and per-line size caps (a deeply-nested line is
still large), so it is not unbounded; the residual is the parser's recursion
depth within a bounded line — a carried limitation, not a discharged property.

Local filesystem (ADR-0015). `O_APPEND` / `FILE_APPEND_DATA` write-atomicity
and working advisory locks are assumed on the local filesystem, and `tl` assumes
the operator places `.tl/` where they hold. Three placements are
documented-unsupported and deliberately *not* detected (ADR-0015 §8): a network
filesystem (NFS/SMB/AFP/WebDAV/9p), where neither primitive is guaranteed; a
FUSE mount, where both are delegated to a userspace process; and a directory
driven by a file-sync agent (Dropbox, iCloud Drive, OneDrive), where the
filesystem is local but another process rewrites files between invocations —
including `.tl/local/replica`, which duplicates a replica id and breaks the
ADR-0007 uniqueness assumption. In all three, convergence still holds via the
per-op nonce; ownership, HLC monotonicity, and recent-write durability do not.
The remedy is a local clone plus `git push`, or `--dir` / `TL_DIR`. The Win32
bindings of these primitives (ADR-0015 §7) are best-effort on native Windows
(our Tier-2, ADR-0006); WSL is the Supported Windows path.

The TCB is: the Lean kernel (+ its checker), the file/JSONL I/O, git, and the
system clock. Nothing else.
