/-
`Tl.Kernel.ReadyFast` — the fast ready queue and its refinement bridge.

The spec (`Ready.lean`) recomputes everything per use: each ranking comparison
recomputes both `weight`s, each `weight`
recomputes `presentIssues` (the closure fuel) and burns all fuel iterations
with no saturation exit, and every `blockersOf`/`isEpic` re-derives
`presentEdges` — superlinear per `ready` even on an edgeless graph. The fast
form hoists the present issues/edges once per call, reads rollups through
the batched map (`RollupFast`), computes each candidate's ranking key once
(`RankKey`), merge-sorts by the cached keys, and runs the reachability closure
on the O(V+E) frontier engine (`reachBFS`, `ReachBFS.lean`) instead of
re-scanning the whole accumulator each round.

The refinement bridge is `readyFast_eq` / `unblocksFast_eq` / `whyFast_eq`:
the fast forms are pointwise equal to the spec, so the proved `ready`
soundness/completeness/ordering, `unblocks` exactness, and `why` correctness
theorems transfer to the shipped path with no re-proof. The close path's
unblocked echo shares the win through `unblocksFast`.
-/
import Tl.Kernel.RollupFast
import Tl.Kernel.HashMapView
import Tl.Kernel.ReachBFS

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## Reachability congruence -/

/-- Pointwise-equal successor functions give equal closures. -/
theorem reachClosure_congr {f g : IssueId → List IssueId} (h : ∀ x, f x = g x)
    (n : Nat) (acc : List IssueId) : reachClosure f n acc = reachClosure g n acc := by
  rw [show f = g from funext h]

/-! ## Hoisted per-call views

Each helper takes the once-computed edge list and is definitionally the spec
function at `edges = s.presentEdges` — the spec already filters that list,
it just recomputes it per call. -/

/-- `blockersOf` over a hoisted edge list. -/
def blockersOfE (edges : List Edge) (i : IssueId) : List IssueId :=
  (edges.filter (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.2.1 = i))).map (·.1)

theorem blockersOfE_eq (s : State) (i : IssueId) :
    blockersOfE s.presentEdges i = s.blockersOf i := rfl

/-- `dependentsOf` over a hoisted edge list. -/
def dependentsOfE (edges : List Edge) (i : IssueId) : List IssueId :=
  (edges.filter (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.1 = i))).map (·.2.1)

theorem dependentsOfE_eq (s : State) (i : IssueId) :
    dependentsOfE s.presentEdges i = s.dependentsOf i := rfl

/-- `isReady` over the hoisted views and the rollup map. -/
def isReadyFast (m : AMap IssueId Status) (edges : List Edge)
    (pe : List (IssueId × IssueId)) (s : State) (now : Instant) (i : IssueId) : Bool :=
  decide (s.hasIssue i)
  && decide ((s.issueData i).statusOf = Status.Open)
  && (kidsOfEdges pe i).isEmpty
  && deferOk (s.issueData i) now
  && (blockersOfE edges i).all (blockerDischargedWith m s ·)

theorem isReadyFast_eq (s : State) (now : Instant) (i : IssueId) :
    isReadyFast (s.effStatusAll) s.presentEdges s.parentEdges s now i
      = s.isReady now i := by
  unfold State.isReadyFast State.isReady
  rw [kidsOfEdges_parentEdges, blockersOfE_eq]
  have hepic : (s.presentChildren i).isEmpty = !s.isEpic i := by
    unfold State.isEpic
    rw [Bool.not_not]
  have hall : (s.blockersOf i).all (blockerDischargedWith (s.effStatusAll) s ·)
            = (s.blockersOf i).all (s.blockerDischarged ·) :=
    List.all_congr rfl (fun b => blockerDischargedWith_eq s b)
  rw [hepic, hall]

/-! ## Hash/bucket-backed readiness — O(1)-amortized per-candidate reads

`isReadyFast` re-derives, per present issue, `s.issueData i` (an O(N)
`AMap.find`), `blockerDischargedWith`'s rollup `find`, and the `blockersOfE`/
`kidsOfEdges` edge filters — so `readyFast`'s candidate filter is Θ(N²)/Θ(N·E).
These forms read the rollup/data through hash copies and blockers/kids through
bucketed adjacency (all built once in `readyFast`), each bridged pointwise to
the `find`/filter form so `readyFast_eq` — hence the proved `ready`
soundness/completeness/ordering — transfers untouched. -/

/-- `Blocks` edges bucketed by target — the blockers of each issue. -/
def blocksByTarget (edges : List Edge) : Std.HashMap IssueId (List IssueId) :=
  bucketBy ((edges.filter (fun e => e.2.2 == EdgeKind.Blocks)).map (fun e => (e.2.1, e.1)))

theorem blocksByTarget_eq (edges : List Edge) (i : IssueId) :
    ((blocksByTarget edges)[i]?.getD []).reverse = blockersOfE edges i := by
  unfold blocksByTarget State.blockersOfE
  rw [getD_bucketBy, List.filter_map, List.map_map, List.filter_filter]
  dsimp only [Function.comp]
  rw [List.filter_congr (q := fun e : Edge => decide (e.2.2 = EdgeKind.Blocks ∧ e.2.1 = i))
    (fun e _ => by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩)]
  exact List.map_congr_left (fun e _ => rfl)

/-- `Blocks` edges bucketed by source — the dependents of each issue (the
    `dependentCount` per row, mirroring `blocksByTarget`). -/
def blocksBySource (edges : List Edge) : Std.HashMap IssueId (List IssueId) :=
  bucketBy ((edges.filter (fun e => e.2.2 == EdgeKind.Blocks)).map (fun e => (e.1, e.2.1)))

theorem blocksBySource_eq (edges : List Edge) (i : IssueId) :
    ((blocksBySource edges)[i]?.getD []).reverse = dependentsOfE edges i := by
  unfold blocksBySource State.dependentsOfE
  rw [getD_bucketBy, List.filter_map, List.map_map, List.filter_filter]
  dsimp only [Function.comp]
  rw [List.filter_congr (q := fun e : Edge => decide (e.2.2 = EdgeKind.Blocks ∧ e.1 = i))
    (fun e _ => by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩)]
  exact List.map_congr_left (fun e _ => rfl)

/-- `blocksSucc` via the prebuilt source-adjacency bucket (`blocksBySource`)
    and the present-issue hash set: the present-filtered dependents of `i`, every
    read O(1)-amortized (bucket lookup + `pset.contains`) instead of an O(E) edge
    filter with an O(N) `hasIssue` per successor (the old `blocksSuccE`). -/
def blocksSuccB (bsrc : Std.HashMap IssueId (List IssueId))
    (pset : Std.HashSet IssueId) (i : IssueId) : List IssueId :=
  ((bsrc[i]?.getD []).reverse).filter (fun j => pset.contains j)

theorem blocksSuccB_eq (s : State) (i : IssueId) :
    blocksSuccB (blocksBySource s.presentEdges) (hashSetOf s.presentIssues) i
      = s.blocksSucc i := by
  unfold State.blocksSuccB State.blocksSucc
  rw [blocksBySource_eq, dependentsOfE_eq]
  exact List.filter_congr (fun j _ => contains_hashSetOf_present s j)

/-- `weight` with the bucket-backed successor view and the saturation exit: the
    blocks-reachability closure reads the once-built adjacency and present set, so
    each step is O(1)-amortized per successor instead of an O(E) edge filter with
    an O(N) `hasIssue` per node.

    Accepted compromise (ADR-0023): `keyOf` calls this once per ready candidate
    (`readyFast`), so the weight phase is O(R·(V+E)) — each candidate's blocks-cone
    is computed independently, with no shared-cone memo across candidates. The
    per-cone engine is O(V+E) (the just-landed reach work); cross-candidate sharing
    is not attempted, and is not cheaply worth it: `weight` is a count of a
    reachable set, and per-node reachable-set counts are Θ(V²) worst case (a union
    of children's sets is not a fold of their counts) — no general O(V+E) — so a
    batched form would need bitset transitive closure over the SCC condensation,
    disproportionate to the bounded-R dogfooding profile (the open working set is
    small, so R is bounded and this phase is near-linear in practice). -/
def weightFast (bsrc : Std.HashMap IssueId (List IssueId))
    (pset : Std.HashSet IssueId) (n : Nat) (i : IssueId) : Nat :=
  ((reachBFS (blocksSuccB bsrc pset) n [i]).erase i).length

theorem weightFast_eq (s : State) (i : IssueId) :
    weightFast (blocksBySource s.presentEdges) (hashSetOf s.presentIssues)
        s.presentIssues.length i = s.weight i := by
  unfold State.weightFast State.weight State.reachableBlocks
  rw [reachBFS_eq _ _ _ (List.nodup_singleton i), reachClosure_congr (fun x => blocksSuccB_eq s x)]

/-- Per-issue field data via the data hash copy (= `issueData`). -/
theorem issueDataH_eq (s : State) (i : IssueId) :
    ((hashAssoc s.data.toList)[i]?).getD IssueData.empty = s.issueData i := by
  rw [getElem?_hashAssoc_amap]; rfl

/-- The per-issue min-create-HLC view: one pass over the issue OR-Set's add map,
    each entry mapped to its min add-tag HLC (`minHlcOf`). Hoisted once per `ready`
    so `keyOf` reads `createdAt` O(1)-amortized instead of an O(N) `createdAtOf`
    find per candidate. Unlike `data`, `createdAt` is not stored — it is a fold
    over the tag set — so this rides the *mapped-list* bridge, not the value copy. -/
def createdAtH (s : State) : Std.HashMap IssueId Nat :=
  hashAssoc (s.issues.adds.toList.map (fun p => (p.1, minHlcOf p.2)))

/-- Per-issue createdAt via the min-create-HLC hash view (= `createdAtOf`). -/
theorem createdAtH_eq (s : State) (i : IssueId) :
    ((s.createdAtH)[i]?).getD 0 = s.createdAtOf i := by
  unfold State.createdAtH
  rw [getElem?_hashAssoc_map_amap minHlcOf s.issues.adds i]
  unfold State.createdAtOf OrSet.tagsOf
  cases h : s.issues.adds.find i with
  | none => rfl
  | some tags => rfl

/-- A blocker is discharged — via the rollup hash and the present-issue set. -/
def blockerDischargedH (pset : Std.HashSet IssueId) (mh : Std.HashMap IssueId Status)
    (s : State) (b : IssueId) : Bool :=
  !pset.contains b || Status.closed ((mh[b]?).getD (s.effectiveStatus b))

theorem blockerDischargedH_eq (m : AMap IssueId Status) (s : State) (b : IssueId) :
    blockerDischargedH (hashSetOf s.presentIssues) (hashAssoc m.toList) s b
      = blockerDischargedWith m s b := by
  unfold State.blockerDischargedH State.blockerDischargedWith State.effClosedWith
    State.effStatusWith
  rw [contains_hashSetOf_present, getElem?_hashAssoc_amap]

/-- `isReadyFast` over the hash/bucket views: presence, status, kids, defer,
    and blocker-discharge all read O(1)-amortized. -/
def isReadyFastH (pset : Std.HashSet IssueId) (mh : Std.HashMap IssueId Status)
    (dataH : Std.HashMap IssueId IssueData) (btgt pbk : Std.HashMap IssueId (List IssueId))
    (s : State) (now : Instant) (i : IssueId) : Bool :=
  pset.contains i
  && decide (((dataH[i]?).getD IssueData.empty).statusOf = Status.Open)
  && ((pbk[i]?.getD []).reverse).isEmpty
  && deferOk ((dataH[i]?).getD IssueData.empty) now
  && ((btgt[i]?.getD []).reverse).all (blockerDischargedH pset mh s ·)

theorem isReadyFastH_eq (m : AMap IssueId Status) (s : State) (now : Instant) (i : IssueId) :
    isReadyFastH (hashSetOf s.presentIssues) (hashAssoc m.toList) (hashAssoc s.data.toList)
        (blocksByTarget s.presentEdges) (bucketBy s.parentEdges) s now i
      = isReadyFast m s.presentEdges s.parentEdges s now i := by
  have hkids : ((bucketBy s.parentEdges)[i]?.getD []).reverse = kidsOfEdges s.parentEdges i := by
    rw [getD_bucketBy]; rfl
  unfold State.isReadyFastH State.isReadyFast
  rw [contains_hashSetOf_present, issueDataH_eq, hkids, blocksByTarget_eq,
    List.all_congr rfl (fun b => blockerDischargedH_eq m s b)]

/-! ## Cached ranking keys -/

/-- One candidate's ranking key, computed once: priority ↑, weight ↓,
    createdAt ↑, id ↑ — the `readyLe` projections (ADR-0004 thm 4). -/
structure RankKey where
  prio : Nat
  weight : Nat
  createdAt : Nat
  id : IssueId

/-- `readyLe` on cached keys. -/
def keyLe (a b : RankKey) : Bool :=
  if a.prio ≠ b.prio then decide (a.prio < b.prio)
  else if a.weight ≠ b.weight then decide (b.weight < a.weight)
  else if a.createdAt ≠ b.createdAt then decide (a.createdAt < b.createdAt)
  else decide (TotalOrd.le a.id b.id)

/-- A candidate's key over the hoisted views: `prio` reads the once-built data hash
    (`dataH`) and `createdAt` the once-built min-create-HLC hash (`crH`) — both
    O(1)-amortized — instead of an O(N) `issueData` / `createdAtOf` find per
    candidate. (`weight` is still a per-candidate blocks-cone closure — its own
    ADR-0023 accepted compromise: O(V+E) per cone via the adjacency index, but no
    cross-candidate shared-cone memo.) -/
def keyOf (dataH : Std.HashMap IssueId IssueData) (crH : Std.HashMap IssueId Nat)
    (bsrc : Std.HashMap IssueId (List IssueId))
    (pset : Std.HashSet IssueId) (n : Nat) (i : IssueId) : RankKey :=
  { prio := ((dataH[i]?).getD IssueData.empty).priorityOf.val
    weight := weightFast bsrc pset n i
    createdAt := (crH[i]?).getD 0
    id := i }

theorem keyLe_keyOf_eq (s : State) (a b : IssueId) :
    keyLe (keyOf (hashAssoc s.data.toList) s.createdAtH (blocksBySource s.presentEdges) (hashSetOf s.presentIssues) s.presentIssues.length a)
          (keyOf (hashAssoc s.data.toList) s.createdAtH (blocksBySource s.presentEdges) (hashSetOf s.presentIssues) s.presentIssues.length b)
      = s.readyLe a b := by
  unfold State.keyLe State.keyOf State.readyLe
  rw [weightFast_eq, weightFast_eq, issueDataH_eq, issueDataH_eq, createdAtH_eq, createdAtH_eq]

/-- Near-linear sort on cached keys. -/
def rankSortK (l : List RankKey) : List RankKey :=
  l.mergeSort keyLe

theorem rankSortK_map (st : State) :
    (l : List IssueId) →
    rankSortK (l.map (keyOf (hashAssoc st.data.toList) st.createdAtH (blocksBySource st.presentEdges) (hashSetOf st.presentIssues) st.presentIssues.length))
      = (st.rankSort l).map (keyOf (hashAssoc st.data.toList) st.createdAtH (blocksBySource st.presentEdges) (hashSetOf st.presentIssues) st.presentIssues.length)
  | l => by
    unfold State.rankSortK State.rankSort
    exact (List.map_mergeSort
      (f := keyOf (hashAssoc st.data.toList) st.createdAtH (blocksBySource st.presentEdges) (hashSetOf st.presentIssues) st.presentIssues.length)
      (r := fun a b => st.readyLe a b)
      (s := fun a b => keyLe a b)
      (l := l) (fun a _ b _ => (keyLe_keyOf_eq st a b).symm)).symm

/-! ## The fast queue and its bridge -/

/-- `ready` with everything hoisted and cached: rollups through the batched
    map, present issues/edges computed once, one `RankKey` per candidate, the
    sort over cached keys, and the saturating closure inside `weight`. -/
def readyFast (m : AMap IssueId Status) (s : State) (now : Instant) : List IssueId :=
  let edges := s.presentEdges
  -- `parentEdgesFast` builds the child-present check through a hash set once; the
  -- plain `parentEdges` does an O(N) `hasIssue` scan per edge (Θ(E·N)) — the
  -- dominant `ready` cost at scale. Same list (`parentEdgesFast_eq`).
  let pe := s.parentEdgesFast
  let present := s.presentIssues
  -- hoist the hash/bucket views once; the per-candidate filter then reads each
  -- O(1)-amortized instead of an O(N) find / O(E) edge-filter per issue
  let pset := hashSetOf present
  let mh := hashAssoc m.toList
  let dataH := hashAssoc s.data.toList
  let crH := s.createdAtH
  let btgt := blocksByTarget edges
  let bsrc := blocksBySource edges
  let pbk := bucketBy pe
  let cands := present.filter (isReadyFastH pset mh dataH btgt pbk s now ·)
  (rankSortK (cands.map (keyOf dataH crH bsrc pset present.length))).map (·.id)

/-- **The bridge.** The fast queue is the spec's ranked queue — `ready`
    soundness, completeness, and the proved ordering transfer untouched. -/
theorem readyFast_eq (s : State) (now : Instant) :
    readyFast (s.effStatusAll) s now = s.ready now := by
  unfold State.readyFast State.ready
  dsimp only
  rw [parentEdgesFast_eq]
  have hf : s.presentIssues.filter (isReadyFastH (hashSetOf s.presentIssues)
              (hashAssoc (s.effStatusAll).toList) (hashAssoc s.data.toList)
              (blocksByTarget s.presentEdges) (bucketBy s.parentEdges) s now ·)
          = s.presentIssues.filter (s.isReady now ·) :=
    List.filter_congr (fun i _ =>
      (isReadyFastH_eq (s.effStatusAll) s now i).trans (isReadyFast_eq s now i))
  rw [hf, rankSortK_map]
  rw [List.map_map]
  show (s.rankSort _).map ((·.id) ∘ keyOf (hashAssoc s.data.toList) s.createdAtH (blocksBySource s.presentEdges) (hashSetOf s.presentIssues) s.presentIssues.length) = _
  have : ((·.id) ∘ keyOf (hashAssoc s.data.toList) s.createdAtH (blocksBySource s.presentEdges) (hashSetOf s.presentIssues) s.presentIssues.length) = (id : IssueId → IssueId) := by
    funext i
    rfl
  rw [this, List.map_id]

/-- `unblocks` through the fast queue (the close echo's path): both sides of
    the ready-diff computed fast, each over its own state's rollup map. -/
def unblocksFast (s : State) (now : Instant) (i : IssueId) : List IssueId :=
  let readyNow := readyFast (s.effStatusAll) s now
  let closed := s.withClosed i
  (readyFast (closed.effStatusAll) closed now).filter (fun j => decide (j ∉ readyNow))

theorem unblocksFast_eq (s : State) (now : Instant) (i : IssueId) :
    unblocksFast s now i = s.unblocks now i := by
  unfold State.unblocksFast State.unblocks
  dsimp only
  rw [readyFast_eq, readyFast_eq]

/-- `liveBlockersSucc` over a hoisted edge list and the rollup map. -/
def liveSuccE (m : AMap IssueId Status) (edges : List Edge) (s : State)
    (x : IssueId) : List IssueId :=
  (blockersOfE edges x).filter
    (fun b => decide (s.hasIssue b) && !effClosedWith m s b)

theorem liveSuccE_eq (s : State) (x : IssueId) :
    liveSuccE (s.effStatusAll) s.presentEdges s x = s.liveBlockersSucc x := by
  unfold State.liveSuccE State.liveBlockersSucc
  rw [blockersOfE_eq]
  apply List.filter_congr
  intro b _
  rw [effClosedWith_eq]

/-- The hoisted live-blocker seed is duplicate-free (it filters the nodup
    `blockersOfE = blockersOf`), so `reachBFS_eq` applies to `whyFast`'s seed. -/
theorem liveSuccE_nodup (m : AMap IssueId Status) (s : State) (x : IssueId) :
    (liveSuccE m s.presentEdges s x).Nodup := by
  unfold State.liveSuccE
  rw [blockersOfE_eq]
  exact List.Nodup.filter _ (blockersOf_nodup s x)

/-- `why` over the hoisted views and the rollup map: live blockers read the
    batched rollup, the closure saturates early. -/
def whyFast (m : AMap IssueId Status) (s : State) (i : IssueId) : List IssueId :=
  let edges := s.presentEdges
  reachBFS (liveSuccE m edges s) s.presentIssues.length (liveSuccE m edges s i)

theorem whyFast_eq (s : State) (i : IssueId) :
    whyFast (s.effStatusAll) s i = s.why i := by
  unfold State.whyFast State.why
  dsimp only
  rw [reachBFS_eq _ _ _ (liveSuccE_nodup (s.effStatusAll) s i),
    reachClosure_congr (liveSuccE_eq s), liveSuccE_eq s i]

/-! ## Bucket-backed `why` successor — O(deg) per cone node

`whyFast`'s successor `liveSuccE` recomputes `blockersOfE edges x` (an O(E) edge
filter) per cone node, so the `why` walk is O(K·E). `liveSuccB` reads the same
live blockers through the prebuilt `blocksByTarget` bucket (`btgt`) and the
present-set/rollup hashes — one bucket lookup + an O(1)-amortized discharge test
per blocker (O(deg) per node) — mirroring `blocksSuccB`. The live filter is the
exact negation of `blockerDischargedH` (`!present || closed`), so the bridge
`liveSuccB_eq` reuses `blockerDischargedH_eq`, and `whyFast_eq` (hence thm 10
`mem_why_iff`) transfers untouched. -/

/-- `liveBlockersSucc` via the prebuilt target-adjacency bucket (`blocksByTarget`),
    the present-issue hash set, and the rollup hash: the present, not-effectively-
    closed blockers of `x`, every read O(1)-amortized instead of an O(E) edge filter
    (the old `liveSuccE`). The keep-predicate is `!blockerDischargedH` — exactly
    `liveSuccE`'s `hasIssue ∧ ¬effClosed`. -/
def liveSuccB (btgt : Std.HashMap IssueId (List IssueId)) (pset : Std.HashSet IssueId)
    (mh : Std.HashMap IssueId Status) (s : State) (x : IssueId) : List IssueId :=
  ((btgt[x]?.getD []).reverse).filter (fun b => !blockerDischargedH pset mh s b)

theorem liveSuccB_eq (m : AMap IssueId Status) (s : State) (x : IssueId) :
    liveSuccB (blocksByTarget s.presentEdges) (hashSetOf s.presentIssues)
        (hashAssoc m.toList) s x
      = liveSuccE m s.presentEdges s x := by
  unfold State.liveSuccB State.liveSuccE
  rw [blocksByTarget_eq]
  apply List.filter_congr
  intro b _
  rw [blockerDischargedH_eq]
  unfold State.blockerDischargedWith
  rw [Bool.not_or, Bool.not_not]

/-- The bucketed live-blocker seed is duplicate-free (it equals the nodup
    `liveSuccE`), so `reachBFS_eq` applies to `whyFastH`'s seed. -/
theorem liveSuccB_nodup (m : AMap IssueId Status) (s : State) (x : IssueId) :
    (liveSuccB (blocksByTarget s.presentEdges) (hashSetOf s.presentIssues)
        (hashAssoc m.toList) s x).Nodup := by
  rw [liveSuccB_eq]
  exact liveSuccE_nodup m s x

/-- `why` over the prebuilt buckets (the shipped CLI path): the live-blocker cone
    runs on the O(V+E) frontier engine over the O(deg)-per-node `liveSuccB`, so the
    whole walk is O(V+E) instead of `whyFast`'s O(K·E). -/
def whyFastH (btgt : Std.HashMap IssueId (List IssueId)) (pset : Std.HashSet IssueId)
    (mh : Std.HashMap IssueId Status) (s : State) (n : Nat) (i : IssueId) : List IssueId :=
  reachBFS (liveSuccB btgt pset mh s) n (liveSuccB btgt pset mh s i)

/-- **The bridge.** The bucketed `why` is the spec's `why` — `whyFast_eq` (thm 10,
    `mem_why_iff`) transfers untouched, routed through `liveSuccB_eq`. -/
theorem whyFastH_eq (s : State) (i : IssueId) :
    whyFastH (blocksByTarget s.presentEdges) (hashSetOf s.presentIssues)
        (hashAssoc (s.effStatusAll).toList) s s.presentIssues.length i
      = s.why i := by
  unfold State.whyFastH State.why
  rw [reachBFS_eq _ _ _ (liveSuccB_nodup (s.effStatusAll) s i),
    reachClosure_congr (fun x => (liveSuccB_eq (s.effStatusAll) s x).trans (liveSuccE_eq s x)),
    (liveSuccB_eq (s.effStatusAll) s i).trans (liveSuccE_eq s i)]

end State

end Tl.Kernel
