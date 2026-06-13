/-
`Tl.Kernel.ReadyFast` — the fast ready queue and its refinement bridge.

The spec (`Ready.lean`) recomputes everything per use: each ranking comparison
recomputes both `weight`s, each `weight`
recomputes `presentIssues` (the closure fuel) and burns ALL fuel iterations
with no saturation exit, and every `blockersOf`/`isEpic` re-derives
`presentEdges` — superlinear per `ready` even on an edgeless graph. The fast
form hoists the present issues/edges once per call, reads rollups through
the batched map (`RollupFast`), computes each candidate's ranking key once
(`RankKey`), merge-sorts by the cached keys, and saturates the reachability
closure early (`reachFix` stops at the first fixed point — justified by
`iterateN_of_fixed`, fixpoint stability).

The refinement bridge is `readyFast_eq` / `unblocksFast_eq` / `whyFast_eq`:
the fast forms are pointwise EQUAL to the spec, so the proved `ready`
soundness/completeness/ordering, `unblocks` exactness, and `why` correctness
theorems transfer to the shipped path with no re-proof. The close path's
unblocked echo shares the win through `unblocksFast`.
-/
import Tl.Kernel.RollupFast
import Tl.Kernel.HashMapView

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## Saturating reachability -/

/-- `reachClosure` with a saturation exit: stop at the first fixed point of
    `reachStep` — on real graphs the closure stabilizes in diameter-many
    steps, not `|presentIssues|`-many. -/
def reachFix (succ : IssueId → List IssueId) : Nat → List IssueId → List IssueId
  | 0, acc => acc
  | n + 1, acc =>
    let next := reachStep succ acc
    if next == acc then acc else reachFix succ n next

/-- Fixpoint stability: iterating from a fixed point goes nowhere. -/
theorem iterateN_of_fixed {α : Type _} (f : α → α) {a : α} (h : f a = a) :
    (n : Nat) → iterateN f n a = a
  | 0 => rfl
  | n + 1 => by
    unfold iterateN
    rw [h]
    exact iterateN_of_fixed f h n

/-- The saturation exit is exact: `reachFix` equals the bounded iteration. -/
theorem reachFix_eq (succ : IssueId → List IssueId) :
    (n : Nat) → (acc : List IssueId) → reachFix succ n acc = reachClosure succ n acc
  | 0, _ => rfl
  | n + 1, acc => by
    unfold reachFix
    show (if reachStep succ acc == acc then acc else reachFix succ n (reachStep succ acc))
       = reachClosure succ (n + 1) acc
    by_cases h : (reachStep succ acc == acc) = true
    · rw [if_pos h]
      have hfix : reachStep succ acc = acc := eq_of_beq h
      show acc = iterateN (reachStep succ) (n + 1) acc
      rw [show iterateN (reachStep succ) (n + 1) acc
            = iterateN (reachStep succ) n (reachStep succ acc) from rfl,
        hfix, iterateN_of_fixed (reachStep succ) hfix n]
    · rw [if_neg h]
      exact reachFix_eq succ n (reachStep succ acc)

/-- Pointwise-equal successor functions give equal closures. -/
theorem reachClosure_congr {f g : IssueId → List IssueId} (h : ∀ x, f x = g x)
    (n : Nat) (acc : List IssueId) : reachClosure f n acc = reachClosure g n acc := by
  rw [show f = g from funext h]

/-! ## Hoisted per-call views

Each helper takes the once-computed edge list and is DEFINITIONALLY the spec
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

/-- `blocksSucc` over a hoisted edge list. -/
def blocksSuccE (edges : List Edge) (s : State) (i : IssueId) : List IssueId :=
  ((edges.filter (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.1 = i))).map (·.2.1)).filter
    (fun j => decide (s.hasIssue j))

theorem blocksSuccE_eq (s : State) (i : IssueId) :
    blocksSuccE s.presentEdges s i = s.blocksSucc i := rfl

/-- `weight` with the hoisted successor view and the saturation exit. -/
def weightFast (edges : List Edge) (s : State) (n : Nat) (i : IssueId) : Nat :=
  ((reachFix (blocksSuccE edges s) n [i]).erase i).length

theorem weightFast_eq (s : State) (i : IssueId) :
    weightFast s.presentEdges s s.presentIssues.length i = s.weight i := by
  unfold State.weightFast State.weight State.reachableBlocks
  rw [reachFix_eq, reachClosure_congr (fun x => blocksSuccE_eq s x)]

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

/-- Per-issue field data via the data hash copy (= `issueData`). -/
theorem issueDataH_eq (s : State) (i : IssueId) :
    ((hashAssoc s.data.toList)[i]?).getD IssueData.empty = s.issueData i := by
  rw [getElem?_hashAssoc_amap]; rfl

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

/-- A candidate's key over the hoisted views. -/
def keyOf (edges : List Edge) (s : State) (n : Nat) (i : IssueId) : RankKey :=
  { prio := (s.issueData i).priorityOf.val
    weight := weightFast edges s n i
    createdAt := s.createdAtOf i
    id := i }

theorem keyLe_keyOf_eq (s : State) (a b : IssueId) :
    keyLe (keyOf s.presentEdges s s.presentIssues.length a)
          (keyOf s.presentEdges s s.presentIssues.length b)
      = s.readyLe a b := by
  unfold State.keyLe State.keyOf State.readyLe
  rw [weightFast_eq, weightFast_eq]

/-- Near-linear sort on cached keys. -/
def rankSortK (l : List RankKey) : List RankKey :=
  l.mergeSort keyLe

theorem rankSortK_map (st : State) :
    (l : List IssueId) →
    rankSortK (l.map (keyOf st.presentEdges st st.presentIssues.length))
      = (st.rankSort l).map (keyOf st.presentEdges st st.presentIssues.length)
  | l => by
    unfold State.rankSortK State.rankSort
    exact (List.map_mergeSort
      (f := keyOf st.presentEdges st st.presentIssues.length)
      (r := fun a b => st.readyLe a b)
      (s := fun a b => keyLe a b)
      (l := l) (fun a _ b _ => (keyLe_keyOf_eq st a b).symm)).symm

/-! ## The fast queue and its bridge -/

/-- `ready` with everything hoisted and cached: rollups through the batched
    map, present issues/edges computed once, one `RankKey` per candidate, the
    sort over cached keys, and the saturating closure inside `weight`. -/
def readyFast (m : AMap IssueId Status) (s : State) (now : Instant) : List IssueId :=
  let edges := s.presentEdges
  let pe := s.parentEdges
  let present := s.presentIssues
  -- hoist the hash/bucket views ONCE; the per-candidate filter then reads each
  -- O(1)-amortized instead of an O(N) find / O(E) edge-filter per issue
  let pset := hashSetOf present
  let mh := hashAssoc m.toList
  let dataH := hashAssoc s.data.toList
  let btgt := blocksByTarget edges
  let pbk := bucketBy pe
  let cands := present.filter (isReadyFastH pset mh dataH btgt pbk s now ·)
  (rankSortK (cands.map (keyOf edges s present.length))).map (·.id)

/-- **The bridge.** The fast queue IS the spec's ranked queue — `ready`
    soundness, completeness, and the proved ordering transfer untouched. -/
theorem readyFast_eq (s : State) (now : Instant) :
    readyFast (s.effStatusAll) s now = s.ready now := by
  unfold State.readyFast State.ready
  dsimp only
  have hf : s.presentIssues.filter (isReadyFastH (hashSetOf s.presentIssues)
              (hashAssoc (s.effStatusAll).toList) (hashAssoc s.data.toList)
              (blocksByTarget s.presentEdges) (bucketBy s.parentEdges) s now ·)
          = s.presentIssues.filter (s.isReady now ·) :=
    List.filter_congr (fun i _ =>
      (isReadyFastH_eq (s.effStatusAll) s now i).trans (isReadyFast_eq s now i))
  rw [hf, rankSortK_map]
  rw [List.map_map]
  show (s.rankSort _).map ((·.id) ∘ keyOf s.presentEdges s s.presentIssues.length) = _
  have : ((·.id) ∘ keyOf s.presentEdges s s.presentIssues.length) = (id : IssueId → IssueId) := by
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

/-- `why` over the hoisted views and the rollup map: live blockers read the
    batched rollup, the closure saturates early. -/
def whyFast (m : AMap IssueId Status) (s : State) (i : IssueId) : List IssueId :=
  let edges := s.presentEdges
  reachFix (liveSuccE m edges s) s.presentIssues.length (liveSuccE m edges s i)

theorem whyFast_eq (s : State) (i : IssueId) :
    whyFast (s.effStatusAll) s i = s.why i := by
  unfold State.whyFast State.why
  dsimp only
  rw [reachFix_eq, reachClosure_congr (liveSuccE_eq s), liveSuccE_eq s i]

end State

end Tl.Kernel
