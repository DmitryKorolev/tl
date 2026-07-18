/-
`Tl.Kernel.Frame` — the frame lemma (ADR-0003 / ADR-0004).

The side-channels — the `meta` map, `labels`, `related` edges, and the per-op
`actor` — are isolated from the verified core: writing them changes neither
`effectiveStatus` nor `ready`. This is what lets ADR-0002 keep them out of every
tracker theorem.

The proof is by *congruence*: `effectiveStatus` and `ready` read the state only
through `issues`, `edges`, and the scalar registers (status/priority/deferUntil),
so two states agreeing on those agree on both functions; and a `metaSet` /
`labelAdd` / `labelRemove` delta leaves exactly those projections fixed (its data
delta writes only `metadata`/`labels`, and its issue/edge deltas are empty).
-/
import Tl.Kernel.Theorems

namespace Tl.Kernel

open Tl.Crdt

/-! ## Congruence: `effectiveStatus` depends only on issues/edges/status -/

/-- If two states agree on present children and stored status pointwise, the
    fuel-bounded rollup agrees (at any fuel). -/
theorem effStatusAux_congr {s1 s2 : State}
    (hpc : ∀ j, s1.presentChildren j = s2.presentChildren j)
    (hst : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf) :
    (fuel : Nat) → (i : IssueId) → s1.effStatusAux fuel i = s2.effStatusAux fuel i
  | 0, i => by unfold State.effStatusAux; rw [hst i, hpc i]
  | fuel + 1, i => by
    have hlam : (fun c => Status.closed (s1.effStatusAux fuel c))
              = (fun c => Status.closed (s2.effStatusAux fuel c)) :=
      funext (fun c => by rw [effStatusAux_congr hpc hst fuel c])
    unfold State.effStatusAux
    rw [hst i, hpc i, hlam]

/-- `decide (hasIssue)` agrees when the issue sets do — rewritten through the
    `Iff` so `simp` handles the `Decidable` instance (the instances are not defeq). -/
theorem decide_hasIssue_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (c : IssueId) :
    decide (s1.hasIssue c) = decide (s2.hasIssue c) := by
  have hiff : s1.hasIssue c ↔ s2.hasIssue c := by unfold State.hasIssue; rw [hi]
  simp only [hiff]

/-- `presentChildren` agrees when issues and edges do. -/
theorem presentChildren_congr {s1 s2 : State}
    (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges) (j : IssueId) :
    s1.presentChildren j = s2.presentChildren j := by
  have hci : s1.childrenOf j = s2.childrenOf j := by
    simp only [State.childrenOf, State.presentEdges, he]
  have hpred : (fun c => decide (s1.hasIssue c)) = (fun c => decide (s2.hasIssue c)) :=
    funext (fun c => decide_hasIssue_congr hi c)
  simp only [State.presentChildren, hci, hpred]

/-- `effectiveStatus` is a congruence over `(issues, edges, status)`. -/
theorem effectiveStatus_congr {s1 s2 : State}
    (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (hst : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf)
    (i : IssueId) : s1.effectiveStatus i = s2.effectiveStatus i := by
  have hpi : s1.presentIssues = s2.presentIssues := by
    simp only [State.presentIssues, hi]
  unfold State.effectiveStatus
  rw [hpi]
  exact effStatusAux_congr (presentChildren_congr hi he) hst _ i

/-! ## Side-channel ops preserve the core projection

A `metaSet`/`labelAdd`/`labelRemove` delta has empty issue/edge components, and its
data delta's `IssueData` leaves the `status` register `none` — so merging it fixes
`issues`, `edges`, and every `status` register. -/

/-- Merging a single-key data delta whose `status` is `none` leaves every issue's
    status register unchanged. -/
theorem status_mergeSingleton (sd : AMap IssueId IssueData) (id : IssueId) (D : IssueData)
    (hD : D.status = none) (j : IssueId) :
    (((AMap.merge IssueData.merge sd (AMap.singleton id D)).find j).getD IssueData.empty).status
      = ((sd.find j).getD IssueData.empty).status := by
  rw [AMap.find_merge, AMap.find_singleton]
  by_cases hj : j = id
  · rw [if_pos hj]
    cases sd.find j with
    | none =>
      rw [optCombine_none_left]; exact hD
    | some d =>
      show Reg.merge d.status D.status = d.status
      rw [hD, Reg.merge_none_right]
  · rw [if_neg hj, optCombine_none_right]

/-- A `metaSet` leaves every status register unchanged (its data delta writes only
    `metadata`). -/
theorem metaSet_status (s : State) (id : IssueId) (st : Stamp) (k : String) (v : Option String)
    (j : IssueId) :
    ((apply s (Op.metaSet id st k v)).issueData j).status = (s.issueData j).status :=
  status_mergeSingleton s.data id (Op.metaData st k v) rfl j

/-- A `labelAdd` leaves every status register unchanged. -/
theorem labelAdd_status (s : State) (id : IssueId) (l : Label) (st : Stamp) (j : IssueId) :
    ((apply s (Op.labelAdd id l st)).issueData j).status = (s.issueData j).status :=
  status_mergeSingleton s.data id (Op.labelData st l) rfl j

/-- A `labelRemove` leaves every status register unchanged. -/
theorem labelRemove_status (s : State) (id : IssueId) (l : Label) (obs : Tl.Crdt.FinSet Stamp)
    (j : IssueId) :
    ((apply s (Op.labelRemove id l obs)).issueData j).status = (s.issueData j).status :=
  status_mergeSingleton s.data id (Op.labelRemoveData l obs) rfl j

/-! ## The frame lemma for `effectiveStatus`

Side-channel writes change neither the issue set, the edge set, nor any stored
status, so they leave `effectiveStatus` unchanged (ADR-0003 / ADR-0004). -/

theorem effectiveStatus_metaSet (s : State) (id : IssueId) (st : Stamp) (k : String)
    (v : Option String) (i : IssueId) :
    (apply s (Op.metaSet id st k v)).effectiveStatus i = s.effectiveStatus i :=
  effectiveStatus_congr (s1 := apply s (Op.metaSet id st k v)) (s2 := s)
    (OrSet.merge_empty_right s.issues) (OrSet.merge_empty_right s.edges)
    (fun j => congrArg (fun r => r.value.getD Status.Open) (metaSet_status s id st k v j)) i

theorem effectiveStatus_labelAdd (s : State) (id : IssueId) (l : Label) (st : Stamp) (i : IssueId) :
    (apply s (Op.labelAdd id l st)).effectiveStatus i = s.effectiveStatus i :=
  effectiveStatus_congr (s1 := apply s (Op.labelAdd id l st)) (s2 := s)
    (OrSet.merge_empty_right s.issues) (OrSet.merge_empty_right s.edges)
    (fun j => congrArg (fun r => r.value.getD Status.Open) (labelAdd_status s id l st j)) i

theorem effectiveStatus_labelRemove (s : State) (id : IssueId) (l : Label)
    (obs : Tl.Crdt.FinSet Stamp) (i : IssueId) :
    (apply s (Op.labelRemove id l obs)).effectiveStatus i = s.effectiveStatus i :=
  effectiveStatus_congr (s1 := apply s (Op.labelRemove id l obs)) (s2 := s)
    (OrSet.merge_empty_right s.issues) (OrSet.merge_empty_right s.edges)
    (fun j => congrArg (fun r => r.value.getD Status.Open) (labelRemove_status s id l obs j)) i

/-! ## The frame lemma for `ready`

`ready` reads the state through `issues`, `edges`, and the status/priority/defer
registers, so it too is a congruence over that projection — and the side-channel
ops fix all of it. We assemble the congruence through `weight`, `isReady`,
`readyLe`, and `rankSort`, then instantiate for `metaSet`/`labelAdd`/`labelRemove`. -/

/-- A single-key data delta whose register `proj` is `none` leaves every issue's
    `proj` register unchanged (generalizes `status_mergeSingleton`). -/
theorem reg_mergeSingleton {V : Type _} [TotalOrd V] (proj : IssueData → Reg V)
    (hmerge : ∀ a b, proj (IssueData.merge a b) = Reg.merge (proj a) (proj b))
    (hempty : proj IssueData.empty = none)
    (sd : AMap IssueId IssueData) (id : IssueId) (D : IssueData) (hD : proj D = none) (j : IssueId) :
    proj (((AMap.merge IssueData.merge sd (AMap.singleton id D)).find j).getD IssueData.empty)
      = proj ((sd.find j).getD IssueData.empty) := by
  rw [AMap.find_merge, AMap.find_singleton]
  by_cases hj : j = id
  · rw [if_pos hj]
    cases sd.find j with
    | none => rw [optCombine_none_left]; show proj D = proj IssueData.empty; rw [hempty]; exact hD
    | some d => show proj (IssueData.merge d D) = proj d; rw [hmerge, hD, Reg.merge_none_right]
  · rw [if_neg hj, optCombine_none_right]

/-! ### Function congruences over `(issues, edges, scalar registers)` -/

theorem dependentsOf_congr {s1 s2 : State} (he : s1.edges = s2.edges) (i : IssueId) :
    s1.dependentsOf i = s2.dependentsOf i := by
  simp only [State.dependentsOf, State.presentEdges, he]

theorem blockersOf_congr {s1 s2 : State} (he : s1.edges = s2.edges) (i : IssueId) :
    s1.blockersOf i = s2.blockersOf i := by
  simp only [State.blockersOf, State.presentEdges, he]

theorem isEpic_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (i : IssueId) : s1.isEpic i = s2.isEpic i := by
  simp only [State.isEpic, presentChildren_congr hi he i]

theorem createdAtOf_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (i : IssueId) :
    s1.createdAtOf i = s2.createdAtOf i := by
  simp only [State.createdAtOf, hi]

theorem blocksSucc_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges) :
    s1.blocksSucc = s2.blocksSucc := by
  funext i
  have hpred : (fun j => decide (s1.hasIssue j)) = (fun j => decide (s2.hasIssue j)) :=
    funext (fun j => decide_hasIssue_congr hi j)
  simp only [State.blocksSucc, dependentsOf_congr he i, hpred]

theorem weight_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (i : IssueId) : s1.weight i = s2.weight i := by
  have hpi : s1.presentIssues = s2.presentIssues := by simp only [State.presentIssues, hi]
  simp only [State.weight, State.reachableBlocks, State.reachClosure, blocksSucc_congr hi he, hpi]

theorem effClosed_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf) (b : IssueId) :
    s1.effClosed b = s2.effClosed b := by
  unfold State.effClosed; rw [effectiveStatus_congr hi he hstat b]

theorem blockerDischarged_congr {s1 s2 : State} (hi : s1.issues = s2.issues)
    (he : s1.edges = s2.edges)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf) :
    s1.blockerDischarged = s2.blockerDischarged := by
  funext b
  simp only [State.blockerDischarged, decide_hasIssue_congr hi b, effClosed_congr hi he hstat b]

theorem deferOk_congr {s1 s2 : State}
    (hdefer : ∀ j, (s1.issueData j).deferUntilOf = (s2.issueData j).deferUntilOf)
    (i : IssueId) (now : Instant) :
    State.deferOk (s1.issueData i) now = State.deferOk (s2.issueData i) now := by
  simp only [State.deferOk, hdefer i]

theorem isReady_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf)
    (hdefer : ∀ j, (s1.issueData j).deferUntilOf = (s2.issueData j).deferUntilOf)
    (now : Instant) : s1.isReady now = s2.isReady now := by
  funext i
  simp only [State.isReady, decide_hasIssue_congr hi i, hstat i, isEpic_congr hi he i,
    deferOk_congr hdefer i now, blockersOf_congr he i, blockerDischarged_congr hi he hstat]

theorem readyLe_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (hprio : ∀ j, (s1.issueData j).priorityOf = (s2.issueData j).priorityOf) :
    s1.readyLe = s2.readyLe := by
  funext a b
  simp only [State.readyLe, hprio a, hprio b, weight_congr hi he a, weight_congr hi he b,
    createdAtOf_congr hi a, createdAtOf_congr hi b]

theorem rankSort_congr {s1 s2 : State} (hle : s1.readyLe = s2.readyLe) :
    (l : List IssueId) → s1.rankSort l = s2.rankSort l
  | l => by
    unfold State.rankSort
    rw [hle]

/-- `ready` is a congruence over `(issues, edges, status, priority, deferUntil)`. -/
theorem ready_congr {s1 s2 : State} (hi : s1.issues = s2.issues) (he : s1.edges = s2.edges)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf)
    (hprio : ∀ j, (s1.issueData j).priorityOf = (s2.issueData j).priorityOf)
    (hdefer : ∀ j, (s1.issueData j).deferUntilOf = (s2.issueData j).deferUntilOf)
    (now : Instant) : s1.ready now = s2.ready now := by
  have hpi : s1.presentIssues = s2.presentIssues := by simp only [State.presentIssues, hi]
  unfold State.ready
  rw [hpi, isReady_congr hi he hstat hdefer now, rankSort_congr (readyLe_congr hi he hprio)]

/-! ### The frame lemma for `ready` (side-channel ops) -/

theorem ready_metaSet (s : State) (id : IssueId) (st : Stamp) (k : String) (v : Option String)
    (now : Instant) : (apply s (Op.metaSet id st k v)).ready now = s.ready now :=
  ready_congr (s1 := apply s (Op.metaSet id st k v)) (s2 := s)
    (OrSet.merge_empty_right s.issues) (OrSet.merge_empty_right s.edges)
    (fun j => congrArg (fun r => r.value.getD Status.Open)
      (reg_mergeSingleton IssueData.status (fun _ _ => rfl) rfl s.data id (Op.metaData st k v) rfl j))
    (fun j => congrArg (fun r => r.value.getD (2 : Fin 5))
      (reg_mergeSingleton IssueData.priority (fun _ _ => rfl) rfl s.data id (Op.metaData st k v) rfl j))
    (fun j => congrArg (fun r => r.value.getD none)
      (reg_mergeSingleton IssueData.deferUntil (fun _ _ => rfl) rfl s.data id (Op.metaData st k v) rfl j))
    now

theorem ready_labelAdd (s : State) (id : IssueId) (l : Label) (st : Stamp) (now : Instant) :
    (apply s (Op.labelAdd id l st)).ready now = s.ready now :=
  ready_congr (s1 := apply s (Op.labelAdd id l st)) (s2 := s)
    (OrSet.merge_empty_right s.issues) (OrSet.merge_empty_right s.edges)
    (fun j => congrArg (fun r => r.value.getD Status.Open)
      (reg_mergeSingleton IssueData.status (fun _ _ => rfl) rfl s.data id (Op.labelData st l) rfl j))
    (fun j => congrArg (fun r => r.value.getD (2 : Fin 5))
      (reg_mergeSingleton IssueData.priority (fun _ _ => rfl) rfl s.data id (Op.labelData st l) rfl j))
    (fun j => congrArg (fun r => r.value.getD none)
      (reg_mergeSingleton IssueData.deferUntil (fun _ _ => rfl) rfl s.data id (Op.labelData st l) rfl j))
    now

theorem ready_labelRemove (s : State) (id : IssueId) (l : Label) (obs : Tl.Crdt.FinSet Stamp)
    (now : Instant) : (apply s (Op.labelRemove id l obs)).ready now = s.ready now :=
  ready_congr (s1 := apply s (Op.labelRemove id l obs)) (s2 := s)
    (OrSet.merge_empty_right s.issues) (OrSet.merge_empty_right s.edges)
    (fun j => congrArg (fun r => r.value.getD Status.Open)
      (reg_mergeSingleton IssueData.status (fun _ _ => rfl) rfl s.data id (Op.labelRemoveData l obs) rfl j))
    (fun j => congrArg (fun r => r.value.getD (2 : Fin 5))
      (reg_mergeSingleton IssueData.priority (fun _ _ => rfl) rfl s.data id (Op.labelRemoveData l obs) rfl j))
    (fun j => congrArg (fun r => r.value.getD none)
      (reg_mergeSingleton IssueData.deferUntil (fun _ _ => rfl) rfl s.data id (Op.labelRemoveData l obs) rfl j))
    now

/-! ## View-based congruences (for ops that change `edges` but not the filtered views)

The congruences above key on `s1.edges = s2.edges`, which a `relate`/`unrelate`
breaks. But `effectiveStatus`/`ready` read edges *only* through the `Blocks`/`Parent`
views `childrenOf`/`blockersOf`/`dependentsOf`; these weaker congruences key on those
view equalities directly, so a `related` edge change (which fixes the views) still
goes through. -/

theorem presentChildren_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j) (j : IssueId) :
    s1.presentChildren j = s2.presentChildren j := by
  have hpred : (fun c => decide (s1.hasIssue c)) = (fun c => decide (s2.hasIssue c)) :=
    funext (fun c => decide_hasIssue_congr hi c)
  simp only [State.presentChildren, hchild j, hpred]

theorem effectiveStatus_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j)
    (hst : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf)
    (i : IssueId) : s1.effectiveStatus i = s2.effectiveStatus i := by
  have hpi : s1.presentIssues = s2.presentIssues := by simp only [State.presentIssues, hi]
  unfold State.effectiveStatus
  rw [hpi]
  exact effStatusAux_congr (presentChildren_congr_view hi hchild) hst _ i

theorem isEpic_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j) (i : IssueId) :
    s1.isEpic i = s2.isEpic i := by
  simp only [State.isEpic, presentChildren_congr_view hi hchild i]

theorem blocksSucc_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hdep : ∀ j, s1.dependentsOf j = s2.dependentsOf j) : s1.blocksSucc = s2.blocksSucc := by
  funext i
  have hpred : (fun j => decide (s1.hasIssue j)) = (fun j => decide (s2.hasIssue j)) :=
    funext (fun j => decide_hasIssue_congr hi j)
  simp only [State.blocksSucc, hdep i, hpred]

theorem weight_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hdep : ∀ j, s1.dependentsOf j = s2.dependentsOf j) (i : IssueId) :
    s1.weight i = s2.weight i := by
  have hpi : s1.presentIssues = s2.presentIssues := by simp only [State.presentIssues, hi]
  simp only [State.weight, State.reachableBlocks, State.reachClosure,
    blocksSucc_congr_view hi hdep, hpi]

theorem effClosed_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf) (b : IssueId) :
    s1.effClosed b = s2.effClosed b := by
  unfold State.effClosed; rw [effectiveStatus_congr_view hi hchild hstat b]

theorem blockerDischarged_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf) :
    s1.blockerDischarged = s2.blockerDischarged := by
  funext b
  simp only [State.blockerDischarged, decide_hasIssue_congr hi b,
    effClosed_congr_view hi hchild hstat b]

theorem isReady_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j)
    (hblock : ∀ j, s1.blockersOf j = s2.blockersOf j)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf)
    (hdefer : ∀ j, (s1.issueData j).deferUntilOf = (s2.issueData j).deferUntilOf)
    (now : Instant) : s1.isReady now = s2.isReady now := by
  funext i
  simp only [State.isReady, decide_hasIssue_congr hi i, hstat i, isEpic_congr_view hi hchild i,
    deferOk_congr hdefer i now, hblock i, blockerDischarged_congr_view hi hchild hstat]

theorem readyLe_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hdep : ∀ j, s1.dependentsOf j = s2.dependentsOf j)
    (hprio : ∀ j, (s1.issueData j).priorityOf = (s2.issueData j).priorityOf) :
    s1.readyLe = s2.readyLe := by
  funext a b
  simp only [State.readyLe, hprio a, hprio b, weight_congr_view hi hdep a,
    weight_congr_view hi hdep b, createdAtOf_congr hi a, createdAtOf_congr hi b]

/-- `ready` keyed on the `Blocks`/`Parent` views rather than full `edges` equality. -/
theorem ready_congr_view {s1 s2 : State} (hi : s1.issues = s2.issues)
    (hchild : ∀ j, s1.childrenOf j = s2.childrenOf j)
    (hblock : ∀ j, s1.blockersOf j = s2.blockersOf j)
    (hdep : ∀ j, s1.dependentsOf j = s2.dependentsOf j)
    (hstat : ∀ j, (s1.issueData j).statusOf = (s2.issueData j).statusOf)
    (hprio : ∀ j, (s1.issueData j).priorityOf = (s2.issueData j).priorityOf)
    (hdefer : ∀ j, (s1.issueData j).deferUntilOf = (s2.issueData j).deferUntilOf)
    (now : Instant) : s1.ready now = s2.ready now := by
  have hpi : s1.presentIssues = s2.presentIssues := by simp only [State.presentIssues, hi]
  unfold State.ready
  rw [hpi, isReady_congr_view hi hchild hblock hstat hdefer now,
    rankSort_congr (readyLe_congr_view hi hdep hprio)]

/-! ## The frame lemma for a `related` edge add (ADR-0003)

`Op.edgeAdd (i,j,Related)` merges one `Related` element into the edge OR-Set. Every
view `effectiveStatus`/`ready` read (`childrenOf`/`blockersOf`/`dependentsOf`) filters
edges to `Blocks`/`Parent`, so the added `Related` element is dropped — the views, and
hence `effectiveStatus`/`ready`, are fixed; issues and every register are fixed too
(empty issue/data delta). So a `relate` is invisible to the verified core.

The `unrelate` (`edgeRemove`) counterpart is proved the same way below
(`effectiveStatus_unrelate` / `ready_unrelate`): its delta tombstones the observed
tags *at the removed edge's own key* — the kind is part of the element key — so only
that `Related` element's presence can change, and the `Blocks`/`Parent` filters drop
it. Unconditional: no stamp-uniqueness side condition, for any observed payload. -/

private theorem decide_related_false (k : EdgeKind) (hk : EdgeKind.Related ≠ k)
    {q : Prop} [Decidable q] : decide (EdgeKind.Related = k ∧ q) = false :=
  decide_eq_false_iff_not.mpr (fun h => hk h.1)

/-! The three `Blocks`/`Parent` view congruences, each from one hypothesis: the
`P`-filtered present edges agree under every filter that rejects a given
`Related` element. Instantiated twice each — the `relate` add and the `unrelate`
remove — so the view filter predicates (which must stay syntactically identical
to their `State` definitions for the rewrites to fire) are stated once. -/

private theorem childrenOf_congr_of_stable {s1 s2 : State} {i0 j0 : IssueId}
    (h : ∀ (P : Edge → Bool), P (i0, j0, EdgeKind.Related) = false →
      (s1.presentEdges).filter P = (s2.presentEdges).filter P) (i : IssueId) :
    s1.childrenOf i = s2.childrenOf i := by
  unfold State.childrenOf
  rw [h (fun e => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i))
      (decide_related_false EdgeKind.Parent (fun hk => EdgeKind.noConfusion hk))]

private theorem blockersOf_congr_of_stable {s1 s2 : State} {i0 j0 : IssueId}
    (h : ∀ (P : Edge → Bool), P (i0, j0, EdgeKind.Related) = false →
      (s1.presentEdges).filter P = (s2.presentEdges).filter P) (i : IssueId) :
    s1.blockersOf i = s2.blockersOf i := by
  unfold State.blockersOf
  rw [h (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.2.1 = i))
      (decide_related_false EdgeKind.Blocks (fun hk => EdgeKind.noConfusion hk))]

private theorem dependentsOf_congr_of_stable {s1 s2 : State} {i0 j0 : IssueId}
    (h : ∀ (P : Edge → Bool), P (i0, j0, EdgeKind.Related) = false →
      (s1.presentEdges).filter P = (s2.presentEdges).filter P) (i : IssueId) :
    s1.dependentsOf i = s2.dependentsOf i := by
  unfold State.dependentsOf
  rw [h (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.1 = i))
      (decide_related_false EdgeKind.Blocks (fun hk => EdgeKind.noConfusion hk))]

/-- A `related` edge add leaves the edge set's present list fixed under any filter
    that rejects the added `Related` element (lifts the OR-Set add workhorse). -/
theorem presentEdges_relate_filter (s : State) (i0 j0 : IssueId) (st : Stamp)
    {P : Edge → Bool} (hP : P (i0, j0, EdgeKind.Related) = false) :
    ((apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).presentEdges).filter P
      = (s.presentEdges).filter P :=
  OrSet.presentElements_mergeAdd_filter s.edges (i0, j0, EdgeKind.Related) st hP

theorem childrenOf_relate (s : State) (i0 j0 : IssueId) (st : Stamp) (i : IssueId) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).childrenOf i = s.childrenOf i :=
  childrenOf_congr_of_stable
    (fun P hP => presentEdges_relate_filter s i0 j0 st (P := P) hP) i

theorem blockersOf_relate (s : State) (i0 j0 : IssueId) (st : Stamp) (i : IssueId) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).blockersOf i = s.blockersOf i :=
  blockersOf_congr_of_stable
    (fun P hP => presentEdges_relate_filter s i0 j0 st (P := P) hP) i

theorem dependentsOf_relate (s : State) (i0 j0 : IssueId) (st : Stamp) (i : IssueId) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).dependentsOf i = s.dependentsOf i :=
  dependentsOf_congr_of_stable
    (fun P hP => presentEdges_relate_filter s i0 j0 st (P := P) hP) i

theorem issues_relate (s : State) (i0 j0 : IssueId) (st : Stamp) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).issues = s.issues :=
  OrSet.merge_empty_right s.issues

theorem issueData_relate (s : State) (i0 j0 : IssueId) (st : Stamp) (j : IssueId) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).issueData j = s.issueData j := by
  unfold State.issueData
  rw [show (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).data = s.data from
    AMap.merge_empty_right IssueData.merge s.data]

/-- **Frame lemma, `relate` case (ADR-0003).** A `related` edge add changes neither
    `effectiveStatus` … -/
theorem effectiveStatus_relate (s : State) (i0 j0 : IssueId) (st : Stamp) (i : IssueId) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).effectiveStatus i = s.effectiveStatus i :=
  effectiveStatus_congr_view (issues_relate s i0 j0 st) (childrenOf_relate s i0 j0 st)
    (fun j => congrArg IssueData.statusOf (issueData_relate s i0 j0 st j)) i

/-- … **nor `ready`.** Completes the frame lemma for every side-channel write. -/
theorem ready_relate (s : State) (i0 j0 : IssueId) (st : Stamp) (now : Instant) :
    (apply s (Op.edgeAdd (i0, j0, EdgeKind.Related) st)).ready now = s.ready now :=
  ready_congr_view (issues_relate s i0 j0 st) (childrenOf_relate s i0 j0 st)
    (blockersOf_relate s i0 j0 st) (dependentsOf_relate s i0 j0 st)
    (fun j => congrArg IssueData.statusOf (issueData_relate s i0 j0 st j))
    (fun j => congrArg IssueData.priorityOf (issueData_relate s i0 j0 st j))
    (fun j => congrArg IssueData.deferUntilOf (issueData_relate s i0 j0 st j)) now

/-! ## The frame lemma for `unrelate` (a `related` `edgeRemove`, ADR-0003)

An `edgeRemove` has empty issue/data deltas (issues and registers are fixed) and
tombstones the observed tags *at the removed edge's own element key* — `Edge`
includes the kind, so a `related` removal's tombstones live under a `Related` key
and can only change *that* element's presence. Every `Blocks`/`Parent` view filter
rejects a `Related` element, so the views — and hence `effectiveStatus`/`ready` —
are fixed **unconditionally**: for any observed payload, malformed or adversarial
included, with no stamp-uniqueness side condition. (A `Blocks`/`Parent` removal is
*meant* to change the views — that is `dep remove` doing its job.) -/

theorem issues_edgeRemove (s : State) (e : Edge) (obs : FinSet Stamp) :
    (apply s (Op.edgeRemove e obs)).issues = s.issues :=
  OrSet.merge_empty_right s.issues

theorem issueData_edgeRemove (s : State) (e : Edge) (obs : FinSet Stamp) (j : IssueId) :
    (apply s (Op.edgeRemove e obs)).issueData j = s.issueData j := by
  unfold State.issueData
  rw [show (apply s (Op.edgeRemove e obs)).data = s.data from
    AMap.merge_empty_right IssueData.merge s.data]

/-- Any `edgeRemove` leaves the edge set's present list fixed under any filter that
    rejects the removed element (lifts the OR-Set tombstone workhorse). -/
theorem presentEdges_edgeRemove_filter (s : State) (e : Edge) (obs : FinSet Stamp)
    {P : Edge → Bool} (hP : P e = false) :
    ((apply s (Op.edgeRemove e obs)).presentEdges).filter P = (s.presentEdges).filter P :=
  OrSet.presentElements_mergeTombstonesAt_filter s.edges e obs hP

theorem childrenOf_unrelate (s : State) (i0 j0 : IssueId) (obs : FinSet Stamp) (i : IssueId) :
    (apply s (Op.edgeRemove (i0, j0, EdgeKind.Related) obs)).childrenOf i = s.childrenOf i :=
  childrenOf_congr_of_stable
    (fun P hP => presentEdges_edgeRemove_filter s (i0, j0, EdgeKind.Related) obs (P := P) hP) i

theorem blockersOf_unrelate (s : State) (i0 j0 : IssueId) (obs : FinSet Stamp) (i : IssueId) :
    (apply s (Op.edgeRemove (i0, j0, EdgeKind.Related) obs)).blockersOf i = s.blockersOf i :=
  blockersOf_congr_of_stable
    (fun P hP => presentEdges_edgeRemove_filter s (i0, j0, EdgeKind.Related) obs (P := P) hP) i

theorem dependentsOf_unrelate (s : State) (i0 j0 : IssueId) (obs : FinSet Stamp) (i : IssueId) :
    (apply s (Op.edgeRemove (i0, j0, EdgeKind.Related) obs)).dependentsOf i = s.dependentsOf i :=
  dependentsOf_congr_of_stable
    (fun P hP => presentEdges_edgeRemove_filter s (i0, j0, EdgeKind.Related) obs (P := P) hP) i

/-- **Frame lemma, `unrelate` case (ADR-0003).** A `related` edge removal changes
    neither `effectiveStatus` … -/
theorem effectiveStatus_unrelate (s : State) (i0 j0 : IssueId) (obs : FinSet Stamp)
    (i : IssueId) :
    (apply s (Op.edgeRemove (i0, j0, EdgeKind.Related) obs)).effectiveStatus i
      = s.effectiveStatus i :=
  effectiveStatus_congr_view (issues_edgeRemove s (i0, j0, EdgeKind.Related) obs)
    (childrenOf_unrelate s i0 j0 obs)
    (fun j => congrArg IssueData.statusOf
      (issueData_edgeRemove s (i0, j0, EdgeKind.Related) obs j)) i

/-- … **nor `ready`** — unconditionally, for any observed payload. Together with
    `ready_relate` this closes the frame lemma for every side-channel write, with
    no carried stamp-uniqueness discharge. -/
theorem ready_unrelate (s : State) (i0 j0 : IssueId) (obs : FinSet Stamp) (now : Instant) :
    (apply s (Op.edgeRemove (i0, j0, EdgeKind.Related) obs)).ready now = s.ready now :=
  ready_congr_view (issues_edgeRemove s (i0, j0, EdgeKind.Related) obs)
    (childrenOf_unrelate s i0 j0 obs) (blockersOf_unrelate s i0 j0 obs)
    (dependentsOf_unrelate s i0 j0 obs)
    (fun j => congrArg IssueData.statusOf (issueData_edgeRemove s (i0, j0, EdgeKind.Related) obs j))
    (fun j => congrArg IssueData.priorityOf (issueData_edgeRemove s (i0, j0, EdgeKind.Related) obs j))
    (fun j => congrArg IssueData.deferUntilOf (issueData_edgeRemove s (i0, j0, EdgeKind.Related) obs j))
    now

end Tl.Kernel
