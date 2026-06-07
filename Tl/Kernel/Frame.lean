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
  | 0, i => hst i
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
  status_mergeSingleton s.data id (Op.labelRemoveData obs) rfl j

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

theorem rankInsert_congr {s1 s2 : State} (hle : s1.readyLe = s2.readyLe) (x : IssueId) :
    (l : List IssueId) → s1.rankInsert x l = s2.rankInsert x l
  | [] => rfl
  | y :: ys => by unfold State.rankInsert; rw [hle, rankInsert_congr hle x ys]

theorem rankSort_congr {s1 s2 : State} (hle : s1.readyLe = s2.readyLe) :
    (l : List IssueId) → s1.rankSort l = s2.rankSort l
  | [] => rfl
  | x :: xs => by
    unfold State.rankSort
    rw [rankSort_congr hle xs, rankInsert_congr hle x (s2.rankSort xs)]

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
      (reg_mergeSingleton IssueData.status (fun _ _ => rfl) rfl s.data id (Op.labelRemoveData obs) rfl j))
    (fun j => congrArg (fun r => r.value.getD (2 : Fin 5))
      (reg_mergeSingleton IssueData.priority (fun _ _ => rfl) rfl s.data id (Op.labelRemoveData obs) rfl j))
    (fun j => congrArg (fun r => r.value.getD none)
      (reg_mergeSingleton IssueData.deferUntil (fun _ _ => rfl) rfl s.data id (Op.labelRemoveData obs) rfl j))
    now

end Tl.Kernel
