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

end Tl.Kernel
