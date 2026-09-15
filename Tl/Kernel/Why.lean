/-
Completion explanations extend the dependency-only `why` with unfinished
children. This is a read-only graph: its edges never alter readiness or rollup.
The indexed frontier engine expands each discovered node once; the list view
below is proof scaffolding for the labelled relation and reachability theorem.
-/
import Tl.Kernel.ReadyFast
import Tl.Kernel.ReachFrontier

namespace Tl.Kernel

open Tl.Crdt

/-- Why a related issue appears in a completion explanation. -/
inductive WhyKind
  | dependsOn | unfinishedChild
  deriving DecidableEq, Repr

/-- A labelled outgoing explanation edge. The source is the queried node. -/
structure WhyLink where
  target : IssueId
  kind : WhyKind
  deriving DecidableEq, Repr

namespace State

/-- Shared edge assembly; closed or missing sources are terminal, and closed or
    missing targets are discharged. A child may also be an explicit blocker:
    both labels survive, while the frontier visits that target only once. -/
def whyLinksWith (discharged : IssueId → Bool)
    (blockers children : IssueId → List IssueId) (i : IssueId) : List WhyLink :=
  if discharged i then [] else
    ((children i).filter (fun j => !discharged j)).map (fun j => ⟨j, .unfinishedChild⟩) ++
    ((blockers i).filter (fun j => !discharged j)).map (fun j => ⟨j, .dependsOn⟩)

/-- State-level labelled relation (proof specification). -/
def whyLinks (s : State) : IssueId → List WhyLink :=
  whyLinksWith (fun j => !decide (s.hasIssue j) || s.effClosed j)
    s.blockersOf s.presentChildren

/-- Production adjacency: bucket lookups and hashed discharge tests, O(degree). -/
def whyLinksH (btgt pbk : Std.HashMap IssueId (List IssueId))
    (pset : Std.HashSet IssueId) (mh : Std.HashMap IssueId Status) (s : State) :
    IssueId → List WhyLink :=
  whyLinksWith (blockerDischargedH pset mh s)
    (fun i => (btgt[i]?.getD []).reverse) (fun i => (pbk[i]?.getD []).reverse)

/-- The indexed labelled edges are exactly the state relation, order included. -/
theorem whyLinksH_eq (s : State) :
    whyLinksH (blocksByTarget s.presentEdges) (bucketBy s.parentEdges)
      (hashSetOf s.presentIssues) (hashAssoc s.effStatusAll.toList) s = s.whyLinks := by
  have hd : blockerDischargedH (hashSetOf s.presentIssues)
      (hashAssoc s.effStatusAll.toList) s =
      (fun j => !decide (s.hasIssue j) || s.effClosed j) := by
    funext j
    rw [blockerDischargedH_eq]
    unfold blockerDischargedWith
    rw [effClosedWith_eq]
  have hb : (fun i => ((blocksByTarget s.presentEdges)[i]?.getD []).reverse) =
      s.blockersOf := by
    funext i
    rw [blocksByTarget_eq, blockersOfE_eq]
  have hc : (fun i => ((bucketBy s.parentEdges)[i]?.getD []).reverse) =
      s.presentChildren := by
    funext i
    rw [kidsBucket_eq rfl, kidsOfEdges_parentEdges]
  unfold whyLinksH whyLinks
  rw [hd, hb, hc]

/-- Each label has its own meaning; neither endpoint is discharged. -/
theorem mem_whyLinks (s : State) (i j : IssueId) (k : WhyKind) :
    WhyLink.mk j k ∈ s.whyLinks i ↔
      s.hasIssue i ∧ s.effClosed i = false ∧
      s.hasIssue j ∧ s.effClosed j = false ∧
      (match k with
       | .dependsOn => j ∈ s.blockersOf i
       | .unfinishedChild => j ∈ s.presentChildren i) := by
  unfold whyLinks whyLinksWith
  dsimp only
  by_cases hi : s.hasIssue i
  · by_cases hci : s.effClosed i = false
    · have hsource : (!decide (s.hasIssue i) || s.effClosed i) = false := by
        rw [decide_eq_true hi, Bool.not_true, hci, Bool.false_or]
      rw [if_neg (by rw [hsource]; exact Bool.false_ne_true)]
      cases k <;>
        simp only [List.mem_append, List.mem_map, List.mem_filter,
          WhyLink.mk.injEq, reduceCtorEq, exists_false,
          false_or, or_false, exists_eq_left, false_and, Bool.not_or, Bool.not_not,
          Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          hi, hci, true_and, and_assoc, and_comm, and_left_comm]
    · have hc : s.effClosed i = true := Bool.eq_true_of_not_eq_false hci
      simp only [hc, Bool.or_true, ite_true, List.not_mem_nil,
        Bool.true_eq_false, false_and, and_false]
  · simp only [hi, decide_false, Bool.not_false, Bool.true_or, ite_true,
      List.not_mem_nil, false_and]

/-- Unlabelled successor for the frontier; labels remain on the original edges. -/
def whyWorkSucc (links : IssueId → List WhyLink) (i : IssueId) : List IssueId :=
  (links i).map WhyLink.target

/-- The root is included once, including in cycles. Singleton seeding avoids
    duplicate frontier expansion when one target has both relationship kinds. -/
def whyWork (links : IssueId → List WhyLink) (n : Nat) (i : IssueId) : List IssueId :=
  reachBFS (whyWorkSucc links) n [i]

/-- Every successor is present, so the present-issue count is sufficient fuel. -/
theorem whyWorkSucc_subset (s : State) (i : IssueId) :
    whyWorkSucc s.whyLinks i ⊆ s.presentIssues := by
  intro j hj
  obtain ⟨⟨target, kind⟩, hlink, rfl⟩ := List.mem_map.mp hj
  obtain ⟨_, _, hp, _, _⟩ := (mem_whyLinks s i target kind).mp hlink
  exact (OrSet.mem_presentElements s.issues target).mpr hp

/-- Soundness and completeness of the shipped frontier over the labelled state
    relation, including mixed cycles and multiple parents. -/
theorem mem_whyWork_iff (s : State) (i j : IssueId) (hi : s.hasIssue i) :
    j ∈ whyWork s.whyLinks s.presentIssues.length i ↔
      Relation.ReflTransGen (StepRel (whyWorkSucc s.whyLinks)) i j := by
  unfold whyWork
  rw [mem_reachBFS_iff, mem_reachClosure_iff
    (by intro x hx; rw [List.mem_singleton] at hx
        exact hx ▸ (OrSet.mem_presentElements s.issues i).mpr hi)
    (fun x _ => whyWorkSucc_subset s x)]
  simp only [List.mem_singleton, exists_eq_left]

/-- Every outgoing target of a discovered node is also in the explanation.
    JSON can therefore retain cyclic/shared edges without dangling node rows. -/
theorem whyWork_closed (s : State) (i x : IssueId) (link : WhyLink)
    (hi : s.hasIssue i) (hx : x ∈ whyWork s.whyLinks s.presentIssues.length i)
    (he : link ∈ s.whyLinks x) :
    link.target ∈ whyWork s.whyLinks s.presentIssues.length i := by
  apply (mem_whyWork_iff s i link.target hi).mpr
  apply ((mem_whyWork_iff s i x hi).mp hx).tail
  exact List.mem_map.mpr ⟨link, he, rfl⟩

/-- The actual indexed call inherits the exact reachability characterization. -/
theorem mem_whyWorkH_iff (s : State) (i j : IssueId) (hi : s.hasIssue i) :
    j ∈ whyWork (whyLinksH (blocksByTarget s.presentEdges) (bucketBy s.parentEdges)
      (hashSetOf s.presentIssues) (hashAssoc s.effStatusAll.toList) s)
      s.presentIssues.length i ↔
      Relation.ReflTransGen (StepRel (whyWorkSucc s.whyLinks)) i j := by
  rw [whyLinksH_eq]
  exact mem_whyWork_iff s i j hi

/-- No output node is repeated, even when reached through both edge kinds. -/
theorem whyWork_nodup (links : IssueId → List WhyLink) (n : Nat) (i : IssueId) :
    (whyWork links n i).Nodup := by
  unfold whyWork
  rw [reachBFS_eq _ _ _ (List.nodup_singleton i)]
  exact reachClosure_nodup _ _ (List.nodup_singleton i) n

end State
end Tl.Kernel
