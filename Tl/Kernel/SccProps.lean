/-
`Tl.Kernel.SccProps` — SCC-witness enumeration correctness (ADR-0003 §2, ADR-0004
thm 6); closes the `sccWitnesses` residual.

`sccWitnesses succ` groups the cyclic nodes by `sameSCC` (mutual reachability). This
file proves that grouping is exactly the SCC partition of the cyclic node set:

  * `sameSCC` is an **equivalence** on present nodes (reflexive, symmetric, and —
    via the `reachClosure` transitive-closure characterization — transitive);
  * the witnesses **cover** exactly the cyclic present nodes (`mem_flatten_*`);
  * two cyclic nodes share a witness **iff** `sameSCC` (`*_same_witness_iff`) — no SCC
    is split across witnesses and none are merged, i.e. exactly one witness per SCC.

Generic over any `succ` whose successors stay within `presentIssues` (true for
`kindSucc`/`precSucc`, ADR-0004 thm 6), so the bounded `reachClosure` saturates.
-/
import Tl.Kernel.Cycles
import Tl.Kernel.Reach

namespace Tl.Kernel

open Tl.Crdt

namespace State

variable {s : State} {succ : IssueId → List IssueId}

/-- `reachSet` membership is exactly reachability, for a present root. -/
theorem mem_reachSet_iff (hsucc : ∀ x, succ x ⊆ s.presentIssues) {v : IssueId}
    (hv : v ∈ s.presentIssues) (a : IssueId) :
    a ∈ s.reachSet succ v ↔ Relation.ReflTransGen (StepRel succ) v a := by
  rw [State.reachSet,
    mem_reachClosure_iff (by intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hv)
      (fun x _ => hsucc x)]
  constructor
  · rintro ⟨s', hs', h⟩; rw [List.mem_singleton] at hs'; exact hs' ▸ h
  · intro h; exact ⟨v, List.mem_singleton.mpr rfl, h⟩

/-- `sameSCC` as mutual reachability, for present nodes. -/
theorem sameSCC_iff (hsucc : ∀ x, succ x ⊆ s.presentIssues) {u v : IssueId}
    (hu : u ∈ s.presentIssues) (hv : v ∈ s.presentIssues) :
    s.sameSCC succ u v = true
      ↔ Relation.ReflTransGen (StepRel succ) v u ∧ Relation.ReflTransGen (StepRel succ) u v := by
  unfold State.sameSCC
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    mem_reachSet_iff hsucc hv u, mem_reachSet_iff hsucc hu v]

/-- `sameSCC` is reflexive on present nodes. -/
theorem sameSCC_refl (hsucc : ∀ x, succ x ⊆ s.presentIssues) {v : IssueId}
    (hv : v ∈ s.presentIssues) : s.sameSCC succ v v = true :=
  (sameSCC_iff hsucc hv hv).mpr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- `sameSCC` is symmetric. -/
theorem sameSCC_symm (u v : IssueId) : s.sameSCC succ u v = s.sameSCC succ v u := by
  unfold State.sameSCC; rw [Bool.and_comm]

/-- `sameSCC` is transitive on present nodes. -/
theorem sameSCC_trans (hsucc : ∀ x, succ x ⊆ s.presentIssues) {u v w : IssueId}
    (hu : u ∈ s.presentIssues) (hv : v ∈ s.presentIssues) (hw : w ∈ s.presentIssues)
    (huv : s.sameSCC succ u v = true) (hvw : s.sameSCC succ v w = true) :
    s.sameSCC succ u w = true := by
  obtain ⟨hvu, huv'⟩ := (sameSCC_iff hsucc hu hv).mp huv
  obtain ⟨hwv, hvw'⟩ := (sameSCC_iff hsucc hv hw).mp hvw
  exact (sameSCC_iff hsucc hu hw).mpr ⟨hwv.trans hvu, huv'.trans hvw'⟩

/-! ## Grouping correctness: `groupSCCGo` partitions the cyclic nodes by SCC -/

/-- Every node in any emitted witness is one of the `cyclic` inputs (witnesses are
    `filter`s of `cyclic`). -/
theorem groupSCCGo_mem_cyclic (cyclic : List IssueId) :
    (vs covered : List IssueId) → ∀ u,
      u ∈ (groupSCCGo s succ cyclic vs covered).flatten → u ∈ cyclic
  | [], _ => by intro u hu; simp only [groupSCCGo, List.flatten_nil] at hu; exact nomatch hu
  | v :: vs, covered => by
    intro u hu
    simp only [groupSCCGo] at hu
    by_cases hv : v ∈ covered
    · rw [if_pos hv] at hu; exact groupSCCGo_mem_cyclic cyclic vs covered u hu
    · rw [if_neg hv, List.flatten_cons, List.mem_append] at hu
      rcases hu with hu | hu
      · exact List.mem_of_mem_filter hu
      · exact groupSCCGo_mem_cyclic cyclic vs _ u hu

/-- Each emitted witness is `cyclic` filtered to one SCC representative `x ∈ vs`. -/
theorem mem_groupSCCGo_form (cyclic : List IssueId) :
    (vs covered : List IssueId) → ∀ W, W ∈ groupSCCGo s succ cyclic vs covered →
      ∃ x ∈ vs, W = cyclic.filter (fun u => s.sameSCC succ u x)
  | [], _ => by intro W hW; simp only [groupSCCGo] at hW; exact nomatch hW
  | v :: vs, covered => by
    intro W hW
    simp only [groupSCCGo] at hW
    by_cases hv : v ∈ covered
    · rw [if_pos hv] at hW
      obtain ⟨x, hx, hWx⟩ := mem_groupSCCGo_form cyclic vs covered W hW
      exact ⟨x, List.mem_cons_of_mem v hx, hWx⟩
    · rw [if_neg hv] at hW
      rcases List.mem_cons.mp hW with rfl | hW'
      · exact ⟨v, List.mem_cons_self .., rfl⟩
      · obtain ⟨x, hx, hWx⟩ := mem_groupSCCGo_form cyclic vs _ W hW'
        exact ⟨x, List.mem_cons_of_mem v hx, hWx⟩

/-- Coverage: every cyclic node still to be processed ends up covered or in a
    witness; with the initial empty `covered` this means every cyclic node is in a
    witness. -/
theorem groupSCCGo_covers (hsucc : ∀ x, succ x ⊆ s.presentIssues) (cyclic : List IssueId)
    (hcyc : cyclic ⊆ s.presentIssues) :
    (vs covered : List IssueId) → ∀ u ∈ vs, u ∈ cyclic →
      u ∈ covered ∨ u ∈ (groupSCCGo s succ cyclic vs covered).flatten
  | [], _ => by intro u hu; exact nomatch hu
  | v :: vs, covered => by
    intro u hu hucyc
    simp only [groupSCCGo]
    by_cases hv : v ∈ covered
    · rw [if_pos hv]
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact Or.inl hv
      · exact groupSCCGo_covers hsucc cyclic hcyc vs covered u hu' hucyc
    · rw [if_neg hv, List.flatten_cons]
      rcases List.mem_cons.mp hu with rfl | hu'
      · refine Or.inr ?_
        rw [List.mem_append]; refine Or.inl ?_
        rw [List.mem_filter]
        exact ⟨hucyc, sameSCC_refl hsucc (hcyc hucyc)⟩
      · rcases groupSCCGo_covers hsucc cyclic hcyc vs
          (cyclic.filter (fun w => s.sameSCC succ w v) ++ covered) u hu' hucyc with hc | hf
        · rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact Or.inr (List.mem_append.mpr (Or.inl hc))
          · exact Or.inl hc
        · exact Or.inr (List.mem_append.mpr (Or.inr hf))

/-! ## Public characterizations -/

/-- **Coverage**: the witnesses of `sccWitnesses` cover exactly the cyclic present
    nodes (ADR-0004 thm 6). -/
theorem mem_flatten_sccWitnesses_iff (hsucc : ∀ x, succ x ⊆ s.presentIssues) (u : IssueId) :
    u ∈ (s.sccWitnesses succ).flatten ↔ u ∈ s.presentIssues ∧ s.onCycle succ u = true := by
  have hcyc : (s.presentIssues.filter (s.onCycle succ)) ⊆ s.presentIssues :=
    fun a ha => List.mem_of_mem_filter ha
  rw [show u ∈ s.presentIssues ∧ s.onCycle succ u = true
        ↔ u ∈ s.presentIssues.filter (s.onCycle succ) from List.mem_filter.symm]
  unfold State.sccWitnesses
  constructor
  · exact groupSCCGo_mem_cyclic _ _ _ u
  · intro hu
    rcases groupSCCGo_covers hsucc _ hcyc _ [] u hu hu with hc | hf
    · exact nomatch hc
    · exact hf

/-- **Each witness is one SCC**: any two nodes in the same witness are `sameSCC`
    (no witness mixes SCCs). -/
theorem sccWitnesses_sameSCC (hsucc : ∀ x, succ x ⊆ s.presentIssues)
    {W : List IssueId} (hW : W ∈ s.sccWitnesses succ) {u v : IssueId}
    (hu : u ∈ W) (hv : v ∈ W) : s.sameSCC succ u v = true := by
  unfold State.sccWitnesses at hW
  obtain ⟨x, hxcyc, rfl⟩ := mem_groupSCCGo_form _ _ _ W hW
  have hxpres : x ∈ s.presentIssues := List.mem_of_mem_filter hxcyc
  rw [List.mem_filter] at hu hv
  have hupres : u ∈ s.presentIssues := List.mem_of_mem_filter hu.1
  have hvpres : v ∈ s.presentIssues := List.mem_of_mem_filter hv.1
  have hxv : s.sameSCC succ x v = true := by rw [sameSCC_symm]; exact hv.2
  exact sameSCC_trans hsucc hupres hxpres hvpres hu.2 hxv

/-- **No SCC is split**: two cyclic nodes that are `sameSCC` share a witness. With
    `sccWitnesses_sameSCC` this means exactly one witness per cyclic SCC. -/
theorem sameSCC_same_witness (hsucc : ∀ x, succ x ⊆ s.presentIssues) {u v : IssueId}
    (hucyc : u ∈ s.presentIssues.filter (s.onCycle succ))
    (hvcyc : v ∈ s.presentIssues.filter (s.onCycle succ))
    (huv : s.sameSCC succ u v = true) :
    ∃ W ∈ s.sccWitnesses succ, u ∈ W ∧ v ∈ W := by
  have hupres : u ∈ s.presentIssues := List.mem_of_mem_filter hucyc
  have hvpres : v ∈ s.presentIssues := List.mem_of_mem_filter hvcyc
  have hu_flat : u ∈ (s.sccWitnesses succ).flatten :=
    (mem_flatten_sccWitnesses_iff hsucc u).mpr ⟨hupres, (List.mem_filter.mp hucyc).2⟩
  rw [List.mem_flatten] at hu_flat
  obtain ⟨W, hW, huW⟩ := hu_flat
  refine ⟨W, hW, huW, ?_⟩
  obtain ⟨x, hxvs, hWeq⟩ :=
    mem_groupSCCGo_form _ _ _ W (by unfold State.sccWitnesses at hW; exact hW)
  have hxpres : x ∈ s.presentIssues := List.mem_of_mem_filter hxvs
  rw [hWeq] at huW ⊢
  rw [List.mem_filter] at huW ⊢
  refine ⟨hvcyc, ?_⟩
  have hvu : s.sameSCC succ v u = true := by rw [sameSCC_symm]; exact huv
  exact sameSCC_trans hsucc hvpres hupres hxpres hvu huW.2

/-- **Exactly one witness per cyclic SCC** (ADR-0004 thm 6): two cyclic present nodes
    share an `sccWitnesses` witness iff they are in the same SCC. -/
theorem sccWitnesses_same_witness_iff (hsucc : ∀ x, succ x ⊆ s.presentIssues) {u v : IssueId}
    (hucyc : u ∈ s.presentIssues.filter (s.onCycle succ))
    (hvcyc : v ∈ s.presentIssues.filter (s.onCycle succ)) :
    (∃ W ∈ s.sccWitnesses succ, u ∈ W ∧ v ∈ W) ↔ s.sameSCC succ u v = true := by
  refine ⟨fun ⟨W, hW, huW, hvW⟩ => sccWitnesses_sameSCC hsucc hW huW hvW, ?_⟩
  exact fun h => sameSCC_same_witness hsucc hucyc hvcyc h

/-! ## Instantiations for the concrete diagnostics (`cycles`, `precCycles`)

The successor of each structural-kind (`kindSucc`) and readiness (`precSucc`) graph
stays within `presentIssues` (Reach), so the generic results apply directly. -/

/-- `dep cycles k` reports exactly the present nodes on a kind-`k` cycle. -/
theorem mem_flatten_cycles_iff (s : State) (k : EdgeKind) (u : IssueId) :
    u ∈ (s.cycles k).flatten ↔ u ∈ s.presentIssues ∧ s.onCycle (s.kindSucc k) u = true :=
  mem_flatten_sccWitnesses_iff (kindSucc_subset_present s k) u

/-- `dep cycles k` gives exactly one witness per kind-`k` SCC. -/
theorem cycles_same_witness_iff (s : State) (k : EdgeKind) {u v : IssueId}
    (hu : u ∈ s.presentIssues.filter (s.onCycle (s.kindSucc k)))
    (hv : v ∈ s.presentIssues.filter (s.onCycle (s.kindSucc k))) :
    (∃ W ∈ s.cycles k, u ∈ W ∧ v ∈ W) ↔ s.sameSCC (s.kindSucc k) u v = true :=
  sccWitnesses_same_witness_iff (kindSucc_subset_present s k) hu hv

/-- The deadlock report covers exactly the present nodes on a `≺` (readiness) cycle. -/
theorem mem_flatten_precCycles_iff (s : State) (u : IssueId) :
    u ∈ s.precCycles.flatten ↔ u ∈ s.presentIssues ∧ s.onCycle s.precSucc u = true :=
  mem_flatten_sccWitnesses_iff (precSucc_subset_present s) u

/-- The deadlock report gives exactly one witness per `≺`-deadlock SCC. -/
theorem precCycles_same_witness_iff (s : State) {u v : IssueId}
    (hu : u ∈ s.presentIssues.filter (s.onCycle s.precSucc))
    (hv : v ∈ s.presentIssues.filter (s.onCycle s.precSucc)) :
    (∃ W ∈ s.precCycles, u ∈ W ∧ v ∈ W) ↔ s.sameSCC s.precSucc u v = true :=
  sccWitnesses_same_witness_iff (precSucc_subset_present s) hu hv

end State

end Tl.Kernel
