/-
`Tl.Kernel.RollupAcyclic` — fuel-adequacy of the epic rollup on acyclic graphs
(ADR-0003 §3); closes the last rollup residual.

`effectiveStatus` runs `effStatusAux` with `presentIssues.length` fuel. On a parent
graph with no cycle, that outlasts the longest descending chain, so the rollup is
*fuel-irrelevant* above an issue's descendant count — and hence equals its spec
(`RollupSpec.effectiveStatus_epic_of_stable`). The measure is the descendant-closure
cardinality: a present child's descendant set is a **strict** subset of its parent's
(the parent is a descendant of itself but, acyclicity, not of its child), so the
cardinality strictly drops — a clean strong-induction measure feeding the one-step
fuel congruence. Reuses the `reachClosure` transitive-closure characterization
(`Reach.mem_reachClosure_iff`) and its Mathlib cardinality lemmas (ADR-0009).
-/
import Tl.Kernel.RollupSpec
import Tl.Kernel.Reach

namespace Tl.Kernel

open Tl.Crdt

/-- The parent graph is acyclic: no present child can reach its own parent (so no
    `parent`-cycle). Stated over the rollup's own `presentChildren` descent. -/
def ParentAcyclic (s : State) : Prop :=
  ∀ i c, c ∈ s.presentChildren i → ¬ Relation.ReflTransGen (StepRel s.presentChildren) c i

/-- The descendant closure of `i` under `presentChildren` (saturated at
    `presentIssues.length`, the `reachClosure` bound). -/
def desc (s : State) (i : IssueId) : List IssueId :=
  State.reachClosure s.presentChildren s.presentIssues.length [i]

/-- The descendant-count measure. -/
def descCard (s : State) (i : IssueId) : Nat := (desc s i).toFinset.card

/-- Membership in the descendant closure is exactly reachability (for a present root). -/
theorem mem_desc_iff (s : State) (i : IssueId) (hi : i ∈ s.presentIssues) (a : IssueId) :
    a ∈ desc s i ↔ Relation.ReflTransGen (StepRel s.presentChildren) i a := by
  rw [desc, mem_reachClosure_iff (by intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hi)
    (fun x _ => presentChildren_subset_present s x)]
  constructor
  · rintro ⟨s', hs', h⟩; rw [List.mem_singleton] at hs'; exact hs' ▸ h
  · intro h; exact ⟨i, List.mem_singleton.mpr rfl, h⟩

/-- A node reachable from a present node through `presentChildren` is present. -/
theorem reachable_present (s : State) {c x : IssueId} (hc : c ∈ s.presentIssues)
    (h : Relation.ReflTransGen (StepRel s.presentChildren) c x) : x ∈ s.presentIssues := by
  induction h with
  | refl => exact hc
  | tail _ hbx ih => exact presentChildren_subset_present s _ hbx

/-- `i` is in its own descendant closure (reflexive reachability). -/
theorem mem_desc_self (s : State) (i : IssueId) (hi : i ∈ s.presentIssues) : i ∈ desc s i :=
  (mem_desc_iff s i hi i).mpr Relation.ReflTransGen.refl

/-- The measure is positive at a present issue. -/
theorem descCard_pos (s : State) (i : IssueId) (hi : i ∈ s.presentIssues) : 0 < descCard s i :=
  Finset.card_pos.mpr ⟨i, List.mem_toFinset.mpr (mem_desc_self s i hi)⟩

/-- A present child's descendant closure is a subset of its parent's. -/
theorem desc_subset (s : State) (i c : IssueId) (hci : c ∈ s.presentChildren i)
    (hi : i ∈ s.presentIssues) (hcpres : c ∈ s.presentIssues) :
    (desc s c).toFinset ⊆ (desc s i).toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  rw [mem_desc_iff s c hcpres] at hx
  rw [mem_desc_iff s i hi]
  exact Relation.ReflTransGen.head hci hx

/-- Acyclicity ⇒ a present child's descendant count is strictly below its parent's. -/
theorem descCard_child_lt (s : State) (hac : ParentAcyclic s) (i c : IssueId)
    (hci : c ∈ s.presentChildren i) (hi : i ∈ s.presentIssues) : descCard s c < descCard s i := by
  have hcpres : c ∈ s.presentIssues := presentChildren_subset_present s i hci
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset (desc_subset s i c hci hi hcpres)).mpr
    ⟨i, List.mem_toFinset.mpr (mem_desc_self s i hi), ?_⟩
  rw [List.mem_toFinset, mem_desc_iff s c hcpres]
  exact hac i c hci

/-- A present child's descendant count is `≤ presentIssues.length - 1`: the parent is
    a present issue outside the child's closure. -/
theorem descCard_child_le_pred (s : State) (hac : ParentAcyclic s) (i c : IssueId)
    (hci : c ∈ s.presentChildren i) (hi : i ∈ s.presentIssues) (N : Nat)
    (hN : s.presentIssues.length = N + 1) : descCard s c ≤ N := by
  have hcpres : c ∈ s.presentIssues := presentChildren_subset_present s i hci
  have hsub : (desc s c).toFinset ⊆ s.presentIssues.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact reachable_present s hcpres ((mem_desc_iff s c hcpres x).mp hx)
  have hssub : (desc s c).toFinset ⊂ s.presentIssues.toFinset := by
    refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨i, List.mem_toFinset.mpr hi, ?_⟩
    rw [List.mem_toFinset, mem_desc_iff s c hcpres]
    exact hac i c hci
  have h1 : descCard s c < s.presentIssues.toFinset.card := Finset.card_lt_card hssub
  have h2 : s.presentIssues.toFinset.card ≤ N + 1 := hN ▸ List.toFinset_card_le s.presentIssues
  exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le h1 h2)

/-! ## Fuel-stability by strong induction on the descendant count -/

/-- Strong-induction core: above the descendant count, the rollup is fuel-irrelevant.
    Structural on `n`, with `descCard s i ≤ n`; the recursive call drops to a child,
    whose count is strictly smaller (`descCard_child_lt`). -/
theorem effStatusAux_stable_aux (s : State) (hac : ParentAcyclic s) :
    (n : Nat) → (i : IssueId) → i ∈ s.presentIssues → descCard s i ≤ n →
    (a b : Nat) → descCard s i ≤ a → descCard s i ≤ b → s.effStatusAux a i = s.effStatusAux b i
  | 0, i, hi, hMn, _, _, _, _ =>
      absurd (Nat.lt_of_lt_of_le (descCard_pos s i hi) hMn) (Nat.lt_irrefl 0)
  | n + 1, i, hi, hMn, a, b, ha, hb => by
    by_cases hep : s.isEpic i = true
    · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (descCard_pos s i hi) ha))
      obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (descCard_pos s i hi) hb))
      apply State.effStatusAux_fuel_congr
      intro c hc
      have hcpres : c ∈ s.presentIssues := presentChildren_subset_present s i hc
      have hlt : descCard s c < descCard s i := descCard_child_lt s hac i c hc hi
      have hcn : descCard s c ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hMn)
      have hca : descCard s c ≤ a' := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt ha)
      have hcb : descCard s c ≤ b' := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hb)
      exact effStatusAux_stable_aux s hac n c hcpres hcn a' b' hca hcb
    · have hne : s.isEpic i = false := by
        cases hb2 : s.isEpic i with
        | true => exact absurd hb2 hep
        | false => rfl
      rw [State.effStatusAux_nonEpic s i hne a, State.effStatusAux_nonEpic s i hne b]

/-- **Fuel-adequacy (acyclic).** On an acyclic parent graph the rollup of a present
    issue is fuel-irrelevant above its descendant count. -/
theorem effStatusAux_stable (s : State) (hac : ParentAcyclic s) (i : IssueId)
    (hi : i ∈ s.presentIssues) (a b : Nat) (ha : descCard s i ≤ a) (hb : descCard s i ≤ b) :
    s.effStatusAux a i = s.effStatusAux b i :=
  effStatusAux_stable_aux s hac (descCard s i) i hi (Nat.le_refl _) a b ha hb

/-- **Epic-rollup correctness (acyclic).** Discharges the rollup residual: on an
    acyclic parent graph, an epic that is not manually cancelled is `Done` iff every
    present child is effectively closed (ADR-0003 §3). -/
theorem effectiveStatus_epic (s : State) (hac : ParentAcyclic s) (i : IssueId)
    (hi : i ∈ s.presentIssues) (hepic : s.isEpic i = true)
    (hcanc : (s.issueData i).statusOf ≠ Status.Cancelled) :
    s.effectiveStatus i
      = (if (s.presentChildren i).all (fun c => s.effClosed c) then Status.Done else Status.Open) := by
  obtain ⟨N, hN⟩ : ∃ N, s.presentIssues.length = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (List.length_pos_of_mem hi))
  refine State.effectiveStatus_epic_of_stable s i N hN hepic hcanc (fun c hc => ?_)
  have hcpres : c ∈ s.presentIssues := presentChildren_subset_present s i hc
  have hMcN : descCard s c ≤ N := descCard_child_le_pred s hac i c hc hi N hN
  show s.effStatusAux N c = s.effectiveStatus c
  unfold State.effectiveStatus
  rw [hN]
  exact effStatusAux_stable s hac c hcpres N (N + 1) hMcN (Nat.le_succ_of_le hMcN)

end Tl.Kernel
