/-
`Tl.Kernel.Ranking` — the `ready` queue is actually sorted (ADR-0004 thm 4).

`ready` returns `rankSort`-ed present-ready issues. `rankSort_perm` (Theorems.lean)
already gives *determinism* (the output is a permutation of the input, so equal states
give equal queues — what convergence needs). This file proves the queue is genuinely
*ordered* by the ranking comparator `readyLe`: `readyLe` is a total order (reflexive,
total, transitive — lexicographic on priority ↑ / weight ↓ / createdAt ↑ / the unique
`id`), and `mergeSort` produces a `Pairwise`-sorted list. Mathlib-free: the order
facts ride on `Nat` and `Tl.Crdt.TotalOrd`, the sortedness on core `List.Pairwise`.
-/
import Tl.Kernel.Theorems

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-- The ranking comparator as a lexicographic disjunction: priority ↑, then weight ↓,
    then createdAt ↑, then the `id` total order. -/
theorem readyLe_eq_true_iff (s : State) (a b : IssueId) :
    s.readyLe a b = true ↔
      (s.issueData a).priorityOf.val < (s.issueData b).priorityOf.val
      ∨ ((s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val ∧ s.weight b < s.weight a)
      ∨ ((s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val ∧ s.weight a = s.weight b
          ∧ s.createdAtOf a < s.createdAtOf b)
      ∨ ((s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val ∧ s.weight a = s.weight b
          ∧ s.createdAtOf a = s.createdAtOf b ∧ TotalOrd.le a b) := by
  unfold State.readyLe
  by_cases hp : (s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val
  · rw [if_neg (fun hne => hne hp)]
    by_cases hw : s.weight a = s.weight b
    · rw [if_neg (fun hne => hne hw)]
      by_cases hc : s.createdAtOf a = s.createdAtOf b
      · rw [if_neg (fun hne => hne hc), decide_eq_true_iff]
        exact ⟨fun hle => Or.inr (Or.inr (Or.inr ⟨hp, hw, hc, hle⟩)),
          fun h => by rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩
                      · exact absurd hp (Nat.ne_of_lt h)
                      · exact absurd hw (Ne.symm (Nat.ne_of_lt h))
                      · exact absurd hc (Nat.ne_of_lt h)
                      · exact h⟩
      · rw [if_pos hc, decide_eq_true_iff]
        exact ⟨fun hlt => Or.inr (Or.inr (Or.inl ⟨hp, hw, hlt⟩)),
          fun h => by rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h, _⟩
                      · exact absurd hp (Nat.ne_of_lt h)
                      · exact absurd hw (Ne.symm (Nat.ne_of_lt h))
                      · exact h
                      · exact absurd h hc⟩
    · rw [if_pos hw, decide_eq_true_iff]
      exact ⟨fun hlt => Or.inr (Or.inl ⟨hp, hlt⟩),
        fun h => by rcases h with h | ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _, _⟩
                    · exact absurd hp (Nat.ne_of_lt h)
                    · exact h
                    · exact absurd h hw
                    · exact absurd h hw⟩
  · rw [if_pos hp, decide_eq_true_iff]
    exact ⟨fun hlt => Or.inl hlt,
      fun h => by rcases h with h | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _, _⟩
                  · exact h
                  · exact absurd h hp
                  · exact absurd h hp
                  · exact absurd h hp⟩

/-! ## `readyLe` is a total order -/

/-- `readyLe` is total (the `id` tie-break makes every pair comparable). -/
theorem readyLe_total (s : State) (a b : IssueId) :
    s.readyLe a b = true ∨ s.readyLe b a = true := by
  rw [readyLe_eq_true_iff, readyLe_eq_true_iff]
  rcases Nat.lt_trichotomy (s.issueData a).priorityOf.val (s.issueData b).priorityOf.val with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy (s.weight a) (s.weight b) with hw | hw | hw
    · exact Or.inr (Or.inr (Or.inl ⟨h.symm, hw⟩))
    · rcases Nat.lt_trichotomy (s.createdAtOf a) (s.createdAtOf b) with hc | hc | hc
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h, hw, hc⟩)))
      · rcases TotalOrd.le_total a b with hle | hle
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨h, hw, hc, hle⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.symm, hw.symm, hc.symm, hle⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.symm, hw.symm, hc⟩)))
    · exact Or.inl (Or.inr (Or.inl ⟨h, hw⟩))
  · exact Or.inr (Or.inl h)

/-! ### Per-level extractors (read off the lexicographic decision) -/

theorem readyLe_prio_le (s : State) (a b : IssueId) (h : s.readyLe a b = true) :
    (s.issueData a).priorityOf.val ≤ (s.issueData b).priorityOf.val := by
  rw [readyLe_eq_true_iff] at h
  rcases h with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact Nat.le_of_lt h
  all_goals exact Nat.le_of_eq h

theorem readyLe_weight_le (s : State) (a b : IssueId) (h : s.readyLe a b = true)
    (hp : (s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val) :
    s.weight b ≤ s.weight a := by
  rw [readyLe_eq_true_iff] at h
  rcases h with h | ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _, _⟩
  · exact absurd hp (Nat.ne_of_lt h)
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h.symm
  · exact Nat.le_of_eq h.symm

theorem readyLe_created_le (s : State) (a b : IssueId) (h : s.readyLe a b = true)
    (hp : (s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val)
    (hw : s.weight a = s.weight b) : s.createdAtOf a ≤ s.createdAtOf b := by
  rw [readyLe_eq_true_iff] at h
  rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h, _⟩
  · exact absurd hp (Nat.ne_of_lt h)
  · exact absurd hw (Ne.symm (Nat.ne_of_lt h))
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h

theorem readyLe_id_le (s : State) (a b : IssueId) (h : s.readyLe a b = true)
    (hp : (s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val)
    (hw : s.weight a = s.weight b) (hc : s.createdAtOf a = s.createdAtOf b) :
    TotalOrd.le a b := by
  rw [readyLe_eq_true_iff] at h
  rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩
  · exact absurd hp (Nat.ne_of_lt h)
  · exact absurd hw (Ne.symm (Nat.ne_of_lt h))
  · exact absurd hc (Nat.ne_of_lt h)
  · exact h

/-- `readyLe` is transitive — the lexicographic cascade composes level by level. -/
theorem readyLe_trans (s : State) {a b c : IssueId}
    (hab : s.readyLe a b = true) (hbc : s.readyLe b c = true) : s.readyLe a c = true := by
  rw [readyLe_eq_true_iff]
  have pab := readyLe_prio_le s a b hab
  have pbc := readyLe_prio_le s b c hbc
  rcases Nat.lt_or_ge (s.issueData a).priorityOf.val (s.issueData c).priorityOf.val with hac | hac
  · exact Or.inl hac
  · have hpac : (s.issueData a).priorityOf.val = (s.issueData c).priorityOf.val :=
      Nat.le_antisymm (Nat.le_trans pab pbc) hac
    have hpab : (s.issueData a).priorityOf.val = (s.issueData b).priorityOf.val :=
      Nat.le_antisymm pab (Nat.le_trans pbc (Nat.le_of_eq hpac.symm))
    have hpbc : (s.issueData b).priorityOf.val = (s.issueData c).priorityOf.val :=
      Nat.le_antisymm pbc (Nat.le_trans (Nat.le_of_eq hpac.symm) pab)
    have wab := readyLe_weight_le s a b hab hpab
    have wbc := readyLe_weight_le s b c hbc hpbc
    rcases Nat.lt_or_ge (s.weight c) (s.weight a) with hwac | hwac
    · exact Or.inr (Or.inl ⟨hpac, hwac⟩)
    · have hwca : s.weight a = s.weight c := Nat.le_antisymm hwac (Nat.le_trans wbc wab)
      have hwab : s.weight a = s.weight b :=
        Nat.le_antisymm (Nat.le_trans (Nat.le_of_eq hwca) wbc) wab
      have hwbc : s.weight b = s.weight c :=
        Nat.le_antisymm (Nat.le_trans wab (Nat.le_of_eq hwca)) wbc
      have cab := readyLe_created_le s a b hab hpab hwab
      have cbc := readyLe_created_le s b c hbc hpbc hwbc
      rcases Nat.lt_or_ge (s.createdAtOf a) (s.createdAtOf c) with hcac | hcac
      · exact Or.inr (Or.inr (Or.inl ⟨hpac, hwca, hcac⟩))
      · have hcca : s.createdAtOf a = s.createdAtOf c :=
          Nat.le_antisymm (Nat.le_trans cab cbc) hcac
        have hcab : s.createdAtOf a = s.createdAtOf b :=
          Nat.le_antisymm cab (Nat.le_trans cbc (Nat.le_of_eq hcca.symm))
        have hcbc : s.createdAtOf b = s.createdAtOf c :=
          Nat.le_antisymm cbc (Nat.le_trans (Nat.le_of_eq hcca.symm) cab)
        exact Or.inr (Or.inr (Or.inr ⟨hpac, hwca, hcca,
          TotalOrd.le_trans (readyLe_id_le s a b hab hpab hwab hcab)
            (readyLe_id_le s b c hbc hpbc hwbc hcbc)⟩))

/-! ## The queue is sorted by `readyLe` -/

theorem readyLe_total_bool (s : State) (a b : IssueId) :
    (s.readyLe a b || s.readyLe b a) = true := by
  rcases readyLe_total s a b with h | h
  · rw [h]
    rfl
  · rw [h, Bool.or_true]

/-- `rankSort` produces a `readyLe`-sorted list. -/
theorem rankSort_sorted (s : State) :
    (l : List IssueId) → List.Pairwise (fun a b => s.readyLe a b = true) (s.rankSort l)
  | l => by
    unfold State.rankSort
    exact List.pairwise_mergeSort
      (le := fun a b => s.readyLe a b)
      (fun a b c => readyLe_trans s)
      (fun a b => readyLe_total_bool s a b)
      l

/-- **The `ready` queue is sorted by the ranking order** (ADR-0004 thm 4): every issue
    ranks `readyLe`-before every later one. Closes the ranking-soundness residual. -/
theorem ready_sorted (s : State) (now : Instant) :
    List.Pairwise (fun a b => s.readyLe a b = true) (s.ready now) := by
  unfold State.ready
  exact rankSort_sorted s _

end State

end Tl.Kernel
