/-
`Tl.Kernel.RollupSat` — fuel saturation and the unconditional rollup
recurrence (ADR-0003 §3 amendment). Spec-side only: nothing here is about
speed — it characterizes the *fuel form* (`Rollup.lean`), and is what the
fast implementation's refinement bridge (`RollupFast.lean`) folds against.

`effectiveStatus` runs the fuel descent at `N = |presentIssues|`. This file
proves the fuel is *saturated* there, so the rollup satisfies its one-step
recurrence with NO acyclicity hypothesis:

  `effectiveStatus i = Cancelled` on manual cancel, the stored status with no
  present children, else `Done` iff every present child is effectively closed.

A cycle has no descent measure, so the argument is a finite ascending-chain
one instead: closed-ness at fuel `f` (`closedAt`) only ever switches false →
true as `f` grows (`closedAt_le_succ`), a fuel where no present issue
switches freezes every later fuel (`closedAt_freeze_present` /
`closedAt_frozen_upto`), and on `M + 1` present issues an unfrozen chain runs
out of room by fuel `M` (`exists_closedSet_freeze` — the cardinality
pigeonhole, in the Mathlib-permitted zone like `RollupAcyclic`, ADR-0009).
On acyclic graphs the recurrence specializes to
`RollupAcyclic.effectiveStatus_epic`.
-/
import Tl.Kernel.RollupSpec
import Tl.Kernel.Reach

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-- Closed-ness of the rollup at fuel `f` — the Bool vector whose ascending
    chain drives the saturation argument. -/
def closedAt (s : State) (f : Nat) (i : IssueId) : Bool :=
  Status.closed (s.effStatusAux f i)

/-- `effClosed` is `closedAt` at the working fuel. -/
theorem effClosed_eq_closedAt (s : State) (c : IssueId) :
    s.effClosed c = closedAt s s.presentIssues.length c := rfl

private theorem boolEq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a with
  | true => exact (h.mp rfl).symm
  | false =>
    cases b with
    | true => exact absurd (h.mpr rfl) Bool.false_ne_true
    | false => rfl

/-- One-step definitional unfolding at fuel 0 (a named equation so rewrites
    stay targeted — a bare `unfold` would also mangle inner occurrences). -/
private theorem effStatusAux_zero_def (s : State) (i : IssueId) :
    s.effStatusAux 0 i =
      if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
      else if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
      else Status.Open := rfl

/-- One-step definitional unfolding at fuel `f + 1`. -/
private theorem effStatusAux_succ_def (s : State) (f : Nat) (i : IssueId) :
    s.effStatusAux (f + 1) i =
      if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
      else if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
      else if (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux f c))
           then Status.Done else Status.Open := rfl

/-- What is closed at fuel 0: a manual cancel, or a closed stored status with
    no present children (an epic at exhaustion is `Open`). -/
theorem closedAt_zero_iff (s : State) (i : IssueId) :
    closedAt s 0 i = true ↔
      (s.issueData i).statusOf = Status.Cancelled ∨
      ((s.presentChildren i).isEmpty = true ∧
        Status.closed (s.issueData i).statusOf = true) := by
  show Status.closed (s.effStatusAux 0 i) = true ↔ _
  rw [effStatusAux_zero_def]
  by_cases hc : (s.issueData i).statusOf = Status.Cancelled
  · rw [if_pos hc]
    exact ⟨fun _ => Or.inl hc, fun _ => rfl⟩
  · rw [if_neg hc]
    cases hk : (s.presentChildren i).isEmpty with
    | true =>
      rw [if_pos rfl]
      constructor
      · intro hcl
        exact Or.inr ⟨rfl, hcl⟩
      · rintro (hcanc | ⟨_, hcl⟩)
        · exact absurd hcanc hc
        · exact hcl
    | false =>
      rw [if_neg Bool.false_ne_true]
      constructor
      · intro h
        exact absurd h Bool.false_ne_true
      · rintro (hcanc | ⟨hk', _⟩)
        · exact absurd hcanc hc
        · exact absurd hk' Bool.false_ne_true

/-- What is closed at fuel `f + 1`: a cancel, a closed childless stored
    status, or an epic whose every present child is closed at fuel `f`. -/
theorem closedAt_succ_iff (s : State) (f : Nat) (i : IssueId) :
    closedAt s (f + 1) i = true ↔
      (s.issueData i).statusOf = Status.Cancelled ∨
      ((s.presentChildren i).isEmpty = true ∧
        Status.closed (s.issueData i).statusOf = true) ∨
      ((s.presentChildren i).isEmpty = false ∧
        ∀ c ∈ s.presentChildren i, closedAt s f c = true) := by
  show Status.closed (s.effStatusAux (f + 1) i) = true ↔ _
  rw [effStatusAux_succ_def]
  by_cases hc : (s.issueData i).statusOf = Status.Cancelled
  · rw [if_pos hc]
    exact ⟨fun _ => Or.inl hc, fun _ => rfl⟩
  · rw [if_neg hc]
    cases hk : (s.presentChildren i).isEmpty with
    | true =>
      rw [if_pos rfl]
      constructor
      · intro hcl
        exact Or.inr (Or.inl ⟨rfl, hcl⟩)
      · rintro (hcanc | ⟨_, hcl⟩ | ⟨hk', _⟩)
        · exact absurd hcanc hc
        · exact hcl
        · exact absurd hk'.symm (by intro hh; exact Bool.noConfusion hh)
    | false =>
      rw [if_neg Bool.false_ne_true]
      cases hall : (s.presentChildren i).all
          (fun c => Status.closed (s.effStatusAux f c)) with
      | true =>
        rw [if_pos rfl]
        constructor
        · intro _
          exact Or.inr (Or.inr ⟨rfl, fun c hcm => List.all_eq_true.mp hall c hcm⟩)
        · intro _
          rfl
      | false =>
        rw [if_neg Bool.false_ne_true]
        constructor
        · intro h
          exact absurd h Bool.false_ne_true
        · rintro (hcanc | ⟨hk', _⟩ | ⟨_, hkids⟩)
          · exact absurd hcanc hc
          · exact absurd hk' Bool.false_ne_true
          · have hcontra : (s.presentChildren i).all
                (fun c => Status.closed (s.effStatusAux f c)) = true :=
              List.all_eq_true.mpr (fun c hcm => hkids c hcm)
            rw [hall] at hcontra
            exact absurd hcontra Bool.false_ne_true

/-- Closed-ness only ever switches false → true as the fuel grows. -/
theorem closedAt_le_succ (s : State) :
    (f : Nat) → ∀ i, closedAt s f i = true → closedAt s (f + 1) i = true
  | 0, i, h => by
    rcases (closedAt_zero_iff s i).mp h with hc | hkcl
    · exact (closedAt_succ_iff s 0 i).mpr (Or.inl hc)
    · exact (closedAt_succ_iff s 0 i).mpr (Or.inr (Or.inl hkcl))
  | f + 1, i, h => by
    rcases (closedAt_succ_iff s f i).mp h with hc | hkcl | ⟨hk, hall⟩
    · exact (closedAt_succ_iff s (f + 1) i).mpr (Or.inl hc)
    · exact (closedAt_succ_iff s (f + 1) i).mpr (Or.inr (Or.inl hkcl))
    · exact (closedAt_succ_iff s (f + 1) i).mpr (Or.inr (Or.inr ⟨hk,
        fun c hcm => closedAt_le_succ s f c (hall c hcm)⟩))

/-- A fuel where no *present* issue switches freezes the next fuel for every
    id: levels `f+1`/`f+2` read only present children at `f`/`f+1`. -/
theorem closedAt_freeze_present (s : State) (f : Nat)
    (h : ∀ j ∈ s.presentIssues, closedAt s f j = closedAt s (f + 1) j) :
    ∀ i, closedAt s (f + 1) i = closedAt s (f + 2) i := by
  intro i
  apply boolEq_of_iff
  rw [closedAt_succ_iff, closedAt_succ_iff]
  constructor
  · rintro (hc | hkcl | ⟨hk, hkids⟩)
    · exact Or.inl hc
    · exact Or.inr (Or.inl hkcl)
    · refine Or.inr (Or.inr ⟨hk, fun c hcm => ?_⟩)
      rw [← h c (presentChildren_subset_present s i hcm)]
      exact hkids c hcm
  · rintro (hc | hkcl | ⟨hk, hkids⟩)
    · exact Or.inl hc
    · exact Or.inr (Or.inl hkcl)
    · refine Or.inr (Or.inr ⟨hk, fun c hcm => ?_⟩)
      rw [h c (presentChildren_subset_present s i hcm)]
      exact hkids c hcm

/-- A present-issue freeze at `f` persists to every later fuel. -/
theorem closedAt_frozen_upto (s : State) (f : Nat)
    (h : ∀ j ∈ s.presentIssues, closedAt s f j = closedAt s (f + 1) j) :
    (g : Nat) → f ≤ g → ∀ j ∈ s.presentIssues, closedAt s g j = closedAt s (g + 1) j
  | 0, hle, j, hj => by
    have hf : f = 0 := Nat.le_zero.mp hle
    exact hf ▸ h j hj
  | g + 1, hle, j, hj => by
    by_cases hfg : f = g + 1
    · exact hfg ▸ h j hj
    · have hle' : f ≤ g := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hle hfg)
      exact closedAt_freeze_present s g
        (fun k hk => closedAt_frozen_upto s f h g hle' k hk) j

/-! ## The cardinality pigeonhole (Mathlib zone, ADR-0009) -/

/-- The present issues closed at fuel `f` — the ascending chain's links. -/
def closedSet (s : State) (f : Nat) : Finset IssueId :=
  s.presentIssues.toFinset.filter (fun j => closedAt s f j = true)

theorem closedSet_subset_succ (s : State) (f : Nat) :
    closedSet s f ⊆ closedSet s (f + 1) := by
  intro j hj
  rw [closedSet, Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, closedAt_le_succ s f j hj.2⟩

theorem present_eq_of_closedSet_eq (s : State) (f : Nat)
    (h : closedSet s f = closedSet s (f + 1)) :
    ∀ j ∈ s.presentIssues, closedAt s f j = closedAt s (f + 1) j := by
  intro j hj
  apply boolEq_of_iff
  constructor
  · intro hcl
    have hmem : j ∈ closedSet s f := by
      rw [closedSet, Finset.mem_filter]
      exact ⟨List.mem_toFinset.mpr hj, hcl⟩
    rw [h, closedSet, Finset.mem_filter] at hmem
    exact hmem.2
  · intro hcl
    have hmem : j ∈ closedSet s (f + 1) := by
      rw [closedSet, Finset.mem_filter]
      exact ⟨List.mem_toFinset.mpr hj, hcl⟩
    rw [← h, closedSet, Finset.mem_filter] at hmem
    exact hmem.2

/-- Nothing is closed at fuel 1 if nothing is closed at fuel 0 (an epic needs
    a closed child; the other arms are fuel-independent) — an empty chain is
    born frozen. -/
theorem closedSet_one_eq_of_zero_empty (s : State)
    (h : closedSet s 0 = ∅) : closedSet s 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  rw [closedSet, Finset.mem_filter] at hj
  obtain ⟨hjp, hcl⟩ := hj
  rcases (closedAt_succ_iff s 0 j).mp hcl with hc | hkcl | ⟨hk, hkids⟩
  · have hmem : j ∈ closedSet s 0 := by
      rw [closedSet, Finset.mem_filter]
      exact ⟨hjp, (closedAt_zero_iff s j).mpr (Or.inl hc)⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty j)
  · have hmem : j ∈ closedSet s 0 := by
      rw [closedSet, Finset.mem_filter]
      exact ⟨hjp, (closedAt_zero_iff s j).mpr (Or.inr hkcl)⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty j)
  · obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil (s.presentChildren j) (by
      intro hnil
      rw [hnil] at hk
      exact Bool.noConfusion hk)
    have hcp : c ∈ s.presentIssues := presentChildren_subset_present s j hcm
    have hmem : c ∈ closedSet s 0 := by
      rw [closedSet, Finset.mem_filter]
      exact ⟨List.mem_toFinset.mpr hcp, hkids c hcm⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty c)

theorem presentIssues_nodup (s : State) : s.presentIssues.Nodup :=
  List.Nodup.filter _ (AMap.keys_nodup s.issues.adds)

/-- **The pigeonhole.** With `M + 1` present issues, some fuel `f ≤ M` is
    frozen: an unfrozen ascending chain of subsets of the present set starts
    nonempty (`closedSet_one_eq_of_zero_empty`) and gains a member per fuel,
    so it fills the present set by fuel `M` and freezes there. -/
theorem exists_closedSet_freeze (s : State) (M : Nat)
    (hN : s.presentIssues.length = M + 1) :
    ∃ f, f ≤ M ∧ closedSet s f = closedSet s (f + 1) := by
  by_contra hnone
  rw [not_exists] at hnone
  have hne : ∀ f, f ≤ M → closedSet s f ≠ closedSet s (f + 1) := by
    intro f hf heq
    exact hnone f ⟨hf, heq⟩
  have hssub : ∀ f, f ≤ M → closedSet s f ⊂ closedSet s (f + 1) := fun f hf =>
    HasSubset.Subset.ssubset_of_ne (closedSet_subset_succ s f) (hne f hf)
  have h0 : (closedSet s 0).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (closedSet s 0) with hemp | hne0
    · exact absurd (by rw [hemp, closedSet_one_eq_of_zero_empty s hemp])
        (hne 0 (Nat.zero_le M))
    · exact hne0
  have hgrow : ∀ f, f ≤ M → f + 1 ≤ (closedSet s f).card := by
    intro f
    induction f with
    | zero => exact fun _ => Finset.card_pos.mpr h0
    | succ g ih =>
      intro hle
      have hg : g ≤ M := Nat.le_of_succ_le hle
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih hg) (Finset.card_lt_card (hssub g hg)))
  have hcardpres : s.presentIssues.toFinset.card = M + 1 := by
    rw [List.toFinset_card_of_nodup (presentIssues_nodup s), hN]
  have hfull : closedSet s M = s.presentIssues.toFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [hcardpres]
    exact hgrow M (Nat.le_refl M)
  have hsq : closedSet s (M + 1) = closedSet s M := by
    apply Finset.Subset.antisymm
    · rw [hfull]
      exact Finset.filter_subset _ _
    · exact closedSet_subset_succ s M
  exact hne M (Nat.le_refl M) hsq.symm

/-- **Saturation.** Present closed-ness is stable between the working fuel
    and its predecessor. -/
theorem closedAt_present_stable (s : State) (M : Nat)
    (hN : s.presentIssues.length = M + 1) :
    ∀ j ∈ s.presentIssues, closedAt s M j = closedAt s (M + 1) j := by
  obtain ⟨f, hfM, hfreeze⟩ := exists_closedSet_freeze s M hN
  exact closedAt_frozen_upto s f (present_eq_of_closedSet_eq s f hfreeze) M hfM

/-- **The recurrence, unconditional (ADR-0003 §3 amendment).** Manual cancel,
    else the stored status with no present children, else `Done` iff every
    present child is effectively closed — with no acyclicity hypothesis: the
    fuel is saturated, so one more descent step changes nothing. -/
theorem effectiveStatus_recurrence (s : State) (i : IssueId) :
    s.effectiveStatus i =
      if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
      else if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
      else if (s.presentChildren i).all (fun c => s.effClosed c) then Status.Done
      else Status.Open := by
  by_cases hc : (s.issueData i).statusOf = Status.Cancelled
  · rw [if_pos hc]
    exact effectiveStatus_cancelled s i hc
  · rw [if_neg hc]
    cases hk : (s.presentChildren i).isEmpty with
    | true =>
      rw [if_pos rfl]
      exact effectiveStatus_nonEpic s i (by
        unfold State.isEpic
        rw [hk]
        rfl)
    | false =>
      rw [if_neg Bool.false_ne_true]
      obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil (s.presentChildren i) (by
        intro hnil
        rw [hnil] at hk
        exact Bool.noConfusion hk)
      obtain ⟨M, hN⟩ : ∃ M, s.presentIssues.length = M + 1 :=
        Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp
          (List.length_pos_of_mem (presentChildren_subset_present s i hc0)))
      have hall : (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux M c))
                = (s.presentChildren i).all (fun c => s.effClosed c) := by
        apply all_congr
        intro c hcm
        show closedAt s M c = s.effClosed c
        rw [effClosed_eq_closedAt, hN]
        exact closedAt_present_stable s M hN c (presentChildren_subset_present s i hcm)
      show s.effStatusAux s.presentIssues.length i = _
      rw [hN, effStatusAux_succ_def, if_neg hc, hk, if_neg Bool.false_ne_true, hall]

end State

end Tl.Kernel
