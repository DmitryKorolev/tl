/-
`Tl.Kernel.Reach` — `reachClosure` computes the transitive closure (the
foundation for ADR-0004 thm 6 cycle-correctness and thm 10 why/unblocks).

This is the one place the kernel proofs use Mathlib (ADR-0009 superseding note):
the *completeness* direction — that iterating the one-step closure
`|presentIssues|` times captures every reachable node — is a finite-graph
saturation argument (a monotone, deduplicated, universe-bounded chain stabilizes),
which rests on Mathlib's `Finset` cardinality and `Relation.ReflTransGen`.

Soundness (everything in `reachClosure` is genuinely reachable) needs no Mathlib.
-/
import Tl.Kernel.Ready
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Card

namespace Tl.Kernel

open Tl.Crdt

variable {α : Type _} [DecidableEq α]

/-! ## `dedup` membership and no-duplication -/

theorem dedup_mem {a : α} : (l : List α) → (a ∈ dedup l ↔ a ∈ l)
  | [] => Iff.rfl
  | x :: xs => by
    show a ∈ (if x ∈ dedup xs then dedup xs else x :: dedup xs) ↔ a ∈ x :: xs
    by_cases hx : x ∈ dedup xs
    · rw [if_pos hx, List.mem_cons, dedup_mem xs]
      have hxs : x ∈ xs := (dedup_mem xs).mp hx
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun he => he ▸ hxs) id⟩
    · rw [if_neg hx, List.mem_cons, List.mem_cons, dedup_mem xs]

theorem dedup_nodup : (l : List α) → (dedup l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    show (if x ∈ dedup xs then dedup xs else x :: dedup xs).Nodup
    by_cases hx : x ∈ dedup xs
    · rw [if_pos hx]; exact dedup_nodup xs
    · rw [if_neg hx]; exact List.nodup_cons.mpr ⟨hx, dedup_nodup xs⟩

/-! ## `reachStep` membership, no-dup, inflation -/

theorem mem_reachStep {a : IssueId} {succ : IssueId → List IssueId} {acc : List IssueId} :
    a ∈ State.reachStep succ acc ↔ a ∈ acc ∨ ∃ x ∈ acc, a ∈ succ x := by
  unfold State.reachStep
  rw [dedup_mem, List.mem_append, List.mem_flatMap]

theorem reachStep_nodup (succ : IssueId → List IssueId) (acc : List IssueId) :
    (State.reachStep succ acc).Nodup := dedup_nodup _

theorem subset_reachStep (succ : IssueId → List IssueId) (acc : List IssueId) :
    acc ⊆ State.reachStep succ acc := fun _ ha => mem_reachStep.mpr (Or.inl ha)

/-! ## `reachClosure` unfolding, soundness, monotonicity -/

theorem iterateN_succ' {β : Type _} (f : β → β) : (n : Nat) → (a : β) →
    iterateN f (n + 1) a = f (iterateN f n a)
  | 0, _ => rfl
  | n + 1, a => iterateN_succ' f n (f a)

theorem reachClosure_succ (succ : IssueId → List IssueId) (N : Nat) (seed : List IssueId) :
    State.reachClosure succ (N + 1) seed = State.reachStep succ (State.reachClosure succ N seed) :=
  iterateN_succ' (State.reachStep succ) N seed

/-- The step relation underlying `reachClosure`. -/
abbrev StepRel (succ : IssueId → List IssueId) : IssueId → IssueId → Prop := fun x y => y ∈ succ x

/-- Everything in `reachClosure` is genuinely reachable from the seed (no Mathlib). -/
theorem reachClosure_sound (succ : IssueId → List IssueId) (seed : List IssueId) :
    (N : Nat) → ∀ {a : IssueId}, a ∈ State.reachClosure succ N seed →
      ∃ s ∈ seed, Relation.ReflTransGen (StepRel succ) s a
  | 0, _, ha => ⟨_, ha, .refl⟩
  | N + 1, a, ha => by
    rw [reachClosure_succ, mem_reachStep] at ha
    rcases ha with ha | ⟨x, hx, hxa⟩
    · exact reachClosure_sound succ seed N ha
    · obtain ⟨s, hs, hsx⟩ := reachClosure_sound succ seed N hx
      exact ⟨s, hs, hsx.tail hxa⟩

theorem subset_reachClosure_succ (succ : IssueId → List IssueId) (N : Nat) (seed : List IssueId) :
    State.reachClosure succ N seed ⊆ State.reachClosure succ (N + 1) seed := by
  rw [reachClosure_succ]; exact subset_reachStep succ _

theorem reachClosure_mono (succ : IssueId → List IssueId) (seed : List IssueId) :
    {N M : Nat} → N ≤ M → State.reachClosure succ N seed ⊆ State.reachClosure succ M seed := by
  intro N M h
  induction h with
  | refl => exact fun _ ha => ha
  | step _ ih => exact fun _ ha => subset_reachClosure_succ succ _ seed (ih ha)

/-- A set closed under `succ` and containing the seed contains everything reachable. -/
theorem reachable_subset_closed {succ : IssueId → List IssueId} {F : List IssueId}
    (hC : ∀ x ∈ F, succ x ⊆ F) {seed : List IssueId} (hsF : seed ⊆ F)
    {a : IssueId} (s : IssueId) (hs : s ∈ seed) (hsa : Relation.ReflTransGen (StepRel succ) s a) :
    a ∈ F := by
  induction hsa with
  | refl => exact hsF hs
  | tail _ hbc ih => exact hC _ ih hbc

/-! ## Saturation (Mathlib): the chain stabilizes within the universe -/

/-- `reachClosure` stays within a universe closed under `succ`. -/
theorem reachClosure_subset_universe {succ : IssueId → List IssueId} {U seed : List IssueId}
    (hsU : seed ⊆ U) (hU : ∀ x ∈ U, succ x ⊆ U) :
    (N : Nat) → State.reachClosure succ N seed ⊆ U
  | 0 => hsU
  | N + 1 => by
    rw [reachClosure_succ]
    intro a ha
    rw [mem_reachStep] at ha
    rcases ha with ha | ⟨x, hx, hxa⟩
    · exact reachClosure_subset_universe hsU hU N ha
    · exact hU x (reachClosure_subset_universe hsU hU N hx) hxa

theorem reachClosure_toFinset_mono {succ : IssueId → List IssueId} {seed : List IssueId}
    {N M : Nat} (h : N ≤ M) :
    (State.reachClosure succ N seed).toFinset ⊆ (State.reachClosure succ M seed).toFinset :=
  fun _ ha => List.mem_toFinset.mpr (reachClosure_mono succ seed h (List.mem_toFinset.mp ha))

/-- If the step from `N` is not yet stable, the deduplicated card strictly grows. -/
theorem card_lt_of_not_stable {succ : IssueId → List IssueId} {seed : List IssueId} {N : Nat}
    (h : ¬ State.reachClosure succ (N + 1) seed ⊆ State.reachClosure succ N seed) :
    (State.reachClosure succ N seed).toFinset.card
      < (State.reachClosure succ (N + 1) seed).toFinset.card := by
  rw [List.subset_def] at h; push Not at h
  obtain ⟨a, haN1, haN⟩ := h
  apply Finset.card_lt_card
  refine ⟨reachClosure_toFinset_mono (Nat.le_succ N), fun hsub => ?_⟩
  exact haN (List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr haN1)))

/-- A run of strict growths forces the card to reach the index. -/
theorem le_card_of_strict {succ : IssueId → List IssueId} {seed : List IssueId} :
    (m : Nat) →
    (∀ N < m, (State.reachClosure succ N seed).toFinset.card
      < (State.reachClosure succ (N + 1) seed).toFinset.card) →
    m ≤ (State.reachClosure succ m seed).toFinset.card
  | 0, _ => Nat.zero_le _
  | k + 1, hstrict => by
    have hk := le_card_of_strict k (fun N hN => hstrict N (Nat.lt_succ_of_lt hN))
    exact Nat.lt_of_le_of_lt hk (hstrict k (Nat.lt_succ_self k))

/-- A stable step exists within `|U.toFinset|` iterations (the pigeonhole). -/
theorem exists_stable_step {succ : IssueId → List IssueId} {U seed : List IssueId}
    (hsU : seed ⊆ U) (hU : ∀ x ∈ U, succ x ⊆ U) :
    ∃ N ≤ U.toFinset.card,
      State.reachClosure succ (N + 1) seed ⊆ State.reachClosure succ N seed := by
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ N < U.toFinset.card + 1,
      (State.reachClosure succ N seed).toFinset.card
        < (State.reachClosure succ (N + 1) seed).toFinset.card :=
    fun N hN => card_lt_of_not_stable (hcon N (Nat.lt_succ_iff.mp hN))
  have hle := le_card_of_strict (U.toFinset.card + 1) hstrict
  have hbound : (State.reachClosure succ (U.toFinset.card + 1) seed).toFinset.card
      ≤ U.toFinset.card :=
    Finset.card_le_card (fun a ha =>
      List.mem_toFinset.mpr (reachClosure_subset_universe hsU hU _ (List.mem_toFinset.mp ha)))
  exact absurd (Nat.le_trans hle hbound) (Nat.not_succ_le_self _)

/-- A stable step persists to all later indices. -/
theorem persist_step {succ : IssueId → List IssueId} {seed : List IssueId} {N : Nat}
    (h : State.reachClosure succ (N + 1) seed ⊆ State.reachClosure succ N seed) :
    State.reachClosure succ (N + 2) seed ⊆ State.reachClosure succ (N + 1) seed := by
  intro a ha
  rw [reachClosure_succ, mem_reachStep] at ha
  rcases ha with ha | ⟨x, hx, hxa⟩
  · exact ha
  · rw [reachClosure_succ]; exact mem_reachStep.mpr (Or.inr ⟨x, h hx, hxa⟩)

theorem persist {succ : IssueId → List IssueId} {seed : List IssueId} {N : Nat}
    (h : State.reachClosure succ (N + 1) seed ⊆ State.reachClosure succ N seed) :
    ∀ M, N ≤ M → State.reachClosure succ (M + 1) seed ⊆ State.reachClosure succ M seed := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => exact h
  | succ M _ ih => exact persist_step ih

/-- The closure at `|U|` steps is a fixpoint (closed under `succ`). -/
theorem reachClosure_closed {succ : IssueId → List IssueId} {U seed : List IssueId}
    (hsU : seed ⊆ U) (hU : ∀ x ∈ U, succ x ⊆ U) :
    State.reachClosure succ (U.length + 1) seed ⊆ State.reachClosure succ U.length seed := by
  obtain ⟨N, hN, hstable⟩ := exists_stable_step hsU hU
  exact persist hstable U.length (Nat.le_trans hN (List.toFinset_card_le U))

/-- **Completeness**: every reachable node is in `reachClosure` at `|U|` steps. -/
theorem reachable_mem_reachClosure {succ : IssueId → List IssueId} {U seed : List IssueId}
    (hsU : seed ⊆ U) (hU : ∀ x ∈ U, succ x ⊆ U)
    {a : IssueId} (s : IssueId) (hs : s ∈ seed)
    (hsa : Relation.ReflTransGen (StepRel succ) s a) :
    a ∈ State.reachClosure succ U.length seed := by
  refine reachable_subset_closed (F := State.reachClosure succ U.length seed) ?_ ?_ s hs hsa
  · intro x hx y hy
    apply reachClosure_closed hsU hU
    rw [reachClosure_succ]
    exact mem_reachStep.mpr (Or.inr ⟨x, hx, hy⟩)
  · intro x hx
    exact reachClosure_mono succ seed (Nat.zero_le _) hx

/-- **The transitive-closure characterization** (soundness + completeness). -/
theorem mem_reachClosure_iff {succ : IssueId → List IssueId} {U seed : List IssueId}
    (hsU : seed ⊆ U) (hU : ∀ x ∈ U, succ x ⊆ U) {a : IssueId} :
    a ∈ State.reachClosure succ U.length seed
      ↔ ∃ s ∈ seed, Relation.ReflTransGen (StepRel succ) s a := by
  refine ⟨reachClosure_sound succ seed U.length, ?_⟩
  rintro ⟨s, hs, hsa⟩
  exact reachable_mem_reachClosure hsU hU s hs hsa

end Tl.Kernel
