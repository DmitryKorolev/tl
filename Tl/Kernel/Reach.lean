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
import Tl.Kernel.Cycles
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
    show a ∈ x :: (dedup xs).filter (fun y => decide (y ≠ x)) ↔ a ∈ x :: xs
    rw [List.mem_cons, List.mem_filter, dedup_mem xs, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hax : a = x
        · exact Or.inl hax
        · exact Or.inr ⟨h, hax⟩

theorem dedup_nodup : (l : List α) → (dedup l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    show (x :: (dedup xs).filter (fun y => decide (y ≠ x))).Nodup
    rw [List.nodup_cons]
    refine ⟨?_, (dedup_nodup xs).filter _⟩
    rw [List.mem_filter]
    rintro ⟨_, h⟩
    rw [decide_eq_true_eq] at h
    exact h rfl

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

/-! ## Thm 10 — `why` correctness -/

/-- Live blockers are present issues. -/
theorem liveBlockersSucc_subset_present (s : State) (x : IssueId) :
    s.liveBlockersSucc x ⊆ s.presentIssues := by
  intro b hb
  unfold State.liveBlockersSucc at hb
  rw [List.mem_filter, Bool.and_eq_true] at hb
  exact (OrSet.mem_presentElements s.issues b).mpr (of_decide_eq_true hb.2.1)

/-- **Thm 10** (`why` correctness): `j ∈ why s i` iff `j` is reachable from a direct
    live blocker of `i` through live blockers — i.e. `j` is a transitive *unclosed*
    `blocks`-blocker of `i` (ADR-0004 thm 10). Total on cyclic/dangling graphs. -/
theorem mem_why_iff (s : State) (i j : IssueId) :
    j ∈ s.why i ↔
      ∃ b ∈ s.liveBlockersSucc i, Relation.ReflTransGen (StepRel s.liveBlockersSucc) b j :=
  mem_reachClosure_iff (liveBlockersSucc_subset_present s i)
    (fun x _ => liveBlockersSucc_subset_present s x)

/-! ## Thm 6 — cycle-detection correctness -/

/-- A node is flagged on a cycle iff one of its successors reaches it back —
    exactly "on a cycle" — whenever `succ` stays within `presentIssues` (so the
    diagnostic's fuel is sufficient). -/
theorem onCycle_iff {s : State} {succ : IssueId → List IssueId}
    (hpres : ∀ x, succ x ⊆ s.presentIssues) (v : IssueId) :
    s.onCycle succ v = true ↔ ∃ b ∈ succ v, Relation.ReflTransGen (StepRel succ) b v := by
  unfold State.onCycle
  rw [decide_eq_true_iff]
  exact mem_reachClosure_iff (hpres v) (fun x _ => hpres x)

theorem kindSucc_subset_present (s : State) (k : EdgeKind) (x : IssueId) :
    s.kindSucc k x ⊆ s.presentIssues := by
  intro j hj
  unfold State.kindSucc at hj
  rw [List.mem_filter] at hj
  exact (OrSet.mem_presentElements s.issues j).mpr (of_decide_eq_true hj.2)

theorem presentChildren_subset_present (s : State) (x : IssueId) :
    s.presentChildren x ⊆ s.presentIssues := by
  intro c hc
  unfold State.presentChildren at hc
  rw [List.mem_filter] at hc
  exact (OrSet.mem_presentElements s.issues c).mpr (of_decide_eq_true hc.2)

theorem liveChildrenSucc_subset_present (s : State) (x : IssueId) :
    s.liveChildrenSucc x ⊆ s.presentIssues := by
  intro c hc
  unfold State.liveChildrenSucc at hc
  rw [List.mem_filter] at hc
  exact presentChildren_subset_present s x hc.1

theorem precSucc_subset_present (s : State) (x : IssueId) :
    s.precSucc x ⊆ s.presentIssues := by
  intro b hb
  unfold State.precSucc at hb
  rw [List.mem_append] at hb
  rcases hb with hb | hb
  · exact liveBlockersSucc_subset_present s x hb
  · split at hb
    · exact liveChildrenSucc_subset_present s x hb
    · exact nomatch hb

/-- **Thm 6** (structural cycle detection): a node is on a kind-`k` cycle iff a
    kind-`k` successor reaches it back (ADR-0004 thm 6). Total on arbitrary graphs. -/
theorem onCycle_kindSucc_iff (s : State) (k : EdgeKind) (v : IssueId) :
    s.onCycle (s.kindSucc k) v = true ↔
      ∃ b ∈ s.kindSucc k v, Relation.ReflTransGen (StepRel (s.kindSucc k)) b v :=
  onCycle_iff (kindSucc_subset_present s k) v

/-- **Thm 5/6** (readiness-deadlock detection): a node is on a `≺`-cycle iff a `≺`
    successor (a live blocker, or — for an epic — a live child) reaches it back. So
    a stuck live working set is detected (ADR-0004 thm 5/6). -/
theorem onCycle_precSucc_iff (s : State) (v : IssueId) :
    s.onCycle s.precSucc v = true ↔
      ∃ b ∈ s.precSucc v, Relation.ReflTransGen (StepRel s.precSucc) b v :=
  onCycle_iff (precSucc_subset_present s) v

/-! ## Thm 5 — honest liveness (the stated direction) -/

/-- No live blocker ⇒ every blocker is discharged. -/
theorem all_discharged_of_liveBlockers_nil (s : State) (i : IssueId)
    (h : s.liveBlockersSucc i = []) : (s.blockersOf i).all (s.blockerDischarged ·) = true := by
  unfold State.liveBlockersSucc at h
  rw [List.all_eq_true]
  intro b hb
  have hp : (decide (s.hasIssue b) && !s.effClosed b) = false := by
    cases hpred : (decide (s.hasIssue b) && !s.effClosed b) with
    | false => rfl
    | true =>
      exfalso
      have hmem : b ∈ (s.blockersOf i).filter (fun b => decide (s.hasIssue b) && !s.effClosed b) :=
        List.mem_filter.mpr ⟨hb, hpred⟩
      rw [h] at hmem; exact nomatch hmem
  have key : s.blockerDischarged b = !(decide (s.hasIssue b) && !s.effClosed b) := by
    unfold State.blockerDischarged; rw [Bool.not_and, Bool.not_not]
  rw [key, hp]; rfl

/-- **Thm 5** (honest liveness, the stated direction): an `open`, non-epic,
    non-deferred, materialized issue with no `≺`-predecessor is ready (ADR-0004
    thm 5). For a non-epic, `≺`-predecessors are exactly its live `blocks`-blockers,
    so "no `≺`-predecessor" is "every blocker discharged" — hence ready. The
    contrapositive — a stuck live set forces a `≺`-cycle — is the `precCycles`
    diagnostic (`onCycle_precSucc_iff`). -/
theorem liveness (s : State) (now : Instant) (i : IssueId)
    (hopen : (s.issueData i).statusOf = Status.Open) (hepic : s.isEpic i = false)
    (hdefer : State.deferOk (s.issueData i) now = true) (hpres : s.hasIssue i)
    (hnopred : s.precSucc i = []) : s.isReady now i = true := by
  have hlb : s.liveBlockersSucc i = [] := by
    unfold State.precSucc at hnopred
    cases hlbc : s.liveBlockersSucc i with
    | nil => rfl
    | cons a as => rw [hlbc] at hnopred; exact nomatch hnopred
  unfold State.isReady
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨decide_eq_true_iff.mpr hpres, decide_eq_true_iff.mpr hopen⟩, ?_⟩, hdefer⟩,
    all_discharged_of_liveBlockers_nil s i hlb⟩
  rw [hepic]; rfl

/-! ## Thm 5 — deadlock existence (the contrapositive)

A *stuck* live set — a nonempty node set in which every member waits on a member
(has a successor inside it) — must contain a cycle. So an empty `ready` over a
nonempty live working set is always *diagnosed* by `precCycles`. Pigeonhole: a
chosen-successor function iterated past the set's size repeats a node. -/

theorem exists_onCycle_of_all_succ {s : State} {succ : IssueId → List IssueId}
    (hpres : ∀ x, succ x ⊆ s.presentIssues) {S : List IssueId}
    (hsucc : ∀ x ∈ S, ∃ y ∈ S, y ∈ succ x) {v0 : IssueId} (hv0 : v0 ∈ S) :
    ∃ v ∈ S, s.onCycle succ v = true := by
  classical
  let f : IssueId → IssueId := fun x => if h : ∃ y, y ∈ S ∧ y ∈ succ x then h.choose else x
  have hfS : ∀ x ∈ S, f x ∈ S := fun x hx => by
    show (if h : ∃ y, y ∈ S ∧ y ∈ succ x then h.choose else x) ∈ S
    rw [dite_eq_left (hsucc x hx)]; exact (hsucc x hx).choose_spec.1
  have hfsucc : ∀ x ∈ S, f x ∈ succ x := fun x hx => by
    show (if h : ∃ y, y ∈ S ∧ y ∈ succ x then h.choose else x) ∈ succ x
    rw [dite_eq_left (hsucc x hx)]; exact (hsucc x hx).choose_spec.2
  have horbit : ∀ k, f^[k] v0 ∈ S := by
    intro k
    induction k with
    | zero => exact hv0
    | succ k ih => rw [Function.iterate_succ_apply']; exact hfS _ ih
  have hreach : ∀ a m, Relation.ReflTransGen (StepRel succ) (f^[a] v0) (f^[a + m] v0) := by
    intro a m
    induction m with
    | zero => exact .refl
    | succ m ih =>
      have hstep : f^[a + m + 1] v0 ∈ succ (f^[a + m] v0) := by
        rw [Function.iterate_succ_apply']; exact hfsucc _ (horbit (a + m))
      exact ih.tail hstep
  have hcard : (S.toFinset).card < (Finset.range (S.length + 1)).card := by
    rw [Finset.card_range]
    exact Nat.lt_succ_of_le (List.toFinset_card_le S)
  obtain ⟨x, _, y, _, hxy, hgxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun k : Nat => f^[k] v0)
    (fun k _ => List.mem_toFinset.mpr (horbit k))
  obtain ⟨a, b, hab, heq⟩ : ∃ a b, a < b ∧ f^[a] v0 = f^[b] v0 := by
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, y, h, hgxy⟩
    · exact ⟨y, x, lt_of_le_of_ne h (Ne.symm hxy), hgxy.symm⟩
  refine ⟨f^[a] v0, horbit a, ?_⟩
  rw [onCycle_iff hpres]
  refine ⟨f^[a + 1] v0, ?_, ?_⟩
  · rw [Function.iterate_succ_apply']; exact hfsucc _ (horbit a)
  · have hreach' := hreach (a + 1) (b - (a + 1))
    rw [Nat.add_sub_cancel' hab] at hreach'
    exact heq.symm ▸ hreach'

/-- **Thm 5** (deadlock existence): a stuck live working set `S` — every member
    has a `≺`-successor in `S` — contains a `≺`-cycle, so it is diagnosed by
    `precCycles` (ADR-0004 thm 5). The honest converse of `liveness`. -/
theorem deadlock_exists (s : State) {S : List IssueId}
    (hstuck : ∀ x ∈ S, ∃ y ∈ S, y ∈ s.precSucc x) {v0 : IssueId} (hv0 : v0 ∈ S) :
    ∃ v ∈ S, s.onCycle s.precSucc v = true :=
  exists_onCycle_of_all_succ (precSucc_subset_present s) hstuck hv0

end Tl.Kernel
