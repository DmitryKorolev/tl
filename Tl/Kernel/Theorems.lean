/-
`Tl.Kernel.Theorems` — the convergence theorems (ADR-0004 thm 1–2, 8).

Because every op acts by `apply s o = State.merge s o.delta` (one mutation path, a
join with the op's delta), the whole convergence story reduces to the state
join-semilattice. We give the lattice order `s ≤ t ↔ merge s t = t`, show `joinAll`
(the fold-as-join-of-deltas) is the *least upper bound* of its argument list, and
read off:

* **thm 2** — strong eventual convergence: replicas that observed the same op
  *set* materialize identical state (`fold_eq_of_mem_iff`); permutation- and
  duplication-insensitivity are corollaries (`fold_perm`, `fold_append_self`).
* **thm 8** — CvRDT inflation/monotonicity: `s ≤ apply s o` (`le_apply`) and
  `ops ⊆ ops' → fold ops ≤ fold ops'` (`fold_le_of_subset`); idempotent
  re-delivery (`apply_idem`) is in `Tl.Kernel.Apply`.

Thm 1 (the join is a commutative/associative/idempotent semilattice over the whole
product) is `State.merge_comm/assoc/idem` and the per-layer laws it composes.
-/
import Tl.Kernel.Cycles
import Tl.Kernel.Apply

namespace Tl.Kernel

open Tl.Crdt

/-! ## The join-semilattice order -/

/-- The lattice order: `s ≤ t` iff merging `s` into `t` is absorbed. -/
def State.le (s t : State) : Prop := State.merge s t = t

theorem State.le_refl (s : State) : s.le s := State.merge_idem s

theorem State.le_trans {a b c : State} (hab : a.le b) (hbc : b.le c) : a.le c := by
  unfold State.le at *
  calc State.merge a c = State.merge a (State.merge b c) := by rw [hbc]
    _ = State.merge (State.merge a b) c := (State.merge_assoc a b c).symm
    _ = State.merge b c := by rw [hab]
    _ = c := hbc

theorem State.le_antisymm {a b : State} (hab : a.le b) (hba : b.le a) : a = b := by
  unfold State.le at hab hba
  rw [← hab, State.merge_comm, hba]

/-! ## `joinAll` is the least upper bound -/

/-- The fold seen as the join of a list of states (here, the per-op deltas). -/
def joinAll (l : List State) : State := l.foldl State.merge State.empty

theorem foldl_merge (l : List State) (a : State) :
    l.foldl State.merge a = State.merge a (joinAll l) := by
  induction l generalizing a with
  | nil =>
    show a = State.merge a (joinAll [])
    rw [show joinAll [] = State.empty from rfl, State.merge_empty_right]
  | cons x xs ih =>
    show xs.foldl State.merge (State.merge a x) = State.merge a (joinAll (x :: xs))
    rw [ih (State.merge a x)]
    have hcons : joinAll (x :: xs) = State.merge x (joinAll xs) := by
      show (x :: xs).foldl State.merge State.empty = State.merge x (joinAll xs)
      rw [List.foldl_cons, State.merge_empty_left, ih x]
    rw [hcons, State.merge_assoc]

theorem joinAll_cons (x : State) (xs : List State) :
    joinAll (x :: xs) = State.merge x (joinAll xs) := by
  show (x :: xs).foldl State.merge State.empty = State.merge x (joinAll xs)
  rw [List.foldl_cons, State.merge_empty_left]
  exact foldl_merge xs x

/-- Every element of the list is below the join. -/
theorem le_joinAll {x : State} : {l : List State} → x ∈ l → x.le (joinAll l)
  | [], h => nomatch h
  | y :: ys, h => by
    rw [joinAll_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · show State.merge x (State.merge x (joinAll ys)) = State.merge x (joinAll ys)
      rw [← State.merge_assoc, State.merge_idem]
    · have hx := le_joinAll hmem
      show State.merge x (State.merge y (joinAll ys)) = State.merge y (joinAll ys)
      calc State.merge x (State.merge y (joinAll ys))
          = State.merge y (State.merge x (joinAll ys)) := by
            rw [← State.merge_assoc, State.merge_comm x y, State.merge_assoc]
        _ = State.merge y (joinAll ys) := by rw [hx]

/-- The join is the *least* upper bound. -/
theorem joinAll_le {u : State} : {l : List State} → (∀ x ∈ l, State.le x u) → (joinAll l).le u
  | [], _ => by
    show State.merge (joinAll []) u = u
    rw [show joinAll [] = State.empty from rfl, State.merge_empty_left]
  | y :: ys, h => by
    rw [joinAll_cons]
    have hy : State.le y u := h y (List.mem_cons_self ..)
    have hys : (joinAll ys).le u := joinAll_le (fun x hx => h x (List.mem_cons_of_mem y hx))
    show State.merge (State.merge y (joinAll ys)) u = u
    calc State.merge (State.merge y (joinAll ys)) u
        = State.merge y (State.merge (joinAll ys) u) := State.merge_assoc ..
      _ = State.merge y u := by rw [hys]
      _ = u := hy

/-! ## The fold as a join of deltas -/

/-- `fold` is exactly the join of the per-op deltas (apply = join-with-delta). -/
theorem fold_eq_joinAll (ops : List Op) : fold ops = joinAll (ops.map Op.delta) := by
  show ops.foldl apply State.empty = (ops.map Op.delta).foldl State.merge State.empty
  rw [List.foldl_map]
  rfl

/-! ## Thm 2 — strong eventual convergence -/

/-- Replicas that have observed the same op *set* materialize identical state
    (ADR-0004 thm 2; with idempotence the result depends on the set, not the
    multiset). The single correctness obligation git-as-transport imposes. -/
theorem fold_eq_of_mem_iff {l1 l2 : List Op} (h : ∀ o, o ∈ l1 ↔ o ∈ l2) :
    fold l1 = fold l2 := by
  rw [fold_eq_joinAll, fold_eq_joinAll]
  apply State.le_antisymm
  · refine joinAll_le (fun x hx => le_joinAll ?_)
    rw [List.mem_map] at hx ⊢
    obtain ⟨o, ho, rfl⟩ := hx
    exact ⟨o, (h o).mp ho, rfl⟩
  · refine joinAll_le (fun x hx => le_joinAll ?_)
    rw [List.mem_map] at hx ⊢
    obtain ⟨o, ho, rfl⟩ := hx
    exact ⟨o, (h o).mpr ho, rfl⟩

/-- Permutation-insensitivity (the git-concat / reorder requirement). -/
theorem fold_perm {l1 l2 : List Op} (h : l1.Perm l2) : fold l1 = fold l2 :=
  fold_eq_of_mem_iff (fun _ => h.mem_iff)

/-- Duplication-insensitivity: re-delivering the whole log is a no-op. -/
theorem fold_append_self (l : List Op) : fold (l ++ l) = fold l :=
  fold_eq_of_mem_iff (fun o => by
    rw [List.mem_append]; exact ⟨fun h => h.elim id id, Or.inl⟩)

/-- Folding an appended suffix continues from the prefix's fold — the anchor of
    the store's fold cache (ADR-0022): the cached state *is* `fold prefix`, and a
    read folds only the appended ops on top. Suffixes interleaved across
    segments reduce to this via `fold_perm`. -/
theorem fold_append (l1 l2 : List Op) : fold (l1 ++ l2) = l2.foldl apply (fold l1) := by
  show (l1 ++ l2).foldl apply State.empty = l2.foldl apply (l1.foldl apply State.empty)
  rw [List.foldl_append]

/-! ## Thm 8 — CvRDT inflation and monotonicity -/

/-- Every op only moves state *up* the lattice. -/
theorem le_apply (s : State) (o : Op) : s.le (apply s o) := by
  show State.merge s (State.merge s o.delta) = State.merge s o.delta
  rw [← State.merge_assoc, State.merge_idem]

/-- The fold is monotone under op-set inclusion — a merge never loses acknowledged
    information. With thm 2 this is the full state-CvRDT pair. -/
theorem fold_le_of_subset {l1 l2 : List Op} (h : ∀ o ∈ l1, o ∈ l2) :
    (fold l1).le (fold l2) := by
  rw [fold_eq_joinAll, fold_eq_joinAll]
  refine joinAll_le (fun x hx => le_joinAll ?_)
  rw [List.mem_map] at hx ⊢
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨o, h o ho, rfl⟩

/-! ## Tracker theorems — `ready` characterization and time-monotonicity

The ranked `ready` list is a permutation of the filtered present issues, so its
membership is exactly the readiness predicate (thm 4); and since `now` enters
`ready` only through the monotone defer conjunct, the passage of time never
un-readies an item (thm 9). -/

/-- The ranked sort is a permutation of its input — it filters nothing. -/
theorem rankSort_perm (s : State) (l : List IssueId) : (State.rankSort s l).Perm l := by
  unfold State.rankSort
  exact List.mergeSort_perm l (fun a b => s.readyLe a b)

theorem mem_rankSort (s : State) (x : IssueId) (l : List IssueId) :
    x ∈ State.rankSort s l ↔ x ∈ l := (rankSort_perm s l).mem_iff

/-- `presentIssues` is exactly the materialized issues. -/
theorem mem_presentIssues (s : State) (i : IssueId) : i ∈ s.presentIssues ↔ s.hasIssue i :=
  OrSet.mem_presentElements s.issues i

/-- **Thm 4** (ready soundness + completeness): `i ∈ ready s now` iff `i` is a
    materialized issue satisfying the readiness predicate — every blocker
    discharged (closed by effective status, or dangling and inert), `open`,
    non-epic, non-deferred (ADR-0004 thm 4, ADR-0003 §5, ADR-0010). The ranked
    list filters nothing, so the queue's membership is exactly readiness. -/
theorem mem_ready_iff (s : State) (now : Instant) (i : IssueId) :
    i ∈ s.ready now ↔ i ∈ s.presentIssues ∧ s.isReady now i = true := by
  unfold State.ready
  rw [mem_rankSort, List.mem_filter]

/-- The defer conjunct is monotone in `now`: a non-deferred-at-`now` item stays
    non-deferred at any later `now'`. -/
theorem deferOk_mono {d : IssueData} {now now' : Instant} (h : now ≤ now') :
    State.deferOk d now = true → State.deferOk d now' = true := by
  unfold State.deferOk
  cases hd : d.deferUntilOf with
  | none => exact fun _ => rfl
  | some t =>
    intro ht
    rw [decide_eq_true_iff] at ht ⊢
    exact Nat.le_trans ht h

/-- Readiness is monotone in `now` (only the defer conjunct depends on `now`). -/
theorem isReady_mono (s : State) {now now' : Instant} (h : now ≤ now') (i : IssueId) :
    s.isReady now i = true → s.isReady now' i = true := by
  unfold State.isReady
  intro hr
  simp only [Bool.and_eq_true] at hr ⊢
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hdef⟩, he⟩ := hr
  exact ⟨⟨⟨⟨ha, hb⟩, hc⟩, deferOk_mono h hdef⟩, he⟩

/-- **Thm 9** (ready time-monotonicity): the passage of time alone never removes a
    workable item — a deferred task only ever resurfaces (ADR-0010, ADR-0004 thm 9).
    The defer-dual of close-monotonicity. -/
theorem ready_time_mono (s : State) {now now' : Instant} (h : now ≤ now') {i : IssueId}
    (hi : i ∈ s.ready now) : i ∈ s.ready now' := by
  rw [mem_ready_iff] at hi ⊢
  exact ⟨hi.1, isReady_mono s h i hi.2⟩

end Tl.Kernel
