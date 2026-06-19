/-
`Tl.Kernel.ReachBFS` — an O(V+E) frontier/worklist reachability engine, proved
list-equal to the spec `reachClosure` (ADR-0004 thms 4/6/10, ADR-0009 reach zone).

The spec `reachClosure` (Ready.lean) iterates `reachStep = dedup (acc ++ acc.flatMap
succ)` — each round re-scans the whole accumulator's successors and `dedup` is
O(M²), so the closure is O(N³) on a deep chain. This module ships a genuine
breadth-first engine: it expands only the *frontier* (the nodes discovered last
round), testing membership against a `Std.HashSet` visited-set (O(1)-amortized),
so each node's out-edges are walked exactly once → O(V+E).

Correctness is a two-step refinement to the spec, exploiting that `dedup` now keeps
the *first* occurrence (so `reachClosure` is a stable BFS-ordered layering — see
`Ready.dedup`):
  1. `reachBFSL` — a list-membership reference engine — is list-equal to
     `reachClosure` (`reachBFSL_eq`), via the round recurrence
     `reachStep succ acc = acc ++ bfsLayer succ acc frontier`.
  2. the shipped `reachBFS` (HashSet visited) is list-equal to `reachBFSL`
     (`reachBFS_eq_spec`), so `reachBFS_eq : reachBFS = reachClosure`.
The seed is assumed duplicate-free (`Nodup`) — every call site seeds a singleton
or an OR-Set-derived adjacency list, both nodup; the spec dedups its seed at the
first step, the frontier engine cannot without rescanning.

`reachBFSL` is proof scaffolding only (list `∈`, so O(N·E)); the shipped path is
the HashSet `reachBFS` (ADR-0024 indexed views; ADR-0023 efficiency tiering).
-/
import Tl.Kernel.Reach
import Tl.Kernel.HashMapView

namespace Tl.Kernel

open Tl.Crdt

variable {α : Type _} [DecidableEq α]

/-! ## `dedup` / `filter` algebra -/

/-- `dedup` commutes with `filter` (both keep first occurrences of `p`-survivors). -/
theorem dedup_filter (p : α → Bool) : (l : List α) →
    (dedup l).filter p = dedup (l.filter p)
  | [] => rfl
  | x :: xs => by
    by_cases hpx : p x = true
    · show (x :: (dedup xs).filter (fun y => decide (y ≠ x))).filter p
         = dedup ((x :: xs).filter p)
      rw [List.filter_cons_of_pos hpx, List.filter_cons_of_pos hpx]
      show x :: List.filter p ((dedup xs).filter (fun y => decide (y ≠ x)))
         = x :: (dedup (xs.filter p)).filter (fun y => decide (y ≠ x))
      rw [List.filter_filter, ← dedup_filter p xs, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro a _
      exact Bool.and_comm (p a) (decide (a ≠ x))
    · show (x :: (dedup xs).filter (fun y => decide (y ≠ x))).filter p
         = dedup ((x :: xs).filter p)
      rw [List.filter_cons_of_neg hpx, List.filter_cons_of_neg hpx]
      show List.filter p ((dedup xs).filter (fun y => decide (y ≠ x)))
         = dedup (xs.filter p)
      rw [List.filter_filter, ← dedup_filter p xs]
      apply List.filter_congr
      intro a _
      by_cases h : p a = true
      · rw [h, Bool.true_and, decide_eq_true_eq]
        exact fun he => hpx (he ▸ h)
      · rw [Bool.not_eq_true] at h
        rw [h, Bool.false_and]

omit [DecidableEq α] in
/-- `filter` with an always-true predicate over a list is the identity. -/
theorem filter_self_of_all (p : α → Bool) {l : List α} (h : ∀ y ∈ l, p y = true) :
    l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons_of_pos (h x List.mem_cons_self),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- **Lemma A** (append/dedup): a duplicate-free prefix survives `dedup` verbatim,
    and the tail is the deduped suffix with the prefix removed. -/
theorem dedup_append_nodup : (acc : List α) → acc.Nodup → (rest : List α) →
    dedup (acc ++ rest) = acc ++ dedup (rest.filter (fun y => decide (y ∉ acc)))
  | [], _, rest => by
    rw [List.nil_append, List.nil_append]
    congr 1
    symm
    apply filter_self_of_all
    intro y _
    rw [decide_eq_true_eq]
    exact fun h => nomatch h
  | a :: acc', hnd, rest => by
    have hnd' : acc'.Nodup := (List.nodup_cons.mp hnd).2
    have haacc' : a ∉ acc' := (List.nodup_cons.mp hnd).1
    rw [List.cons_append]
    show a :: (dedup (acc' ++ rest)).filter (fun y => decide (y ≠ a))
       = a :: (acc' ++ dedup (rest.filter (fun y => decide (y ∉ a :: acc'))))
    rw [dedup_append_nodup acc' hnd' rest, List.filter_append]
    have hacc'fil : acc'.filter (fun y => decide (y ≠ a)) = acc' := by
      apply filter_self_of_all
      intro y hy
      rw [decide_eq_true_eq]
      exact fun he => haacc' (he ▸ hy)
    rw [hacc'fil]
    congr 2
    rw [dedup_filter]
    congr 1
    rw [List.filter_filter]
    apply List.filter_congr
    intro y _
    rw [← Bool.decide_and]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hya, hyacc⟩ hmem
      rcases List.mem_cons.mp hmem with he | hin
      · exact hya he
      · exact hyacc hin
    · intro hnotmem
      exact ⟨fun he => hnotmem (List.mem_cons.mpr (Or.inl he)),
             fun hin => hnotmem (List.mem_cons.mpr (Or.inr hin))⟩

namespace State

/-! ## The list-membership reference engine -/

/-- The next frontier layer: successors of the current frontier not yet in `acc`,
    deduplicated (first-occurrence order). -/
def bfsLayer (succ : IssueId → List IssueId) (acc frontier : List IssueId) : List IssueId :=
  dedup ((frontier.flatMap succ).filter (fun y => decide (y ∉ acc)))

theorem mem_bfsLayer {succ : IssueId → List IssueId} {acc frontier : List IssueId} {y : IssueId} :
    y ∈ bfsLayer succ acc frontier ↔ y ∈ frontier.flatMap succ ∧ y ∉ acc := by
  unfold bfsLayer
  rw [dedup_mem, List.mem_filter, decide_eq_true_eq]

/-- The round recurrence: one `reachStep` over a nodup accumulator whose
    pre-frontier part is `succ`-closed grows the accumulator by exactly the next
    frontier layer. -/
theorem reachStep_eq_append_layer (succ : IssueId → List IssueId)
    (acc below frontier : List IssueId) (hnd : acc.Nodup)
    (hsplit : acc = below ++ frontier)
    (hclosed : ∀ y ∈ below.flatMap succ, y ∈ acc) :
    reachStep succ acc = acc ++ bfsLayer succ acc frontier := by
  unfold State.reachStep bfsLayer
  rw [dedup_append_nodup acc hnd]
  congr 1
  have hsucc : acc.flatMap succ = below.flatMap succ ++ frontier.flatMap succ := by
    rw [hsplit, List.flatMap_append]
  have hbelow : (below.flatMap succ).filter (fun y => decide (y ∉ acc)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy
    rw [decide_eq_true_eq]
    exact fun hcon => hcon (hclosed y hy)
  rw [hsucc, List.filter_append, hbelow, List.nil_append]

/-- List-membership frontier closure (PROOF REFERENCE, not shipped): carry the
    reachable accumulator and the last frontier; each round appends the next layer
    and recurses on it. -/
def reachBFSLgo (succ : IssueId → List IssueId) :
    Nat → List IssueId → List IssueId → List IssueId
  | 0, acc, _ => acc
  | n + 1, acc, frontier =>
    reachBFSLgo succ n (acc ++ bfsLayer succ acc frontier) (bfsLayer succ acc frontier)

def reachBFSL (succ : IssueId → List IssueId) (n : Nat) (seed : List IssueId) : List IssueId :=
  reachBFSLgo succ n seed seed

/-- The frontier-engine invariant: started from a nodup accumulator split as
    `below ++ frontier` with the pre-frontier part `succ`-closed, `reachBFSLgo`
    reproduces `iterateN reachStep`. -/
theorem reachBFSLgo_eq (succ : IssueId → List IssueId) :
    (n : Nat) → (acc below frontier : List IssueId) → acc.Nodup →
    acc = below ++ frontier → (∀ y ∈ below.flatMap succ, y ∈ acc) →
    reachBFSLgo succ n acc frontier = iterateN (reachStep succ) n acc
  | 0, acc, _, _, _, _, _ => rfl
  | n + 1, acc, below, frontier, hnd, hsplit, hclosed => by
    have hstep : reachStep succ acc = acc ++ bfsLayer succ acc frontier :=
      reachStep_eq_append_layer succ acc below frontier hnd hsplit hclosed
    show reachBFSLgo succ n (acc ++ bfsLayer succ acc frontier) (bfsLayer succ acc frontier)
       = iterateN (reachStep succ) (n + 1) acc
    rw [show iterateN (reachStep succ) (n + 1) acc
          = iterateN (reachStep succ) n (reachStep succ acc) from rfl, hstep]
    -- continue with acc' = acc ++ layer, below' = acc, frontier' = layer
    refine reachBFSLgo_eq succ n (acc ++ bfsLayer succ acc frontier) acc
      (bfsLayer succ acc frontier) ?_ rfl ?_
    · -- nodup of acc ++ layer
      rw [List.nodup_append]
      refine ⟨hnd, dedup_nodup _, ?_⟩
      intro x hx y hy
      rw [mem_bfsLayer] at hy
      exact fun he => hy.2 (he ▸ hx)
    · -- acc.flatMap succ ⊆ acc ++ layer
      intro y hy
      rw [List.mem_append]
      by_cases hyacc : y ∈ acc
      · exact Or.inl hyacc
      · refine Or.inr (mem_bfsLayer.mpr ⟨?_, hyacc⟩)
        rw [hsplit, List.flatMap_append, List.mem_append] at hy
        rcases hy with hb | hf
        · exact absurd (hclosed y hb) hyacc
        · exact hf

/-- **The list reference is `reachClosure`.** -/
theorem reachBFSL_eq (succ : IssueId → List IssueId) (n : Nat) (seed : List IssueId)
    (hseed : seed.Nodup) : reachBFSL succ n seed = reachClosure succ n seed := by
  unfold State.reachBFSL State.reachClosure
  exact reachBFSLgo_eq succ n seed [] seed hseed (List.nil_append seed).symm
    (by intro y hy; rw [List.mem_flatMap] at hy; obtain ⟨a, ha, _⟩ := hy; exact nomatch ha)

end State

end Tl.Kernel
