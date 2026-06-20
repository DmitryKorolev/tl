/-
`Tl.Kernel.ReachFrontier` — the BFS frontier sequence of the O(V+E) reach engine,
and the PROVED "processed-once" structural invariant (ADR-0023 efficiency tiering,
the *provable-shape* tier).

The shipped engine `reachBFSgo` (ReachBFS.lean) expands one *frontier* per round —
the nodes discovered last round — testing membership against a `Std.HashSet`. This
module names that frontier sequence (`reachFrontier`, the recurrence the engine
threads, proved equal to one round's `bfsLayer`) and proves the structure that pins
its complexity class as a PLAIN PROPOSITION (no cost semantics):

  - `reachClosure_eq_flatMap_frontier` — the frontiers, concatenated in BFS order,
    ARE the reachable set: `reachClosure n = ⋃ k≤n reachFrontier k` (as lists).
  - `reachFrontier_disjoint` — the frontiers are pairwise disjoint: a node in one
    layer is in no other. With the concatenation above, every reachable node lands
    in EXACTLY ONE frontier (`reachClosure_mem_unique_frontier`).
  - `reachFrontier_subset_present` — each frontier ⊆ `presentIssues`.
  - `reachExpanded_nodup` — the nodes the engine ever *expands* (folds `succ` over)
    across a run are duplicate-free ⇒ each node's out-edges are folded exactly once
    (total edge-work ≤ E, node-work ≤ V).
  - `reachBFSLgo_step_frontier` — the engine genuinely threads `reachFrontier`: one
    round at state `(reachClosure k, reachFrontier k)` advances to
    `(reachClosure (k+1), reachFrontier (k+1))`.

Why this is a *self-enforcing* guard, not a restatement of correctness: the
disjointness rests on `bfsLayer`'s `∉ acc` filter (`mem_bfsLayer`), and the
engine-threading lemma pins `reachFrontier` to the engine's actual per-round
frontier. A regression to a whole-accumulator re-scan (the retired `reachStep`
shape, or a per-round re-dedup) would make the "per-round inputs are pairwise
disjoint" claim FALSE — the accumulator is not disjoint from itself — so it cannot
be proved about a Θ(V·E) engine. The build fails, not just a perf test (the defect
that shipped under the dep-path work existed precisely because this was tested-only).

Tier boundary (ADR-0023): this proves the operation STRUCTURE (each node/edge
processed once). The per-operation → wall-clock gap, and `Std.HashSet`/`HashMap`
amortized-O(1) (hash distribution, resizing), stay TESTED + a tier-3 carried
assumption (docs/overview.md, Trusted) — the same status as the system clock.

Stated over the list-reference engine `reachBFSLgo` / the spec `reachClosure`; the
shipped HashSet engine equals them (`reachBFSgo_eq` / `reachBFS_eq`), so the
structure transfers to the compiled path. Seeds are duplicate-free at every call
site (singletons / OR-Set adjacency), as the partition needs.
-/
import Tl.Kernel.ReachBFS

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## The BFS frontier sequence -/

/-- The breadth-first frontier discovered at round `k`: the seed at round 0, then
    each subsequent layer is the engine's `bfsLayer` over the accumulated closure
    and the previous frontier — exactly the frontier `reachBFSLgo` threads. -/
def reachFrontier (succ : IssueId → List IssueId) (seed : List IssueId) : Nat → List IssueId
  | 0 => seed
  | k + 1 => bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k)

/-- `reachClosure` is duplicate-free for a nodup seed (each round is a `dedup`). -/
theorem reachClosure_nodup (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) : (n : Nat) → (reachClosure succ n seed).Nodup
  | 0 => hnd
  | n + 1 => by rw [reachClosure_succ]; exact reachStep_nodup succ _

/-! ## The layer decomposition: closure grows by exactly the next frontier -/

/-- **Keystone.** Each round grows the closure by appending precisely the next
    frontier: `reachClosure (k+1) = reachClosure k ++ reachFrontier (k+1)`. The
    induction carries the split `reachClosure k = reachClosure (k-1) ++ reachFrontier k`
    (the IH) into `reachStep_eq_append_layer`, whose `below = reachClosure (k-1)` is
    already `succ`-closed (its out-edges are in the next closure). -/
theorem reach_frontier_decomp (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) :
    (k : Nat) → reachClosure succ (k + 1) seed
      = reachClosure succ k seed ++ reachFrontier succ seed (k + 1)
  | 0 => by
    rw [reachClosure_succ]
    exact reachStep_eq_append_layer succ seed [] seed hnd (List.nil_append seed).symm
      (by intro y hy; rw [List.mem_flatMap] at hy; obtain ⟨a, ha, _⟩ := hy; exact nomatch ha)
  | k + 1 => by
    rw [reachClosure_succ]
    refine reachStep_eq_append_layer succ (reachClosure succ (k + 1) seed)
      (reachClosure succ k seed) (reachFrontier succ seed (k + 1))
      (reachClosure_nodup succ seed hnd (k + 1)) (reach_frontier_decomp succ seed hnd k) ?_
    intro y hy
    rw [List.mem_flatMap] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [reachClosure_succ]
    exact mem_reachStep.mpr (Or.inr ⟨x, hx, hxy⟩)

/-- **Union = closure (BFS-ordered).** The frontiers `reachFrontier 0 … n`, in
    order, concatenate to `reachClosure n` — the reachable set IS the disjoint
    union of the layers, listed in discovery order. -/
theorem reachClosure_eq_flatMap_frontier (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) :
    (n : Nat) → reachClosure succ n seed = (List.range (n + 1)).flatMap (reachFrontier succ seed)
  | 0 => by
    show reachClosure succ 0 seed = (List.range 1).flatMap (reachFrontier succ seed)
    rw [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  | n + 1 => by
    have hrange : (List.range (n + 2)).flatMap (reachFrontier succ seed)
        = (List.range (n + 1)).flatMap (reachFrontier succ seed)
          ++ reachFrontier succ seed (n + 1) := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
    rw [hrange, reach_frontier_decomp succ seed hnd n,
      reachClosure_eq_flatMap_frontier succ seed hnd n]

/-! ## Pairwise disjointness: each node lands in exactly one frontier -/

/-- A node in frontier `j ≤ k` is in the accumulated closure at `k`. -/
theorem reachFrontier_subset_closure (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) {j k : Nat} (hjk : j ≤ k) :
    reachFrontier succ seed j ⊆ reachClosure succ k seed := by
  intro a ha
  rw [reachClosure_eq_flatMap_frontier succ seed hnd k, List.mem_flatMap]
  exact ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hjk), ha⟩

/-- A node freshly discovered at round `k+1` is NOT in the closure at `k` (the
    `bfsLayer` `∉ acc` filter — the structural fact a re-scan engine would lose). -/
theorem mem_reachFrontier_succ_notMem (succ : IssueId → List IssueId) (seed : List IssueId)
    {k : Nat} {a : IssueId} (ha : a ∈ reachFrontier succ seed (k + 1)) :
    a ∉ reachClosure succ k seed := by
  have ha' : a ∈ bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k) := ha
  rw [mem_bfsLayer] at ha'
  exact ha'.2

/-- Frontiers at distinct rounds are disjoint (the strictly-increasing-rounds
    direction): a node in an earlier layer is absent from every later one. -/
theorem reachFrontier_disjoint_lt (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) {i j : Nat} (hij : i < j) (a : IssueId)
    (hai : a ∈ reachFrontier succ seed i) : a ∉ reachFrontier succ seed j := by
  cases j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ m =>
    intro haj
    exact mem_reachFrontier_succ_notMem succ seed haj
      (reachFrontier_subset_closure succ seed hnd (Nat.lt_succ_iff.mp hij) hai)

/-- **Each reachable node lands in EXACTLY ONE frontier.** Existence is the union
    decomposition; uniqueness is pairwise disjointness. -/
theorem reachClosure_mem_unique_frontier (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) (n : Nat) {a : IssueId} (ha : a ∈ reachClosure succ n seed) :
    ∃! k, k ≤ n ∧ a ∈ reachFrontier succ seed k := by
  rw [reachClosure_eq_flatMap_frontier succ seed hnd n, List.mem_flatMap] at ha
  obtain ⟨k, hk, hak⟩ := ha
  refine ⟨k, ⟨Nat.lt_succ_iff.mp (List.mem_range.mp hk), hak⟩, ?_⟩
  rintro k' ⟨_, hak'⟩
  by_contra hne
  rcases Nat.lt_or_ge k' k with hlt | hge
  · exact reachFrontier_disjoint_lt succ seed hnd hlt a hak' hak
  · exact reachFrontier_disjoint_lt succ seed hnd (lt_of_le_of_ne hge (Ne.symm hne)) a hak hak'

/-! ## Each frontier ⊆ presentIssues -/

/-- Every frontier stays within a universe closed under `succ`. -/
theorem reachFrontier_subset_universe (succ : IssueId → List IssueId) {U seed : List IssueId}
    (hsU : seed ⊆ U) (hU : ∀ x ∈ U, succ x ⊆ U) :
    (k : Nat) → reachFrontier succ seed k ⊆ U
  | 0 => hsU
  | k + 1 => by
    intro a ha
    have ha' : a ∈ bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k) := ha
    rw [mem_bfsLayer, List.mem_flatMap] at ha'
    obtain ⟨⟨x, hx, hxa⟩, _⟩ := ha'
    exact hU x (reachFrontier_subset_universe succ hsU hU k hx) hxa

/-- **Each frontier ⊆ `presentIssues`** for any successor that stays present
    (`liveBlockersSucc`, `kindSucc`, … via the `_subset_present` lemmas). -/
theorem reachFrontier_subset_present (s : State) (succ : IssueId → List IssueId)
    (seed : List IssueId) (hsp : seed ⊆ s.presentIssues)
    (hsucc : ∀ x, succ x ⊆ s.presentIssues) (k : Nat) :
    reachFrontier succ seed k ⊆ s.presentIssues :=
  reachFrontier_subset_universe succ hsp (fun x _ => hsucc x) k

/-! ## Processed-once: each node's out-edges folded exactly once -/

/-- **Each edge folded once.** Across a fuel-`n` run the engine expands the
    frontiers `reachFrontier 0 … (n-1)`; their concatenation is `reachClosure (n-1)`
    — duplicate-free — so each reachable node's out-edges are folded in exactly its
    own round (≤ E edge-examinations, ≤ V node-insertions total). -/
theorem reachExpanded_nodup (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) (n : Nat) :
    ((List.range n).flatMap (reachFrontier succ seed)).Nodup := by
  cases n with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact List.nodup_nil
  | succ m =>
    rw [← reachClosure_eq_flatMap_frontier succ seed hnd m]
    exact reachClosure_nodup succ seed hnd m

/-! ## The engine genuinely threads `reachFrontier` -/

/-- **Engine ⇄ frontier sequence.** One round of the list-reference engine at state
    `(reachClosure k, reachFrontier k)` advances to `(reachClosure (k+1),
    reachFrontier (k+1))` — so the per-round frontier the engine folds `succ` over
    is exactly `reachFrontier k`, and the disjointness above is a statement about the
    engine's actual inputs (`reachBFSgo` shares this layering via `reachBFSgo_eq`). -/
theorem reachBFSLgo_step_frontier (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) (n k : Nat) :
    reachBFSLgo succ (n + 1) (reachClosure succ k seed) (reachFrontier succ seed k)
      = reachBFSLgo succ n (reachClosure succ (k + 1) seed) (reachFrontier succ seed (k + 1)) := by
  show reachBFSLgo succ n
        (reachClosure succ k seed
          ++ bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k))
        (bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k))
     = reachBFSLgo succ n (reachClosure succ (k + 1) seed) (reachFrontier succ seed (k + 1))
  rw [show bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k)
        = reachFrontier succ seed (k + 1) from rfl, ← reach_frontier_decomp succ seed hnd k]

end State

end Tl.Kernel
