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
  - `reachExpanded_nodup` — across a run the layers expanded are duplicate-free.
  - `reachExpandTrace_eq` — the reference engine's actual per-round `flatMap succ`
    input list equals `reachFrontier 0 … (n-1)`.
  - `reachBFSgoTrace_flatten_nodup` — the SHIPPED engine's actual per-round fold
    inputs flatten to a duplicate-free list ⇒ each node's out-edges folded once.

Three layers of claim, kept distinct to avoid overstating (a prior review caught a
*false* O(V+E) structural claim in this epic, and a follow-up caught the work-shape
guard being stated only over the reference engine):
  • The partition theorems hold of the reachable set's BFS layering and so of any
    correct engine's *output* — they do NOT by themselves forbid a Θ(V·E) engine.
    The guard against an output-changing regression remains `reachBFSgo_eq`.
  • `reachExpandTrace_eq` is the *work-shape* guard over the list-reference engine
    `reachBFSLgo`: an equation over its per-round fold-INPUT list, which a
    whole-accumulator re-scan recursion (folding over the entire `reachClosure k`)
    cannot satisfy — its faithful trace is the nested closures, not the fresh layers.
  • `reachBFSgoTrace_flatten_nodup` carries the same tooth to the SHIPPED HashSet
    engine `reachBFSgo` (`reachBFSgoTrace` instruments its real recursion, early-exit
    and all): the actual fold inputs of the engine that RUNS flatten to a
    duplicate-free list. Since `reachBFSgo_eq` is output-only, this — not it — is what
    forbids a re-scan rewrite of the shipped recursion.

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

/-! ## Engine-coupled: the per-round fold inputs ARE the frontiers

The theorems above are about `reachFrontier` and `reachClosure` — true of the
reachable-set's BFS layering, hence of any correct engine's *output*. The guard
that distinguishes the O(V+E) frontier engine from a Θ(V·E) whole-accumulator
re-scan is an equation over the engine's *per-round `flatMap succ` input list*:
`reachExpandTrace` instruments `reachBFSLgo`'s recursion (the `acc ++ bfsLayer …`
/ `bfsLayer …` threading and the recorded `frontier` are copied verbatim).
`reachExpandTrace_eq` then proves those inputs are exactly the disjoint
`reachFrontier`s — a statement a re-scan recursion (per-round input = the whole
`reachClosure k`) cannot satisfy, so regressing the recursion breaks this proof.
This is the work-shape guard over the LIST-REFERENCE engine; the next section
(`reachBFSgoTrace_*`) carries it to the SHIPPED `reachBFSgo`, since `reachBFSgo_eq`
relates the two only by output. -/

/-- The per-round `flatMap succ` input the list-reference engine expands, traced in
    round order — `reachBFSLgo`'s recursion with the expanded `frontier` recorded. -/
def reachExpandTrace (succ : IssueId → List IssueId) :
    Nat → List IssueId → List IssueId → List (List IssueId)
  | 0, _, _ => []
  | n + 1, acc, frontier =>
    frontier :: reachExpandTrace succ n (acc ++ bfsLayer succ acc frontier)
      (bfsLayer succ acc frontier)

/-- The engine's per-round inputs from state `(reachClosure k, reachFrontier k)` are
    `reachFrontier k, reachFrontier (k+1), …` — the fresh layers, not the closures. -/
theorem reachExpandTrace_frontier (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) :
    (n k : Nat) →
    reachExpandTrace succ n (reachClosure succ k seed) (reachFrontier succ seed k)
      = (List.range' k n).map (reachFrontier succ seed)
  | 0, _ => rfl
  | n + 1, k => by
    show reachFrontier succ seed k :: reachExpandTrace succ n
          (reachClosure succ k seed
            ++ bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k))
          (bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k))
       = (List.range' k (n + 1)).map (reachFrontier succ seed)
    rw [show bfsLayer succ (reachClosure succ k seed) (reachFrontier succ seed k)
          = reachFrontier succ seed (k + 1) from rfl,
      ← reach_frontier_decomp succ seed hnd k,
      reachExpandTrace_frontier succ seed hnd n (k + 1), List.range'_succ, List.map_cons]

/-- **The engine expands exactly `reachFrontier 0 … (n-1)`** — an equation over the
    actual per-round fold inputs. A whole-accumulator re-scan recursion expands the
    nested `reachClosure k` instead, so it fails this equation. -/
theorem reachExpandTrace_eq (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) (n : Nat) :
    reachExpandTrace succ n seed seed = (List.range n).map (reachFrontier succ seed) := by
  rw [List.range_eq_range']
  exact reachExpandTrace_frontier succ seed hnd n 0

/-- **Each node's out-edges folded once (engine-coupled).** The flattened per-round
    expansion inputs are duplicate-free — each reachable node is expanded in exactly
    one round (≤ E edge-examinations, ≤ V node-insertions). FALSE for a re-scan
    engine, whose per-round inputs are the overlapping nested closures. -/
theorem reachExpandTrace_flatten_nodup (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) (n : Nat) :
    (reachExpandTrace succ n seed seed).flatten.Nodup := by
  rw [reachExpandTrace_eq succ seed hnd n]
  show ((List.range n).flatMap (reachFrontier succ seed)).Nodup
  exact reachExpanded_nodup succ seed hnd n

/-! ## The SHIPPED HashSet engine expands the same frontiers

The trace above is over the list-reference `reachBFSLgo`; `reachBFSgo_eq` couples
`reachBFSgo` to it only by OUTPUT equality, so on its own it would not catch a
`reachBFSgo` rewritten to re-scan whole closures while returning the same list.
This section closes that gap: `reachBFSgoTrace` instruments the SHIPPED engine's
recursion (HashSet visited, early-exit), and `reachBFSgoTrace_flatten_nodup` proves
its actual per-round fold inputs are duplicate-free — the work-shape guard over the
engine that really runs. A re-scan rewrite of `reachBFSgo`'s recursion records the
nested closures, whose flatten is not duplicate-free, so it fails to compile. -/

/-- A trailing empty frontier contributes nothing: every later layer is empty. -/
theorem reachExpandTrace_nil_flatten (succ : IssueId → List IssueId) :
    (n : Nat) → (acc : List IssueId) → (reachExpandTrace succ n acc []).flatten = []
  | 0, _ => rfl
  | n + 1, acc => by
    show (([] : List IssueId)
          :: reachExpandTrace succ n (acc ++ bfsLayer succ acc []) (bfsLayer succ acc [])).flatten = []
    rw [show bfsLayer succ acc ([] : List IssueId) = [] from rfl, List.append_nil,
      List.flatten_cons, List.nil_append, reachExpandTrace_nil_flatten succ n acc]

/-- The per-round `flatMap succ` input the SHIPPED engine `reachBFSgo` expands, traced
    in round order — `reachBFSgo`'s recursion (HashSet visited, early-exit) with the
    expanded `frontier` recorded. -/
def reachBFSgoTrace (succ : IssueId → List IssueId) :
    Nat → Std.HashSet IssueId → List IssueId → List IssueId → List (List IssueId)
  | 0, _, _, _ => []
  | n + 1, vis, accRev, frontier =>
    if frontier.isEmpty then []
    else frontier :: reachBFSgoTrace succ n ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).1
      (((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2 ++ accRev)
      ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2.reverse

/-- The shipped engine's recorded inputs flatten to the same nodes as the reference's
    (the early-exit only drops trailing empty layers) — a representation refinement
    reusing `reachBFSgo_eq`'s visited-set invariant (`bfsFold_spec`). -/
theorem reachBFSgoTrace_flatten (succ : IssueId → List IssueId) :
    (n : Nat) → (vis : Std.HashSet IssueId) → (accRev frontier : List IssueId) →
    (∀ z, vis.contains z = true ↔ z ∈ accRev.reverse) →
    (reachBFSgoTrace succ n vis accRev frontier).flatten
      = (reachExpandTrace succ n accRev.reverse frontier).flatten
  | 0, _, _, _, _ => rfl
  | n + 1, vis, accRev, frontier, hvis => by
    by_cases hfe : frontier.isEmpty = true
    · have hfnil : frontier = [] := List.isEmpty_iff.mp hfe
      show (if frontier.isEmpty then [] else
              frontier :: reachBFSgoTrace succ n ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).1
                (((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2 ++ accRev)
                ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2.reverse).flatten
         = (reachExpandTrace succ (n + 1) accRev.reverse frontier).flatten
      rw [if_pos hfe, hfnil]
      exact (reachExpandTrace_nil_flatten succ (n + 1) accRev.reverse).symm
    · show (if frontier.isEmpty then [] else
              frontier :: reachBFSgoTrace succ n ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).1
                (((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2 ++ accRev)
                ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2.reverse).flatten
         = (reachExpandTrace succ (n + 1) accRev.reverse frontier).flatten
      rw [if_neg hfe]
      obtain ⟨hout, hvis'⟩ := bfsFold_spec (frontier.flatMap succ) accRev.reverse [] vis
        (fun z => by rw [List.append_nil]; exact hvis z)
      have hlayer : ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2
                  = (bfsLayer succ accRev.reverse frontier).reverse := by
        rw [hout, List.append_nil]
        unfold State.bfsLayer
        congr 2
        apply List.filter_congr
        intro w _
        rw [List.append_nil]
      have hp1 : ∀ z, ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).1.contains z = true
                    ↔ z ∈ (((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2 ++ accRev).reverse := by
        intro z
        rw [hvis' z, List.reverse_append, List.mem_append, List.mem_append, List.mem_reverse,
          List.mem_reverse]
      rw [List.flatten_cons,
        show reachExpandTrace succ (n + 1) accRev.reverse frontier
            = frontier :: reachExpandTrace succ n (accRev.reverse ++ bfsLayer succ accRev.reverse frontier)
                (bfsLayer succ accRev.reverse frontier) from rfl,
        List.flatten_cons]
      congr 1
      rw [reachBFSgoTrace_flatten succ n _ _ _ hp1, hlayer, List.reverse_append,
        List.reverse_reverse]

/-- **Each node's out-edges folded once — over the SHIPPED engine.** The actual
    per-round fold inputs of `reachBFSgo` flatten to a duplicate-free list. A
    whole-accumulator re-scan recursion records the nested `reachClosure k` instead,
    whose flatten repeats nodes, so this proof fails — the build-time work-shape guard
    over the engine that runs. -/
theorem reachBFSgoTrace_flatten_nodup (succ : IssueId → List IssueId) (seed : List IssueId)
    (hnd : seed.Nodup) (n : Nat) :
    (reachBFSgoTrace succ n (hashSetOf seed) seed.reverse seed).flatten.Nodup := by
  rw [reachBFSgoTrace_flatten succ n (hashSetOf seed) seed.reverse seed
        (by intro z; rw [List.reverse_reverse, Std.HashSet.contains_iff_mem, mem_hashSetOf]),
      List.reverse_reverse]
  exact reachExpandTrace_flatten_nodup succ seed hnd n

end State

end Tl.Kernel
