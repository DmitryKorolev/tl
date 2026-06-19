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

/-! ## The shipped HashSet engine -/

/-- One expansion step (HashSet, shipped): cons a genuinely-new successor onto the
    reverse-output and mark it visited; skip a node already seen (O(1) membership). -/
def bfsStepFn (p : Std.HashSet IssueId × List IssueId) (y : IssueId) :
    Std.HashSet IssueId × List IssueId :=
  if p.1.contains y then p else (p.1.insert y, y :: p.2)

/-- A node is new for the next-round filter iff it is outside the current seen set
    and distinct from the just-added node. -/
theorem decide_notMem_cons_mid (z y : IssueId) (S r : List IssueId) :
    (decide (z ∉ S ++ r) && decide (z ≠ y)) = decide (z ∉ S ++ (y :: r)) := by
  rw [← Bool.decide_and]
  apply decide_eq_decide.mpr
  rw [List.mem_append, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨hnsr, hny⟩ (hs | he | hr)
    · exact hnsr (Or.inl hs)
    · exact hny he
    · exact hnsr (Or.inr hr)
  · intro hn
    exact ⟨fun h => h.elim (fun hs => hn (Or.inl hs)) (fun hr => hn (Or.inr (Or.inr hr))),
           fun he => hn (Or.inr (Or.inl he))⟩

/-- **The expansion fold.** Against a visited set representing the seen list
    `S ++ r`, folding the successors `ys` collects (reversed) exactly the deduped
    not-yet-seen nodes, and the resulting visited set represents the extended seen
    list. The HashSet's O(1) membership stands in for the spec's list `∉`. -/
theorem bfsFold_spec : ∀ (ys S r : List IssueId) (v : Std.HashSet IssueId),
    (∀ z, v.contains z = true ↔ z ∈ S ++ r) →
    (ys.foldl bfsStepFn (v, r)).2
        = (dedup (ys.filter (fun y => decide (y ∉ S ++ r)))).reverse ++ r
      ∧ ∀ z, (ys.foldl bfsStepFn (v, r)).1.contains z = true
          ↔ z ∈ S ++ (ys.foldl bfsStepFn (v, r)).2
  | [], S, r, v, hv => by
    refine ⟨?_, ?_⟩
    · show r = (dedup (([] : List IssueId).filter _)).reverse ++ r
      rw [List.filter_nil]; rfl
    · intro z
      show v.contains z = true ↔ z ∈ S ++ r
      exact hv z
  | y :: ys, S, r, v, hv => by
    rw [List.foldl_cons]
    show (ys.foldl bfsStepFn (bfsStepFn (v, r) y)).2 = _
       ∧ ∀ z, (ys.foldl bfsStepFn (bfsStepFn (v, r) y)).1.contains z = true ↔ _
    by_cases hc : v.contains y = true
    · -- y already seen: the step is a no-op, and the filter drops y
      have hceq : bfsStepFn (v, r) y = (v, r) := by unfold bfsStepFn; rw [if_pos hc]
      rw [hceq]
      have hyin : y ∈ S ++ r := (hv y).mp hc
      have hpy : decide (y ∉ S ++ r) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => h hyin
      rw [List.filter_cons_of_neg (by rw [hpy]; exact Bool.false_ne_true)]
      exact bfsFold_spec ys S r v hv
    · -- y new: cons it, recurse with the extended seen list
      rw [Bool.not_eq_true] at hc
      have hceq : bfsStepFn (v, r) y = (v.insert y, y :: r) := by
        unfold bfsStepFn
        rw [if_neg (show ¬ v.contains y = true by rw [hc]; exact Bool.false_ne_true)]
      rw [hceq]
      have hynotin : y ∉ S ++ r := by
        intro h
        have hcy : v.contains y = true := (hv y).mpr h
        rw [hc] at hcy
        exact Bool.noConfusion hcy
      have hpy : decide (y ∉ S ++ r) = true := by rw [decide_eq_true_eq]; exact hynotin
      -- new visited represents S ++ (y :: r)
      have hv' : ∀ z, (v.insert y).contains z = true ↔ z ∈ S ++ (y :: r) := by
        intro z
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hv z,
          List.mem_append, List.mem_append, List.mem_cons]
        constructor
        · rintro (he | hs | hr)
          · exact Or.inr (Or.inl he.symm)
          · exact Or.inl hs
          · exact Or.inr (Or.inr hr)
        · rintro (hs | he | hr)
          · exact Or.inr (Or.inl hs)
          · exact Or.inl he.symm
          · exact Or.inr (Or.inr hr)
      have hfeq : ys.filter (fun w => decide (w ∉ S ++ y :: r))
                = (ys.filter (fun w => decide (w ∉ S ++ r))).filter (fun w => decide (w ≠ y)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro w _
        rw [← decide_notMem_cons_mid w y S r, Bool.and_comm]
      obtain ⟨ih1, ih2⟩ := bfsFold_spec ys S (y :: r) (v.insert y) hv'
      refine ⟨?_, ih2⟩
      rw [ih1, List.filter_cons_of_pos (by rw [hpy]), hfeq, ← dedup_filter,
        show dedup (y :: ys.filter (fun w => decide (w ∉ S ++ r)))
           = y :: (dedup (ys.filter (fun w => decide (w ∉ S ++ r)))).filter (fun w => decide (w ≠ y))
           from rfl,
        List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The shipped frontier closure (HashSet visited, reverse-built output). -/
def reachBFSgo (succ : IssueId → List IssueId) :
    Nat → Std.HashSet IssueId → List IssueId → List IssueId → List IssueId
  | 0, _vis, accRev, _frontier => accRev.reverse
  | n + 1, vis, accRev, frontier =>
    let p := (frontier.flatMap succ).foldl bfsStepFn (vis, [])
    reachBFSgo succ n p.1 (p.2 ++ accRev) p.2.reverse

/-- **The shipped O(V+E) reachability engine** (ADR-0024 indexed views): each
    round expands only the frontier, walking each node's out-edges once and
    testing membership against the visited `Std.HashSet`. -/
def reachBFS (succ : IssueId → List IssueId) (n : Nat) (seed : List IssueId) : List IssueId :=
  reachBFSgo succ n (hashSetOf seed) seed.reverse seed

/-- The HashSet engine reproduces the list reference (a representation refinement:
    the visited set stands in for the `∉ acc` list scan). -/
theorem reachBFSgo_eq (succ : IssueId → List IssueId) :
    (n : Nat) → (vis : Std.HashSet IssueId) → (accRev frontier : List IssueId) →
    (∀ z, vis.contains z = true ↔ z ∈ accRev.reverse) →
    reachBFSgo succ n vis accRev frontier = reachBFSLgo succ n accRev.reverse frontier
  | 0, _, _, _, _ => rfl
  | n + 1, vis, accRev, frontier, hvis => by
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
    show reachBFSgo succ n ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).1
        (((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2 ++ accRev)
        ((frontier.flatMap succ).foldl bfsStepFn (vis, [])).2.reverse
       = reachBFSLgo succ n (accRev.reverse ++ bfsLayer succ accRev.reverse frontier)
           (bfsLayer succ accRev.reverse frontier)
    rw [reachBFSgo_eq succ n _ _ _ hp1, hlayer,
      List.reverse_append, List.reverse_reverse]

/-- **The shipped engine is `reachClosure`.** -/
theorem reachBFS_eq (succ : IssueId → List IssueId) (n : Nat) (seed : List IssueId)
    (hseed : seed.Nodup) : reachBFS succ n seed = reachClosure succ n seed := by
  unfold State.reachBFS
  rw [reachBFSgo_eq succ n (hashSetOf seed) seed.reverse seed
        (by intro z; rw [List.reverse_reverse]; rw [Std.HashSet.contains_iff_mem, mem_hashSetOf]),
      List.reverse_reverse]
  exact reachBFSL_eq succ n seed hseed

/-! ## Nodup of the adjacency seeds (so `reachBFS_eq` applies at the call sites)

The present edge set is duplicate-free (an OR-Set's present elements are distinct),
and the adjacency projections map an edge to one endpoint after fixing the other
endpoint and the kind, so the map is injective on the filtered edges — hence the
single-source/single-target adjacency lists are themselves duplicate-free. -/

theorem presentEdges_nodup (s : State) : s.presentEdges.Nodup := by
  show (s.edges.presentElements).Nodup
  rw [OrSet.presentElements_eq_keys_filter]
  exact List.Nodup.filter _ (AMap.keys_nodup s.edges.adds)

theorem blockersOf_nodup (s : State) (i : IssueId) : (s.blockersOf i).Nodup := by
  unfold State.blockersOf
  apply List.Nodup.map_on _ (List.Nodup.filter _ (presentEdges_nodup s))
  intro e1 h1 e2 h2 hfst
  rw [List.mem_filter] at h1 h2
  obtain ⟨hc1, hb1⟩ := of_decide_eq_true h1.2
  obtain ⟨hc2, hb2⟩ := of_decide_eq_true h2.2
  exact Prod.ext hfst (Prod.ext (hb1.trans hb2.symm) (hc1.trans hc2.symm))

theorem dependentsOf_nodup (s : State) (i : IssueId) : (s.dependentsOf i).Nodup := by
  unfold State.dependentsOf
  apply List.Nodup.map_on _ (List.Nodup.filter _ (presentEdges_nodup s))
  intro e1 h1 e2 h2 hsnd
  rw [List.mem_filter] at h1 h2
  obtain ⟨hc1, ha1⟩ := of_decide_eq_true h1.2
  obtain ⟨hc2, ha2⟩ := of_decide_eq_true h2.2
  exact Prod.ext (ha1.trans ha2.symm) (Prod.ext hsnd (hc1.trans hc2.symm))

theorem liveBlockersSucc_nodup (s : State) (i : IssueId) : (s.liveBlockersSucc i).Nodup :=
  List.Nodup.filter _ (blockersOf_nodup s i)

theorem kindSucc_nodup (s : State) (k : EdgeKind) (i : IssueId) : (s.kindSucc k i).Nodup := by
  unfold State.kindSucc
  apply List.Nodup.filter
  apply List.Nodup.map_on _ (List.Nodup.filter _ (presentEdges_nodup s))
  intro e1 h1 e2 h2 hsnd
  rw [List.mem_filter] at h1 h2
  obtain ⟨hc1, ha1⟩ := of_decide_eq_true h1.2
  obtain ⟨hc2, ha2⟩ := of_decide_eq_true h2.2
  exact Prod.ext (ha1.trans ha2.symm) (Prod.ext hsnd (hc1.trans hc2.symm))

/-! ## Membership characterization (unconditional — handles non-nodup seeds)

`reachBFS_eq` needs a nodup seed; the cycle diagnostics seed `precSucc v`, which
may repeat a node (a child that also blocks its parent). For those the
membership of `reachBFS` is what matters, and it agrees with `reachClosure`
regardless of seed duplicates — only the spec's *order* (a duplicate-free
prefix) needs the seed nodup, and a cycle check reads only membership. -/

/-- `reachStep` membership depends only on the accumulator's membership. -/
theorem reachStep_mem_congr {succ : IssueId → List IssueId} {X Y : List IssueId}
    (h : ∀ b, b ∈ X ↔ b ∈ Y) (a : IssueId) :
    a ∈ reachStep succ X ↔ a ∈ reachStep succ Y := by
  rw [mem_reachStep, mem_reachStep]
  constructor
  · rintro (ha | ⟨x, hx, hxa⟩)
    · exact Or.inl ((h a).mp ha)
    · exact Or.inr ⟨x, (h x).mp hx, hxa⟩
  · rintro (ha | ⟨x, hx, hxa⟩)
    · exact Or.inl ((h a).mpr ha)
    · exact Or.inr ⟨x, (h x).mpr hx, hxa⟩

/-- Hence iterating `reachStep` respects membership-equality of the seed. -/
theorem mem_iterateN_reachStep_congr {succ : IssueId → List IssueId} :
    (n : Nat) → {X Y : List IssueId} → (∀ b, b ∈ X ↔ b ∈ Y) →
    ∀ a, (a ∈ iterateN (reachStep succ) n X ↔ a ∈ iterateN (reachStep succ) n Y)
  | 0, _, _, h => h
  | n + 1, X, Y, h => by
    intro a
    show a ∈ iterateN (reachStep succ) n (reachStep succ X)
       ↔ a ∈ iterateN (reachStep succ) n (reachStep succ Y)
    exact mem_iterateN_reachStep_congr n (fun b => reachStep_mem_congr h b) a

/-- The frontier-engine membership invariant — like `reachBFSLgo_eq` but needs no
    nodup (membership of `acc ++ layer` matches `reachStep acc` unconditionally). -/
theorem mem_reachBFSLgo {succ : IssueId → List IssueId} (a : IssueId) :
    (n : Nat) → (acc below frontier : List IssueId) →
    acc = below ++ frontier → (∀ y ∈ below.flatMap succ, y ∈ acc) →
    (a ∈ reachBFSLgo succ n acc frontier ↔ a ∈ iterateN (reachStep succ) n acc)
  | 0, _, _, _, _, _ => Iff.rfl
  | n + 1, acc, below, frontier, hsplit, hclosed => by
    have hstepmem : ∀ b, b ∈ acc ++ bfsLayer succ acc frontier ↔ b ∈ reachStep succ acc := by
      intro b
      rw [List.mem_append, mem_bfsLayer, mem_reachStep]
      constructor
      · rintro (hb | ⟨hbf, _⟩)
        · exact Or.inl hb
        · obtain ⟨x, hx, hxb⟩ := List.mem_flatMap.mp hbf
          exact Or.inr ⟨x, by rw [hsplit, List.mem_append]; exact Or.inr hx, hxb⟩
      · rintro (hb | ⟨x, hx, hxb⟩)
        · exact Or.inl hb
        · by_cases hba : b ∈ acc
          · exact Or.inl hba
          · refine Or.inr ⟨?_, hba⟩
            rw [hsplit, List.mem_append] at hx
            rcases hx with hxb' | hxf
            · exact absurd (hclosed b (List.mem_flatMap.mpr ⟨x, hxb', hxb⟩)) hba
            · exact List.mem_flatMap.mpr ⟨x, hxf, hxb⟩
    show a ∈ reachBFSLgo succ n (acc ++ bfsLayer succ acc frontier) (bfsLayer succ acc frontier)
       ↔ a ∈ iterateN (reachStep succ) n (reachStep succ acc)
    rw [mem_reachBFSLgo a n (acc ++ bfsLayer succ acc frontier) acc (bfsLayer succ acc frontier) rfl
      (by
        intro y hy
        rw [List.mem_append]
        by_cases hyacc : y ∈ acc
        · exact Or.inl hyacc
        · refine Or.inr (mem_bfsLayer.mpr ⟨?_, hyacc⟩)
          rw [hsplit, List.flatMap_append, List.mem_append] at hy
          rcases hy with hb | hf
          · exact absurd (hclosed y hb) hyacc
          · exact hf)]
    exact mem_iterateN_reachStep_congr n hstepmem a

/-- `reachBFS` reproduces the list reference unconditionally (no nodup needed —
    `reachBFSgo_eq` is a pure representation refinement). -/
theorem reachBFS_eq_reachBFSL (succ : IssueId → List IssueId) (n : Nat) (seed : List IssueId) :
    reachBFS succ n seed = reachBFSL succ n seed := by
  unfold State.reachBFS State.reachBFSL
  rw [reachBFSgo_eq succ n (hashSetOf seed) seed.reverse seed
        (by intro z; rw [List.reverse_reverse, Std.HashSet.contains_iff_mem, mem_hashSetOf]),
      List.reverse_reverse]

/-- **Unconditional membership characterization**: the shipped engine reaches
    exactly `reachClosure`'s nodes, for any (possibly duplicated) seed. -/
theorem mem_reachBFS_iff {succ : IssueId → List IssueId} (n : Nat) (seed : List IssueId)
    (a : IssueId) : a ∈ reachBFS succ n seed ↔ a ∈ reachClosure succ n seed := by
  rw [reachBFS_eq_reachBFSL]
  show a ∈ reachBFSLgo succ n seed seed ↔ a ∈ iterateN (reachStep succ) n seed
  exact mem_reachBFSLgo a n seed [] seed (List.nil_append seed).symm
    (by intro y hy; rw [List.mem_flatMap] at hy; obtain ⟨x, hx, _⟩ := hy; exact nomatch hx)

end State

end Tl.Kernel
