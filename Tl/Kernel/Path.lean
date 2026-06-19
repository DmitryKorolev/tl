/-
`Tl.Kernel.Path` — `blocksPath`: a TOTAL witness-path extractor over the
`blocks` edge graph, the ordered companion to `why`'s reach+ set (the cycle
witnesses in `Cycles`/`SccProps` are sorted node-SETS, not ordered paths, so a
genuinely new function is needed here). `blocksPath s a b` returns an actual
edge path `[a, …, b]` exactly when `b` is reach+-reachable from `a` over present
`blocks` edges (`a` transitively blocks `b`), and `none` otherwise.

It is a frontier/worklist BFS that records a PARENT pointer AT DISCOVERY. A
single forward sweep (`parentSweep`) expands only the last layer each round
(`bfsLayer`, the frontier expansion — so it saturates early and never re-scans
the whole accumulator like the retired `reachStep` tower), and for every
newly-reached node stores one discovering predecessor (`IssueId`) and its
discovery depth. The witness path is then a single parent walk from `b` back to
a seed root (`parentWalk`), which strictly decreases depth and so terminates.
Structural recursion on the round/fuel count makes it total with no acyclicity
precondition; dangling endpoints are inert because `kindSucc` drops non-present
targets (ADR-0003 §5).

Correctness: `parentSweep_reach` pins the layer's membership to `reachClosure`
(so `blocksPath_isSome_iff` reuses the proved reach characterization);
`parentSweep_inv` is the parent invariant — each parent edge is real
(`parent w = u → w ∈ succ u`), depth strictly decreases along it, and a
parentless reached node is a seed root; and `parentWalk_chain` turns that into
reconstruction soundness (the walk is a real consecutive-edge chain from a seed
root to `cur`). The two public theorems `blocksPath_valid` /
`blocksPath_isSome_iff` keep their statements. Mirrors `mem_why_iff` (thm 10).

Direction (recorded): `kindSucc .Blocks i` is the present OUTGOING blocks
edges (the issues `i` blocks), consistent with `blocksSucc`/`unblocks`/critical;
`blocksPath a b` is therefore a chain `a` blocks … blocks `b`. The Mathlib
reachability/cardinality zone (ADR-0009) extends to this `Reach`/`ReachBFS`
dependent.

Cost (ADR-0023 tiering): the shipped engine is `parentSweepH` — a `Std.HashSet`
visited set (O(1)-amortized membership for the frontier filter), `Std.HashMap`
parent/depth maps (O(1)-amortized), and a REVERSED accumulator (per-round prepend
is O(layer), not an O(N) append), so each node's out-edges are expanded once, the
walk runs once, saturation is early (an empty frontier costs O(1) per remaining
round), and the whole sweep is O(V+E). The list/`AMap` `parentSweep` is the proof
REFERENCE (its `∉ acc`/`AMap.find` are O(N)); `parentSweepH_eq` proves the two
agree pointwise, so the soundness/completeness proofs transfer to the shipped
`blocksPath` unchanged (structure proved, wall-clock tested — ADR-0023; indexed-
view substrate — ADR-0024).
-/
import Tl.Kernel.Reach
import Tl.Kernel.ReachBFS
import Mathlib.Data.List.Chain

namespace Tl.Kernel

open Tl.Crdt

/-- `find` after folding a batch of `insert (val ·)` over a key list: a key in the
    batch reads its `val`, anything else falls through to the starting map. The
    `val` is a function of the key, so duplicate keys in the batch are harmless. -/
theorem find_foldl_insert {K V : Type _} [TotalOrd K] (val : K → V) :
    ∀ (l : List K) (m0 : AMap K V) (z : K),
      (l.foldl (fun m k => m.insert k (val k)) m0).find z =
        if z ∈ l then some (val z) else m0.find z
  | [], m0, z => by rw [List.foldl_nil, if_neg List.not_mem_nil]
  | a :: rest, m0, z => by
    show (rest.foldl (fun m k => m.insert k (val k)) (m0.insert a (val a))).find z = _
    rw [find_foldl_insert val rest (m0.insert a (val a)) z, AMap.find_insert]
    by_cases hz : z ∈ rest
    · rw [if_pos hz, if_pos (List.mem_cons.mpr (Or.inr hz))]
    · rw [if_neg hz]
      by_cases hza : z = a
      · rw [if_pos hza, if_pos (List.mem_cons.mpr (Or.inl hza)), hza]
      · rw [if_neg hza, if_neg (fun h => (List.mem_cons.mp h).elim hza hz)]

/-! ## O(V+E) parent-recording frontier BFS

The path is extracted from a parent map recorded *at discovery* during a single
frontier sweep: each round expands only the last layer, and every newly-reached
node remembers the frontier predecessor that found it (one `IssueId`, not a whole
path) together with the round it was found (`depth`). The witness path to `b` is
then a one-shot parent walk from `b` back to a seed root — strictly decreasing
`depth`, so it terminates. This replaces the materialized full-path map (whose
per-node `path ++ [node]` append was a further O(N²) over the shared closure). -/

/-- A discovering frontier predecessor of `y`: the first frontier node that lists
    `y` as a successor. -/
def parentOf (succ : IssueId → List IssueId) (frontier : List IssueId) (y : IssueId) :
    Option IssueId :=
  frontier.find? (fun u => decide (y ∈ succ u))

/-- A single forward sweep recording a parent map (`IssueId → IssueId`, at
    discovery) and a discovery-depth map. Carries `(acc, frontier, parent, depth)`:
    `acc` is the round-`k` reachable layer (grown by `bfsLayer`, the frontier
    expansion, so `= reachClosure succ k seed`); `frontier` is the nodes added last
    round; `parent`/`depth` send every node reached so far to a discovering
    predecessor / its round. Seed roots are at depth 0 with no parent entry. -/
def parentSweep (succ : IssueId → List IssueId) (seed : List IssueId) :
    Nat → List IssueId × List IssueId × AMap IssueId IssueId × AMap IssueId Nat
  | 0 => (seed, seed, AMap.empty, seed.foldl (fun m y => m.insert y 0) AMap.empty)
  | k + 1 =>
    let prev := parentSweep succ seed k
    let layer := State.bfsLayer succ prev.1 prev.2.1
    (prev.1 ++ layer, layer,
     layer.foldl (fun m y => m.insert y ((parentOf succ prev.2.1 y).getD y)) prev.2.2.1,
     layer.foldl (fun m y => m.insert y (k + 1)) prev.2.2.2)

/-- Reconstruct the witness path to `cur` by walking the parent map back to a seed
    root, prepending as it goes (so the result reads root → … → `cur`). Fuel-total;
    `depth cur` strictly bounds the walk length. -/
def parentWalk (parent : AMap IssueId IssueId) : Nat → IssueId → List IssueId → List IssueId
  | 0, cur, acc => cur :: acc
  | f + 1, cur, acc =>
    match parent.find cur with
    | none => cur :: acc
    | some u => parentWalk parent f u (cur :: acc)

/-- The sweep's reachability projection: its accumulator has exactly
    `reachClosure`'s membership, and it splits as `below ++ frontier` with the
    pre-frontier part `succ`-closed (the frontier invariant `bfsLayer` needs). -/
theorem parentSweep_reach (succ : IssueId → List IssueId) (seed : List IssueId) :
    (n : Nat) →
    (∀ z, z ∈ (parentSweep succ seed n).1 ↔ z ∈ State.reachClosure succ n seed)
    ∧ (∃ below, (parentSweep succ seed n).1 = below ++ (parentSweep succ seed n).2.1
        ∧ ∀ y ∈ below.flatMap succ, y ∈ (parentSweep succ seed n).1)
  | 0 => by
    refine ⟨fun z => Iff.rfl, [], (List.nil_append seed).symm, ?_⟩
    intro y hy; rw [List.mem_flatMap] at hy; obtain ⟨x, hx, _⟩ := hy; exact nomatch hx
  | k + 1 => by
    obtain ⟨ihmem, below, hsplit, hclosed⟩ := parentSweep_reach succ seed k
    set acc := (parentSweep succ seed k).1 with hacc
    set fr := (parentSweep succ seed k).2.1 with hfr
    have hfst : (parentSweep succ seed (k + 1)).1 = acc ++ State.bfsLayer succ acc fr := rfl
    have hfrnt : (parentSweep succ seed (k + 1)).2.1 = State.bfsLayer succ acc fr := rfl
    -- membership of the new accumulator matches one `reachStep`
    have hstepmem : ∀ z, z ∈ acc ++ State.bfsLayer succ acc fr ↔ z ∈ State.reachStep succ acc := by
      intro z
      rw [List.mem_append, State.mem_bfsLayer, mem_reachStep]
      constructor
      · rintro (hz | ⟨hzf, _⟩)
        · exact Or.inl hz
        · obtain ⟨x, hx, hxz⟩ := List.mem_flatMap.mp hzf
          exact Or.inr ⟨x, by rw [hsplit, List.mem_append]; exact Or.inr hx, hxz⟩
      · rintro (hz | ⟨x, hx, hxz⟩)
        · exact Or.inl hz
        · by_cases hza : z ∈ acc
          · exact Or.inl hza
          · refine Or.inr ⟨?_, hza⟩
            rw [hsplit, List.mem_append] at hx
            rcases hx with hb | hf
            · exact absurd (hclosed z (List.mem_flatMap.mpr ⟨x, hb, hxz⟩)) hza
            · exact List.mem_flatMap.mpr ⟨x, hf, hxz⟩
    refine ⟨?_, acc, hfst, ?_⟩
    · intro z
      rw [hfst, hstepmem z, reachClosure_succ]
      exact State.reachStep_mem_congr (fun b => ihmem b) z
    · intro y hy
      rw [hfst, List.mem_append]
      by_cases hya : y ∈ acc
      · exact Or.inl hya
      · refine Or.inr (State.mem_bfsLayer.mpr ⟨?_, hya⟩)
        rw [hsplit, List.flatMap_append, List.mem_append] at hy
        rcases hy with hb | hf
        · exact absurd (hclosed y hb) hya
        · exact hf

/-- A newly-reached layer node has a real discovering predecessor in the frontier. -/
theorem parentOf_layer (succ : IssueId → List IssueId) (acc fr : List IssueId) (y : IssueId)
    (hy : y ∈ State.bfsLayer succ acc fr) : ∃ u, parentOf succ fr y = some u ∧ y ∈ succ u := by
  rw [State.mem_bfsLayer] at hy
  obtain ⟨u0, hu0, hyu0⟩ := List.mem_flatMap.mp hy.1
  unfold parentOf
  cases h : fr.find? (fun u => decide (y ∈ succ u)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by rw [decide_eq_true_eq]; exact hyu0) (h u0 hu0)
  | some u' =>
    have hp := List.find?_some h
    exact ⟨u', rfl, of_decide_eq_true hp⟩

/-- The parent-map invariant after `n` rounds: every parented node remembers a
    real predecessor at a strictly smaller depth; every accumulator node has a
    depth; a parentless accumulator node is a seed root; seeds are roots; the
    frontier sits at depth `n`. The depth strictly decreasing along parents is
    what makes the reconstruction walk terminate at a seed root. -/
theorem parentSweep_inv (succ : IssueId → List IssueId) (seed : List IssueId) :
    (n : Nat) →
    (∀ u ∈ (parentSweep succ seed n).2.1, (parentSweep succ seed n).2.2.2.find u = some n)
    ∧ (∀ w u, (parentSweep succ seed n).2.2.1.find w = some u → w ∈ succ u)
    ∧ (∀ w u, (parentSweep succ seed n).2.2.1.find w = some u →
        ∃ dw du, (parentSweep succ seed n).2.2.2.find w = some dw
          ∧ (parentSweep succ seed n).2.2.2.find u = some du ∧ du < dw)
    ∧ (∀ w ∈ (parentSweep succ seed n).1, ((parentSweep succ seed n).2.2.2.find w).isSome)
    ∧ (∀ w ∈ (parentSweep succ seed n).1,
        (parentSweep succ seed n).2.2.1.find w = none → w ∈ seed)
    ∧ (∀ w u, (parentSweep succ seed n).2.2.1.find w = some u → u ∈ (parentSweep succ seed n).1)
    ∧ (∀ w ∈ seed, (parentSweep succ seed n).2.2.1.find w = none)
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      show (seed.foldl (fun m y => m.insert y 0) AMap.empty).find u = some 0
      rw [find_foldl_insert (fun _ => 0) seed AMap.empty u, if_pos (show u ∈ seed from hu)]
    · intro w u hw; rw [show (parentSweep succ seed 0).2.2.1 = AMap.empty from rfl, AMap.find_empty] at hw; exact nomatch hw
    · intro w u hw; rw [show (parentSweep succ seed 0).2.2.1 = AMap.empty from rfl, AMap.find_empty] at hw; exact nomatch hw
    · intro w hw
      show ((seed.foldl (fun m y => m.insert y 0) AMap.empty).find w).isSome
      rw [find_foldl_insert (fun _ => 0) seed AMap.empty w, if_pos (show w ∈ seed from hw)]; rfl
    · intro w hw _; exact hw
    · intro w u hw; rw [show (parentSweep succ seed 0).2.2.1 = AMap.empty from rfl, AMap.find_empty] at hw; exact nomatch hw
    · intro w _; rfl
  | k + 1 => by
    obtain ⟨ihF, ihR, ihD, ihT, ihRoot, ihAccP, ihSeed⟩ := parentSweep_inv succ seed k
    set acc := (parentSweep succ seed k).1 with hacc
    set fr := (parentSweep succ seed k).2.1 with hfr
    set par := (parentSweep succ seed k).2.2.1 with hpar
    set dep := (parentSweep succ seed k).2.2.2 with hdep
    set layer := State.bfsLayer succ acc fr with hlayer
    have hpar' : (parentSweep succ seed (k + 1)).2.2.1
        = layer.foldl (fun m y => m.insert y ((parentOf succ fr y).getD y)) par := rfl
    have hdep' : (parentSweep succ seed (k + 1)).2.2.2
        = layer.foldl (fun m y => m.insert y (k + 1)) dep := rfl
    have hfrnt : (parentSweep succ seed (k + 1)).2.1 = layer := rfl
    have hfst : (parentSweep succ seed (k + 1)).1 = acc ++ layer := rfl
    have hparfind : ∀ z, (parentSweep succ seed (k + 1)).2.2.1.find z
        = if z ∈ layer then some ((parentOf succ fr z).getD z) else par.find z := fun z => by
      rw [hpar']; exact find_foldl_insert (fun y => (parentOf succ fr y).getD y) layer par z
    have hdepfind : ∀ z, (parentSweep succ seed (k + 1)).2.2.2.find z
        = if z ∈ layer then some (k + 1) else dep.find z := fun z => by
      rw [hdep']; exact find_foldl_insert (fun _ => k + 1) layer dep z
    -- layer is disjoint from acc, and fr ⊆ acc
    have hlayer_notacc : ∀ z ∈ layer, z ∉ acc := fun z hz => (State.mem_bfsLayer.mp hz).2
    have hfr_acc : ∀ u ∈ fr, u ∈ acc := by
      obtain ⟨_, below, hsplit, _⟩ := parentSweep_reach succ seed k
      intro u hu; rw [hacc, hsplit, List.mem_append]; exact Or.inr hu
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- frontier' = layer at depth k+1
      intro u hu; rw [hfrnt] at hu; rw [hdepfind u, if_pos hu]
    · -- real edge
      intro w u hw
      rw [hparfind w] at hw
      by_cases hwl : w ∈ layer
      · rw [if_pos hwl] at hw
        obtain ⟨u', hu', hwu'⟩ := parentOf_layer succ acc fr w hwl
        rw [hu', Option.getD_some, Option.some.injEq] at hw; exact hw ▸ hwu'
      · rw [if_neg hwl] at hw; exact ihR w u hw
    · -- depth strictly decreases along the parent edge
      intro w u hw
      rw [hparfind w] at hw
      by_cases hwl : w ∈ layer
      · rw [if_pos hwl] at hw
        obtain ⟨u', hu', _⟩ := parentOf_layer succ acc fr w hwl
        rw [hu', Option.getD_some, Option.some.injEq] at hw
        subst hw
        have hu'fr : u' ∈ fr := List.mem_of_find?_eq_some hu'
        refine ⟨k + 1, k, ?_, ?_, Nat.lt_succ_self k⟩
        · rw [hdepfind w, if_pos hwl]
        · rw [hdepfind u', if_neg (fun hc => hlayer_notacc u' hc (hfr_acc u' hu'fr)), ihF u' hu'fr]
      · rw [if_neg hwl] at hw
        obtain ⟨dw, du, hdw, hdu, hlt⟩ := ihD w u hw
        have huacc : u ∈ acc := ihAccP w u hw
        refine ⟨dw, du, ?_, ?_, hlt⟩
        · rw [hdepfind w, if_neg hwl]; exact hdw
        · rw [hdepfind u, if_neg (fun hc => hlayer_notacc u hc huacc)]; exact hdu
    · -- depth total over the accumulator
      intro w hw
      rw [hfst, List.mem_append] at hw
      rcases hw with hwa | hwl
      · have hwnl : w ∉ layer := fun hc => hlayer_notacc w hc hwa
        rw [hdepfind w, if_neg hwnl]; exact ihT w hwa
      · rw [hdepfind w, if_pos hwl]; rfl
    · -- a parentless accumulator node is a seed root
      intro w hw hnone
      rw [hfst, List.mem_append] at hw
      rcases hw with hwa | hwl
      · have hwnl : w ∉ layer := fun hc => hlayer_notacc w hc hwa
        rw [hparfind w, if_neg hwnl] at hnone
        exact ihRoot w hwa hnone
      · rw [hparfind w, if_pos hwl] at hnone
        obtain ⟨u', hu', _⟩ := parentOf_layer succ acc fr w hwl
        rw [hu', Option.getD_some] at hnone
        exact absurd hnone (Option.some_ne_none _)
    · -- the parent stays in the accumulator
      intro w u hw
      rw [hparfind w] at hw
      rw [hfst, List.mem_append]
      by_cases hwl : w ∈ layer
      · rw [if_pos hwl] at hw
        obtain ⟨u', hu', _⟩ := parentOf_layer succ acc fr w hwl
        rw [hu', Option.getD_some, Option.some.injEq] at hw
        subst hw
        exact Or.inl (hfr_acc u' (List.mem_of_find?_eq_some hu'))
      · rw [if_neg hwl] at hw
        exact Or.inl (ihAccP w u hw)
    · -- seeds are roots
      intro w hw
      have hwacc : w ∈ acc := by
        obtain ⟨ihmem, _⟩ := parentSweep_reach succ seed k
        exact (ihmem w).mpr (reachClosure_mono succ seed (Nat.zero_le k)
          (show w ∈ State.reachClosure succ 0 seed from hw))
      have hwnl : w ∉ layer := fun hc => hlayer_notacc w hc hwacc
      rw [hparfind w, if_neg hwnl]; exact ihSeed w hw

/-- **Reconstruction soundness**: walking the parent map from a reachable `cur`
    (with fuel above its depth) yields a real `succ`-edge chain that starts at a
    seed root and ends at `cur`, prepended to a compatible chain `acc0`. The depth
    strictly decreases along each parent step, so the walk reaches a root. -/
theorem parentWalk_chain (succ : IssueId → List IssueId) (seed : List IssueId) (N : Nat) :
    (fuel : Nat) → (cur : IssueId) → (acc0 : List IssueId) →
    cur ∈ (parentSweep succ seed N).1 →
    (∀ d, (parentSweep succ seed N).2.2.2.find cur = some d → d < fuel) →
    List.IsChain (fun u v => v ∈ succ u) acc0 →
    (∀ w, acc0.head? = some w → w ∈ succ cur) →
    parentWalk (parentSweep succ seed N).2.2.1 fuel cur acc0 ≠ []
    ∧ (parentWalk (parentSweep succ seed N).2.2.1 fuel cur acc0).getLast? = (cur :: acc0).getLast?
    ∧ (∃ r, (parentWalk (parentSweep succ seed N).2.2.1 fuel cur acc0).head? = some r ∧ r ∈ seed)
    ∧ List.IsChain (fun u v => v ∈ succ u) (parentWalk (parentSweep succ seed N).2.2.1 fuel cur acc0)
  | 0, cur, acc0, hcur, hfuel, _, _ => by
    obtain ⟨_, _, _, ihT, _, _, _⟩ := parentSweep_inv succ seed N
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (ihT cur hcur)
    exact absurd (hfuel d hd) (Nat.not_lt_zero d)
  | f + 1, cur, acc0, hcur, hfuel, hchain, hhead => by
    obtain ⟨_, ihR, ihD, _, ihRoot, ihAccP, _⟩ := parentSweep_inv succ seed N
    cases hpar : (parentSweep succ seed N).2.2.1.find cur with
    | none =>
      have hpw : parentWalk (parentSweep succ seed N).2.2.1 (f + 1) cur acc0 = cur :: acc0 := by
        show (match (parentSweep succ seed N).2.2.1.find cur with
              | none => cur :: acc0
              | some u => parentWalk (parentSweep succ seed N).2.2.1 f u (cur :: acc0)) = cur :: acc0
        rw [hpar]
      rw [hpw]
      refine ⟨List.cons_ne_nil _ _, rfl, ⟨cur, rfl, ihRoot cur hcur hpar⟩, ?_⟩
      rw [List.isChain_cons]
      refine ⟨fun y hy => ?_, hchain⟩
      rw [Option.mem_def] at hy; exact hhead y hy
    | some u =>
      have hcuru : cur ∈ succ u := ihR cur u hpar
      have huacc : u ∈ (parentSweep succ seed N).1 := ihAccP cur u hpar
      obtain ⟨dw, du, hdw, hdu, hlt⟩ := ihD cur u hpar
      have hpw : parentWalk (parentSweep succ seed N).2.2.1 (f + 1) cur acc0
              = parentWalk (parentSweep succ seed N).2.2.1 f u (cur :: acc0) := by
        show (match (parentSweep succ seed N).2.2.1.find cur with
              | none => cur :: acc0
              | some u' => parentWalk (parentSweep succ seed N).2.2.1 f u' (cur :: acc0)) = _
        rw [hpar]
      rw [hpw]
      have hdufuel : du < f := Nat.lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp (hfuel dw hdw))
      have hchain' : List.IsChain (fun u v => v ∈ succ u) (cur :: acc0) := by
        rw [List.isChain_cons]
        refine ⟨fun y hy => ?_, hchain⟩
        rw [Option.mem_def] at hy; exact hhead y hy
      exact parentWalk_chain succ seed N f u (cur :: acc0) huacc
        (fun d hd => by rw [hdu] at hd; injection hd with he; exact he ▸ hdufuel)
        hchain'
        (fun w hw => by rw [List.head?_cons, Option.some.injEq] at hw; exact hw ▸ hcuru)
        |>.imp id (fun ⟨hlast, hrest⟩ => ⟨by rw [hlast, List.getLast?_cons_cons], hrest⟩)

/-- Every recorded discovery depth is within the round count, so the
    reconstruction walk (run with `fuel + 1` steps) always outlasts it. -/
theorem parentSweep_depth_bound (succ : IssueId → List IssueId) (seed : List IssueId) :
    (n : Nat) → ∀ w d, (parentSweep succ seed n).2.2.2.find w = some d → d ≤ n
  | 0, w, d, hw => by
    rw [show (parentSweep succ seed 0).2.2.2
          = seed.foldl (fun m y => m.insert y 0) AMap.empty from rfl,
      find_foldl_insert (fun _ => 0) seed AMap.empty w] at hw
    by_cases hws : w ∈ seed
    · rw [if_pos hws, Option.some.injEq] at hw; subst hw; exact Nat.le_refl 0
    · rw [if_neg hws, AMap.find_empty] at hw; exact nomatch hw
  | k + 1, w, d, hw => by
    rw [show (parentSweep succ seed (k + 1)).2.2.2
          = (State.bfsLayer succ (parentSweep succ seed k).1 (parentSweep succ seed k).2.1).foldl
              (fun m y => m.insert y (k + 1)) (parentSweep succ seed k).2.2.2 from rfl,
      find_foldl_insert (fun _ => k + 1) _ _ w] at hw
    by_cases hwl : w ∈ State.bfsLayer succ (parentSweep succ seed k).1 (parentSweep succ seed k).2.1
    · rw [if_pos hwl, Option.some.injEq] at hw; subst hw; exact Nat.le_refl _
    · rw [if_neg hwl] at hw
      exact Nat.le_succ_of_le (parentSweep_depth_bound succ seed k w d hw)

/-- The witness path to `cur` after a `fuel`-round parent sweep (`none` if `cur`
    is not reached). The reconstruction walk gets `fuel + 1` steps so it reaches
    the seed root from any reached node (whose discovery depth is ≤ `fuel`). -/
def bfsPath (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) : Option (List IssueId) :=
  if cur ∈ (parentSweep succ seed fuel).1
  then some (parentWalk (parentSweep succ seed fuel).2.2.1 (fuel + 1) cur [])
  else none

/-- **Soundness**: a returned path is real — nonempty, ends at `cur`, starts at a
    `seed` member, every consecutive pair a `succ`-edge. -/
theorem bfsPath_sound (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) (p : List IssueId) (h : bfsPath succ seed fuel cur = some p) :
    p ≠ [] ∧ p.getLast? = some cur ∧
    (∀ h, p.head? = some h → h ∈ seed) ∧
    List.IsChain (fun u v => v ∈ succ u) p := by
  unfold bfsPath at h
  by_cases hcur : cur ∈ (parentSweep succ seed fuel).1
  · rw [if_pos hcur, Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, ihT, _, _, _⟩ := parentSweep_inv succ seed fuel
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (ihT cur hcur)
    obtain ⟨hne, hlast, ⟨r, hr, hrseed⟩, hchain⟩ :=
      parentWalk_chain succ seed fuel (fuel + 1) cur [] hcur
        (fun d' hd' => by
          rw [hd] at hd'; injection hd' with he
          exact he ▸ Nat.lt_succ_of_le (parentSweep_depth_bound succ seed fuel cur d hd))
        List.IsChain.nil (fun w hw => nomatch hw)
    refine ⟨hne, ?_, ?_, hchain⟩
    · rw [hlast]; rfl
    · intro h hh; rw [hr, Option.some.injEq] at hh; exact hh ▸ hrseed
  · rw [if_neg hcur] at h; exact nomatch h

/-- **Completeness**: a node in the round-`k` closure has a witness path. -/
theorem bfsPath_complete (succ : IssueId → List IssueId) (seed : List IssueId)
    (k : Nat) (cur : IssueId) (h : cur ∈ State.reachClosure succ k seed) :
    (bfsPath succ seed k cur).isSome := by
  unfold bfsPath
  rw [if_pos (((parentSweep_reach succ seed k).1 cur).mpr h)]
  rfl

/-! ## True O(V+E): the shipped `Std.HashSet` / `Std.HashMap` engine

`parentSweep` above is the list/`AMap` proof REFERENCE (its `∉ acc` test and
`AMap.find` are O(N), and `acc ++ layer` per round is O(N²)). The shipped
`parentSweepH` carries a `Std.HashSet` visited set (O(1)-amortized membership for
the frontier filter), `Std.HashMap` parent/depth maps (O(1)-amortized), and a
REVERSED accumulator (per-round prepend is O(layer), not the O(N) append), so the
whole sweep is O(V+E). `parentSweepH_eq` proves it agrees pointwise with
`parentSweep`, so the soundness/completeness proofs transfer to `blocksPath`
unchanged (ADR-0024 indexed-view substrate; ADR-0023 tiering: structure proved,
wall-clock tested). -/

/-- The hash parent walk — `parentWalk` with a `Std.HashMap` lookup. -/
def parentWalkH (parent : Std.HashMap IssueId IssueId) : Nat → IssueId → List IssueId → List IssueId
  | 0, cur, acc => cur :: acc
  | f + 1, cur, acc =>
    match parent[cur]? with
    | none => cur :: acc
    | some u => parentWalkH parent f u (cur :: acc)

theorem parentWalkH_eq (parentH : Std.HashMap IssueId IssueId) (parentL : AMap IssueId IssueId)
    (h : ∀ z, parentH[z]? = parentL.find z) :
    ∀ (fuel : Nat) (cur : IssueId) (acc : List IssueId),
      parentWalkH parentH fuel cur acc = parentWalk parentL fuel cur acc
  | 0, _, _ => rfl
  | f + 1, cur, acc => by
    show (match parentH[cur]? with
          | none => cur :: acc
          | some u => parentWalkH parentH f u (cur :: acc))
       = (match parentL.find cur with
          | none => cur :: acc
          | some u => parentWalk parentL f u (cur :: acc))
    rw [h cur]
    cases parentL.find cur with
    | none => rfl
    | some u => exact parentWalkH_eq parentH parentL h f u (cur :: acc)

/-- The frontier layer via a `Std.HashSet` membership test. -/
def bfsLayerH (succ : IssueId → List IssueId) (visited : Std.HashSet IssueId)
    (fr : List IssueId) : List IssueId :=
  dedup ((fr.flatMap succ).filter (fun y => !visited.contains y))

theorem bfsLayerH_eq (succ : IssueId → List IssueId) (visited : Std.HashSet IssueId)
    (acc fr : List IssueId) (h : ∀ z, visited.contains z = decide (z ∈ acc)) :
    bfsLayerH succ visited fr = State.bfsLayer succ acc fr := by
  unfold bfsLayerH State.bfsLayer
  congr 1
  apply List.filter_congr
  intro y _
  rw [h y, decide_not]

/-- The shipped O(V+E) sweep: `(accRev, frontier, parent, depth, visited)` —
    `accRev` is the reversed reachable list, `visited` mirrors its membership for
    the O(1) frontier filter, `parent`/`depth` are `Std.HashMap`s. -/
def parentSweepH (succ : IssueId → List IssueId) (seed : List IssueId) :
    Nat → List IssueId × List IssueId × Std.HashMap IssueId IssueId
        × Std.HashMap IssueId Nat × Std.HashSet IssueId
  | 0 => (seed.reverse, seed, ∅, seed.foldl (fun m y => m.insert y 0) ∅, hashSetOf seed)
  | k + 1 =>
    let p := parentSweepH succ seed k
    let layer := bfsLayerH succ p.2.2.2.2 p.2.1
    (layer.reverse ++ p.1, layer,
     layer.foldl (fun m y => m.insert y ((parentOf succ p.2.1 y).getD y)) p.2.2.1,
     layer.foldl (fun m y => m.insert y (k + 1)) p.2.2.2.1,
     layer.foldl (fun s y => s.insert y) p.2.2.2.2)

/-- The shipped sweep agrees pointwise with the list/`AMap` reference. -/
theorem parentSweepH_eq (succ : IssueId → List IssueId) (seed : List IssueId) :
    (n : Nat) →
    (parentSweepH succ seed n).1.reverse = (parentSweep succ seed n).1
    ∧ (parentSweepH succ seed n).2.1 = (parentSweep succ seed n).2.1
    ∧ (∀ z, (parentSweepH succ seed n).2.2.1[z]? = (parentSweep succ seed n).2.2.1.find z)
    ∧ (∀ z, (parentSweepH succ seed n).2.2.2.1[z]? = (parentSweep succ seed n).2.2.2.find z)
    ∧ (∀ z, (parentSweepH succ seed n).2.2.2.2.contains z = decide (z ∈ (parentSweep succ seed n).1))
  | 0 => by
    refine ⟨List.reverse_reverse seed, rfl, ?_, ?_, ?_⟩
    · intro z
      rw [show (parentSweepH succ seed 0).2.2.1 = (∅ : Std.HashMap IssueId IssueId) from rfl,
        show (parentSweep succ seed 0).2.2.1 = AMap.empty from rfl,
        Std.HashMap.getElem?_empty, AMap.find_empty]
    · intro z
      rw [show (parentSweepH succ seed 0).2.2.2.1
            = seed.foldl (fun m y => m.insert y 0) ∅ from rfl,
        show (parentSweep succ seed 0).2.2.2
            = seed.foldl (fun m y => m.insert y 0) AMap.empty from rfl,
        getElem?_foldl_insert_keys (fun _ => 0) seed ∅ z,
        find_foldl_insert (fun _ => 0) seed AMap.empty z]
      by_cases hz : z ∈ seed
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz, Std.HashMap.getElem?_empty, AMap.find_empty]
    · intro z
      rw [show (parentSweepH succ seed 0).2.2.2.2 = hashSetOf seed from rfl,
        show (parentSweep succ seed 0).1 = seed from rfl, Bool.eq_iff_iff, decide_eq_true_eq,
        Std.HashSet.contains_iff_mem, mem_hashSetOf]
  | k + 1 => by
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := parentSweepH_eq succ seed k
    set accL := (parentSweep succ seed k).1 with haccL
    set frL := (parentSweep succ seed k).2.1 with hfrL
    have hlayer : bfsLayerH succ (parentSweepH succ seed k).2.2.2.2 (parentSweepH succ seed k).2.1
                = State.bfsLayer succ accL frL := by
      rw [ih2, bfsLayerH_eq succ (parentSweepH succ seed k).2.2.2.2 accL frL ih5]
    -- the (k+1) projections
    have hH1 : (parentSweepH succ seed (k + 1)).1
        = (bfsLayerH succ (parentSweepH succ seed k).2.2.2.2 (parentSweepH succ seed k).2.1).reverse
            ++ (parentSweepH succ seed k).1 := rfl
    have hH2 : (parentSweepH succ seed (k + 1)).2.1
        = bfsLayerH succ (parentSweepH succ seed k).2.2.2.2 (parentSweepH succ seed k).2.1 := rfl
    have hH3 : (parentSweepH succ seed (k + 1)).2.2.1
        = (bfsLayerH succ (parentSweepH succ seed k).2.2.2.2 (parentSweepH succ seed k).2.1).foldl
            (fun m y => m.insert y ((parentOf succ (parentSweepH succ seed k).2.1 y).getD y))
            (parentSweepH succ seed k).2.2.1 := rfl
    have hH4 : (parentSweepH succ seed (k + 1)).2.2.2.1
        = (bfsLayerH succ (parentSweepH succ seed k).2.2.2.2 (parentSweepH succ seed k).2.1).foldl
            (fun m y => m.insert y (k + 1)) (parentSweepH succ seed k).2.2.2.1 := rfl
    have hH5 : (parentSweepH succ seed (k + 1)).2.2.2.2
        = (bfsLayerH succ (parentSweepH succ seed k).2.2.2.2 (parentSweepH succ seed k).2.1).foldl
            (fun s y => s.insert y) (parentSweepH succ seed k).2.2.2.2 := rfl
    have hL1 : (parentSweep succ seed (k + 1)).1 = accL ++ State.bfsLayer succ accL frL := rfl
    have hL2 : (parentSweep succ seed (k + 1)).2.1 = State.bfsLayer succ accL frL := rfl
    have hL3 : (parentSweep succ seed (k + 1)).2.2.1
        = (State.bfsLayer succ accL frL).foldl
            (fun m y => m.insert y ((parentOf succ frL y).getD y)) (parentSweep succ seed k).2.2.1 := rfl
    have hL4 : (parentSweep succ seed (k + 1)).2.2.2
        = (State.bfsLayer succ accL frL).foldl
            (fun m y => m.insert y (k + 1)) (parentSweep succ seed k).2.2.2 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hH1, hL1, List.reverse_append, List.reverse_reverse, hlayer, ih1]
    · rw [hH2, hL2, hlayer]
    · intro z
      rw [hH3, hL3, hlayer, ih2,
        getElem?_foldl_insert_keys (fun y => (parentOf succ frL y).getD y) _ _ z,
        find_foldl_insert (fun y => (parentOf succ frL y).getD y) _ _ z]
      by_cases hz : z ∈ State.bfsLayer succ accL frL
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz]; exact ih3 z
    · intro z
      rw [hH4, hL4, hlayer, getElem?_foldl_insert_keys (fun _ => k + 1) _ _ z,
        find_foldl_insert (fun _ => k + 1) _ _ z]
      by_cases hz : z ∈ State.bfsLayer succ accL frL
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz]; exact ih4 z
    · intro z
      rw [hH5, hL1, hlayer, Bool.eq_iff_iff, decide_eq_true_eq, Std.HashSet.contains_iff_mem,
        mem_foldl_insert, List.mem_append]
      rw [← Std.HashSet.contains_iff_mem, ih5 z, decide_eq_true_eq]
      exact Or.comm

/-- The shipped witness-path extractor: the parent walk over the hash sweep. -/
def bfsPathH (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) : Option (List IssueId) :=
  if (parentSweepH succ seed fuel).2.2.2.2.contains cur
  then some (parentWalkH (parentSweepH succ seed fuel).2.2.1 (fuel + 1) cur [])
  else none

theorem bfsPathH_eq (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) : bfsPathH succ seed fuel cur = bfsPath succ seed fuel cur := by
  unfold bfsPathH bfsPath
  obtain ⟨_, _, hpar, _, hvis⟩ := parentSweepH_eq succ seed fuel
  by_cases hc : cur ∈ (parentSweep succ seed fuel).1
  · rw [if_pos (show (parentSweepH succ seed fuel).2.2.2.2.contains cur = true by
        rw [hvis cur, decide_eq_true_eq]; exact hc),
      if_pos hc,
      parentWalkH_eq (parentSweepH succ seed fuel).2.2.1 (parentSweep succ seed fuel).2.2.1 hpar]
  · rw [if_neg (show ¬ (parentSweepH succ seed fuel).2.2.2.2.contains cur = true by
        rw [hvis cur, decide_eq_true_eq]; exact hc),
      if_neg hc]

namespace State

/-- `blocksPath s a b` (ADR-0004 thm 10 companion): a witness path `[a, …, b]`
    of present `blocks` edges (`a` transitively blocks `b`) when `b` is
    reach+-reachable from `a`, else `none`. Total on cyclic and dangling graphs.
    The seed is `a`'s direct blocks-successors and the bound is `|presentIssues|`
    (the saturating layer), so it agrees with `reachClosure`/`why`'s reach+. -/
def blocksPath (s : State) (a b : IssueId) : Option (List IssueId) :=
  (bfsPathH (s.kindSucc .Blocks) (s.kindSucc .Blocks a)
      s.presentIssues.length b).map (a :: ·)

/-- **`blocksPath` path validity**: a returned path is a real `blocks`-edge path
    `a ⇝ b` — head `a`, last `b`, every consecutive pair connected by a present
    `blocks` edge. -/
theorem blocksPath_valid (s : State) (a b : IssueId) (p : List IssueId)
    (h : s.blocksPath a b = some p) :
    p.head? = some a ∧ p.getLast? = some b ∧
      List.IsChain (fun u v => v ∈ s.kindSucc .Blocks u) p := by
  unfold State.blocksPath at h
  rw [bfsPathH_eq, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, hpe⟩ := h
  obtain ⟨hne, hlast, hhead, hchain⟩ := bfsPath_sound _ _ _ _ _ hq
  subst hpe
  refine ⟨rfl, ?_, ?_⟩
  · change ([a] ++ q).getLast? = some b
    rw [List.getLast?_append_of_ne_nil _ hne]; exact hlast
  · rw [List.isChain_cons]
    refine ⟨?_, hchain⟩
    intro y hy
    rw [Option.mem_def] at hy
    exact hhead y hy

/-- **`blocksPath` reachability** (mirrors `mem_why_iff`, ADR-0004 thm 10): a
    path exists iff `b` is reach+-reachable from `a` over present `blocks` edges —
    i.e. reachable from a direct `blocks`-successor of `a`. Total on
    cyclic/dangling graphs. -/
theorem blocksPath_isSome_iff (s : State) (a b : IssueId) :
    (s.blocksPath a b).isSome ↔
      ∃ c ∈ s.kindSucc .Blocks a,
        Relation.ReflTransGen (StepRel (s.kindSucc .Blocks)) c b := by
  have hsU : s.kindSucc .Blocks a ⊆ s.presentIssues := kindSucc_subset_present s .Blocks a
  have hU : ∀ x ∈ s.presentIssues, s.kindSucc .Blocks x ⊆ s.presentIssues :=
    fun x _ => kindSucc_subset_present s .Blocks x
  constructor
  · intro hs
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    unfold State.blocksPath at hp
    rw [bfsPathH_eq, Option.map_eq_some_iff] at hp
    obtain ⟨q, hq, -⟩ := hp
    obtain ⟨hne, hlast, hhead, hchain⟩ := bfsPath_sound _ _ _ _ _ hq
    refine ⟨q.head hne, hhead _ (List.head?_eq_some_head hne), ?_⟩
    have hrtg := List.relationReflTransGen_of_exists_isChain q hchain hne
    have hgl : q.getLast hne = b := by
      rw [List.getLast?_eq_some_getLast hne] at hlast; exact Option.some.inj hlast
    rwa [hgl] at hrtg
  · rintro ⟨c, hc, hrtg⟩
    have hmem : b ∈ State.reachClosure (s.kindSucc .Blocks) s.presentIssues.length
        (s.kindSucc .Blocks a) := reachable_mem_reachClosure hsU hU c hc hrtg
    have hwb := bfsPath_complete (s.kindSucc .Blocks) (s.kindSucc .Blocks a)
      s.presentIssues.length b hmem
    unfold State.blocksPath
    rw [bfsPathH_eq]
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hwb
    rw [hq]; rfl

end State

end Tl.Kernel
