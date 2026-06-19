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

Cost (ADR-0023 tiering): the shipped engine is `parentSweepH`, carrying only what
the witness walk reads — `(frontier, parent, visited)`. Each round expands the
frontier's out-edges once via a single `bfsStepFn` fold (a `Std.HashSet` visited
set, O(1)-amortized membership, drops intra-round duplicates with no O(layer²) list
`dedup`) and records the discovery parent from `firstPred` (one O(E) pass, O(1)
per-child lookup, not a per-node `parentOf` frontier rescan). The successor itself
is bucketed (`blocksSuccB`, O(deg)/node). Each node's out-edges are thus expanded
once, and an empty frontier short-circuits the round (`if p.1.isEmpty then p`), so
the whole sweep is O(V+E). The list/`AMap` `parentSweep` is the proof REFERENCE (its `∉ acc`/`AMap.find`
and per-discovery `parentOf` are O(N), and it additionally keeps a depth map and the
full accumulator for the termination/soundness proofs); `parentSweepH_eq` proves the
two agree pointwise on the frontier, parent map, and visited set, so the
soundness/completeness proofs transfer to the shipped `blocksPath` unchanged
(structure proved, wall-clock tested — ADR-0023; indexed-view substrate — ADR-0024).
-/
import Tl.Kernel.Reach
import Tl.Kernel.ReachBFS
import Tl.Kernel.ReadyFast
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

/-- A discovering frontier predecessor of `y`: the first frontier node that lists
    `y` as a successor. -/
def parentOf (succ : IssueId → List IssueId) (frontier : List IssueId) (y : IssueId) :
    Option IssueId :=
  frontier.find? (fun u => decide (y ∈ succ u))

/-! ## First-predecessor index (one O(E) pass, no per-node rescan)

`parentOf succ fr y = fr.find? (y ∈ succ ·)` re-walks the whole frontier per
discovered node (Θ(|layer|·|fr|) per round). `firstPred` precomputes, in ONE pass
over the frontier's out-edges, the first predecessor of every child; a lookup is
then O(1)-amortized and `firstPred[y]? = parentOf succ fr y`. -/

/-- The frontier's out-edges as `(predecessor, successor)` pairs, in frontier×succ
    order. -/
def frontierEdges (succ : IssueId → List IssueId) (fr : List IssueId) : List (IssueId × IssueId) :=
  fr.flatMap (fun u => (succ u).map (fun y => (u, y)))

/-- First-writer-wins batch insert: a child already mapped keeps its first
    predecessor. -/
def firstPredStep (m : Std.HashMap IssueId IssueId) (e : IssueId × IssueId) :
    Std.HashMap IssueId IssueId :=
  if m.contains e.2 then m else m.insert e.2 e.1

/-- The first-predecessor map of the frontier (one O(E) pass). -/
def firstPred (succ : IssueId → List IssueId) (fr : List IssueId) : Std.HashMap IssueId IssueId :=
  (frontierEdges succ fr).foldl firstPredStep ∅

/-- First-writer-wins fold lookup: a key already in `m0` keeps its value; else the
    first edge with that child supplies the predecessor. -/
theorem getElem?_foldl_firstPredStep (y : IssueId) :
    ∀ (L : List (IssueId × IssueId)) (m0 : Std.HashMap IssueId IssueId),
      (L.foldl firstPredStep m0)[y]?
        = match m0[y]? with
          | some v => some v
          | none => (L.find? (fun e => decide (e.2 = y))).map (·.1)
  | [], m0 => by
    show m0[y]? = match m0[y]? with
      | some v => some v
      | none => (([] : List (IssueId × IssueId)).find? (fun e => decide (e.2 = y))).map (·.1)
    cases hm : m0[y]? with
    | some _ => rfl
    | none => rfl
  | e :: L', m0 => by
    show (L'.foldl firstPredStep (firstPredStep m0 e))[y]? = _
    rw [getElem?_foldl_firstPredStep y L' (firstPredStep m0 e), List.find?_cons]
    by_cases hc : m0.contains e.2 = true
    · -- m0 already maps e.2: the step is a no-op
      have hfp : firstPredStep m0 e = m0 := by unfold firstPredStep; rw [if_pos hc]
      rw [hfp]
      cases hm : m0[y]? with
      | some _ => rfl
      | none =>
        have hey : ¬ (e.2 = y) := by
          intro he; subst he
          rw [Std.HashMap.contains_eq_isSome_getElem?, hm] at hc
          exact Bool.noConfusion hc
        rw [show decide (e.2 = y) = false from decide_eq_false hey]
    · -- m0 does not map e.2: e.2 ↦ e.1 is the first writer
      rw [Bool.not_eq_true] at hc
      have hfp : firstPredStep m0 e = m0.insert e.2 e.1 := by
        unfold firstPredStep
        rw [if_neg (show ¬ (m0.contains e.2 = true) by rw [hc]; exact Bool.false_ne_true)]
      rw [hfp, Std.HashMap.getElem?_insert]
      by_cases hey : e.2 = y
      · subst hey
        have hm : m0[e.2]? = none := by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
          cases hmm : m0[e.2]? with
          | none => rfl
          | some v => rw [hmm] at hc; exact Bool.noConfusion hc
        rw [if_pos (beq_self_eq_true e.2), hm,
          show decide (e.2 = e.2) = true from decide_eq_true rfl]
        rfl
      · rw [if_neg (show ¬ ((e.2 == y) = true) by rw [beq_iff_eq]; exact hey),
          show decide (e.2 = y) = false from decide_eq_false hey]

/-- The first frontier out-edge into `y` carries exactly `parentOf`'s predecessor. -/
theorem frontierEdges_find?_parentOf (succ : IssueId → List IssueId) (y : IssueId) :
    ∀ (fr : List IssueId),
      ((frontierEdges succ fr).find? (fun e => decide (e.2 = y))).map (·.1)
        = parentOf succ fr y
  | [] => rfl
  | u :: fr' => by
    have hinner : (((succ u).map (fun s => (u, s))).find? (fun e => decide (e.2 = y))).map (·.1)
        = if y ∈ succ u then some u else none := by
      rw [List.find?_map, Option.map_map]
      show ((succ u).find? (fun s => decide (s = y))).map (fun _ => u) = _
      cases h : (succ u).find? (fun s => decide (s = y)) with
      | none =>
        rw [List.find?_eq_none] at h
        rw [Option.map_none, if_neg (fun hy => absurd (decide_eq_true (rfl : y = y)) (h y hy))]
      | some v =>
        have hmem : v ∈ succ u := List.mem_of_find?_eq_some h
        have hpv := List.find?_some h
        have hvy : v = y := of_decide_eq_true hpv
        rw [if_pos (hvy ▸ hmem)]
        rfl
    have hLHS : ((frontierEdges succ (u :: fr')).find? (fun e => decide (e.2 = y))).map (·.1)
        = (if y ∈ succ u then some u else none).or
            (((frontierEdges succ fr').find? (fun e => decide (e.2 = y))).map (·.1)) := by
      unfold frontierEdges
      rw [List.flatMap_cons, List.find?_append, Option.map_or, hinner]
    have hpar : parentOf succ (u :: fr') y
        = if y ∈ succ u then some u else parentOf succ fr' y := by
      unfold parentOf
      rw [List.find?_cons]
      cases hy : decide (y ∈ succ u) with
      | true => rw [if_pos (of_decide_eq_true hy)]
      | false => rw [if_neg (of_decide_eq_false hy)]
    rw [hLHS, hpar, frontierEdges_find?_parentOf succ y fr']
    by_cases hy : y ∈ succ u
    · rw [if_pos hy, if_pos hy, Option.some_or]
    · rw [if_neg hy, if_neg hy, Option.none_or]

/-- **The one-pass index equals `parentOf`.** -/
theorem firstPred_getElem? (succ : IssueId → List IssueId) (fr : List IssueId) (y : IssueId) :
    (firstPred succ fr)[y]? = parentOf succ fr y := by
  unfold firstPred
  rw [getElem?_foldl_firstPredStep y (frontierEdges succ fr) ∅, Std.HashMap.getElem?_empty]
  exact frontierEdges_find?_parentOf succ y fr

/-! ## O(V+E) parent-recording frontier BFS

The path is extracted from a parent map recorded *at discovery* during a single
frontier sweep: each round expands only the last layer, and every newly-reached
node remembers the frontier predecessor that found it (one `IssueId`, not a whole
path) together with the round it was found (`depth`). The witness path to `b` is
then a one-shot parent walk from `b` back to a seed root — strictly decreasing
`depth`, so it terminates. This replaces the materialized full-path map (whose
per-node `path ++ [node]` append was a further O(N²) over the shared closure). -/

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

`parentSweep` above is the list/`AMap` proof REFERENCE: its `∉ acc` test and
`AMap.find` are O(N), the per-discovery `parentOf` rescans the whole frontier, and
`acc ++ layer` per round is O(N²). The shipped `parentSweepH` carries only what the
witness walk reads — `(frontier, parent, visited)` — and spends O(deg) per node per
round:

* the layer is one `bfsStepFn` fold over the frontier's out-edges (the proven
  `Std.HashSet` dedup of `ReachBFS`), which also returns the extended visited set,
  so a membership test is O(1)-amortized and intra-round duplicates cost O(1) each
  (no O(layer²) list `dedup`);
* the parent at discovery comes from `firstPred` — one O(E) pass over the frontier's
  out-edges building a first-writer-wins child→predecessor map — so a per-child
  parent lookup is O(1)-amortized, not an O(|frontier|) `parentOf` walk.

Each node's out-edges are thus expanded once and the whole sweep is O(V+E). An empty
frontier is a fixpoint, so the round short-circuits (`if p.1.isEmpty then p`): once
the cone saturates, the remaining rounds of the `|presentIssues|`-round bound are
O(1) returns rather than re-walks. The reference keeps the depth map and the full
forward accumulator for the termination/soundness proofs; the shipped engine carries
neither. `parentSweepH_eq` proves the two agree pointwise on
the frontier, the parent map, and the visited set, so the soundness/completeness
proofs transfer to `blocksPath` unchanged (ADR-0024 indexed-view substrate; ADR-0023
tiering: structure proved, wall-clock tested). -/

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

/-- One shipped expansion step: folding `bfsStepFn` over the frontier's out-edges
    against a visited set mirroring `acc` yields the reference layer (first-occurrence
    order) and a visited set mirroring `acc ++ layer`. The `Std.HashSet` membership
    test stands in for the spec's list `∉ acc`, and intra-round duplicates are dropped
    in O(1) each (no list `dedup`). -/
theorem bfsStep_layer (succ : IssueId → List IssueId) (acc fr : List IssueId)
    (v : Std.HashSet IssueId) (hv : ∀ z, v.contains z = decide (z ∈ acc)) :
    ((fr.flatMap succ).foldl State.bfsStepFn (v, [])).2.reverse = State.bfsLayer succ acc fr
    ∧ (∀ z, ((fr.flatMap succ).foldl State.bfsStepFn (v, [])).1.contains z
        = decide (z ∈ acc ++ State.bfsLayer succ acc fr)) := by
  have hv' : ∀ z, v.contains z = true ↔ z ∈ acc ++ [] := by
    intro z; rw [hv z, List.append_nil, decide_eq_true_eq]
  obtain ⟨h1, h2⟩ := State.bfsFold_spec (fr.flatMap succ) acc [] v hv'
  have hlayer : ((fr.flatMap succ).foldl State.bfsStepFn (v, [])).2.reverse
      = State.bfsLayer succ acc fr := by
    rw [h1, List.append_nil, List.reverse_reverse]
    unfold State.bfsLayer
    apply congrArg dedup
    apply List.filter_congr
    intro y _
    rw [List.append_nil]
  refine ⟨hlayer, fun z => ?_⟩
  have hmem : z ∈ ((fr.flatMap succ).foldl State.bfsStepFn (v, [])).2
      ↔ z ∈ State.bfsLayer succ acc fr := by
    rw [← hlayer, List.mem_reverse]
  rw [Bool.eq_iff_iff, h2 z, decide_eq_true_eq, List.mem_append, List.mem_append, hmem]

/-- The shipped O(V+E) sweep: `(frontier, parent, visited)`. `visited` mirrors the
    reachable set for the O(1)-amortized frontier filter; `parent` is the discovery
    map. The layer and the extended visited set come from a single `bfsStepFn` fold;
    the parent at discovery comes from the one-pass `firstPred` index. -/
def parentSweepH (succ : IssueId → List IssueId) (seed : List IssueId) :
    Nat → List IssueId × Std.HashMap IssueId IssueId × Std.HashSet IssueId
  | 0 => (seed, ∅, hashSetOf seed)
  | k + 1 =>
    let p := parentSweepH succ seed k
    -- early exit: an empty frontier is a fixpoint, so every remaining round is O(1)
    if p.1.isEmpty then p
    else
      let step := (p.1.flatMap succ).foldl State.bfsStepFn (p.2.2, [])
      let layer := step.2.reverse
      let fp := firstPred succ p.1
      (layer,
       layer.foldl (fun m y => m.insert y ((fp[y]?).getD y)) p.2.1,
       step.1)

/-- The shipped sweep agrees pointwise with the list/`AMap` reference on the frontier,
    the parent map, and the visited set — the projections the witness walk reads. -/
theorem parentSweepH_eq (succ : IssueId → List IssueId) (seed : List IssueId) :
    (n : Nat) →
    (parentSweepH succ seed n).1 = (parentSweep succ seed n).2.1
    ∧ (∀ z, (parentSweepH succ seed n).2.1[z]? = (parentSweep succ seed n).2.2.1.find z)
    ∧ (∀ z, (parentSweepH succ seed n).2.2.contains z = decide (z ∈ (parentSweep succ seed n).1))
  | 0 => by
    refine ⟨rfl, ?_, ?_⟩
    · intro z
      rw [show (parentSweepH succ seed 0).2.1 = (∅ : Std.HashMap IssueId IssueId) from rfl,
        show (parentSweep succ seed 0).2.2.1 = AMap.empty from rfl,
        Std.HashMap.getElem?_empty, AMap.find_empty]
    · intro z
      rw [show (parentSweepH succ seed 0).2.2 = hashSetOf seed from rfl,
        show (parentSweep succ seed 0).1 = seed from rfl, Bool.eq_iff_iff, decide_eq_true_eq,
        Std.HashSet.contains_iff_mem, mem_hashSetOf]
  | k + 1 => by
    obtain ⟨ih1, ih2, ih3⟩ := parentSweepH_eq succ seed k
    set accL := (parentSweep succ seed k).1 with haccL
    set frL := (parentSweep succ seed k).2.1 with hfrL
    have hL1 : (parentSweep succ seed (k + 1)).2.1 = State.bfsLayer succ accL frL := rfl
    have hL2 : (parentSweep succ seed (k + 1)).2.2.1
        = (State.bfsLayer succ accL frL).foldl
            (fun m y => m.insert y ((parentOf succ frL y).getD y)) (parentSweep succ seed k).2.2.1 := rfl
    have hL3 : (parentSweep succ seed (k + 1)).1 = accL ++ State.bfsLayer succ accL frL := rfl
    by_cases hfe : (parentSweepH succ seed k).1.isEmpty = true
    · -- empty frontier: the shipped sweep returns `p` unchanged (the early exit), and
      -- the reference's next layer is `bfsLayer _ _ [] = []`, so both stabilize
      have hp1 : (parentSweepH succ seed k).1 = [] := List.isEmpty_iff.mp hfe
      have hfr0 : frL = [] := by rw [← ih1]; exact hp1
      have hlay0 : State.bfsLayer succ accL frL = [] := by rw [hfr0]; rfl
      have hfix : parentSweepH succ seed (k + 1) = parentSweepH succ seed k := by
        show (if (parentSweepH succ seed k).1.isEmpty then parentSweepH succ seed k else _)
          = parentSweepH succ seed k
        rw [if_pos hfe]
      refine ⟨?_, ?_, ?_⟩
      · rw [hfix, hp1, hL1, hlay0]
      · intro z; rw [hfix, hL2, hlay0, List.foldl_nil]; exact ih2 z
      · intro z; rw [hfix, hL3, hlay0, List.append_nil]; exact ih3 z
    · -- nonempty frontier: the expanding round, matched to the reference layer
      rw [Bool.not_eq_true] at hfe
      -- reduce the early-exit `if` to its `else` branch, then project
      have hite : parentSweepH succ seed (k + 1)
          = (let p := parentSweepH succ seed k
             let step := (p.1.flatMap succ).foldl State.bfsStepFn (p.2.2, [])
             (step.2.reverse,
              step.2.reverse.foldl (fun m y => m.insert y (((firstPred succ p.1)[y]?).getD y)) p.2.1,
              step.1)) := by
        show (if (parentSweepH succ seed k).1.isEmpty then parentSweepH succ seed k else _) = _
        rw [if_neg (show ¬ (parentSweepH succ seed k).1.isEmpty = true by rw [hfe]; exact Bool.false_ne_true)]
      -- the shipped layer / visited set from the bfsStepFn fold matches the reference
      obtain ⟨hLay, hVis⟩ :=
        bfsStep_layer succ accL (parentSweepH succ seed k).1 (parentSweepH succ seed k).2.2 ih3
      have hH1 : (parentSweepH succ seed (k + 1)).1
          = (((parentSweepH succ seed k).1.flatMap succ).foldl State.bfsStepFn
              ((parentSweepH succ seed k).2.2, [])).2.reverse := by rw [hite]
      have hH2 : (parentSweepH succ seed (k + 1)).2.1
          = ((((parentSweepH succ seed k).1.flatMap succ).foldl State.bfsStepFn
                ((parentSweepH succ seed k).2.2, [])).2.reverse).foldl
              (fun m y => m.insert y (((firstPred succ (parentSweepH succ seed k).1)[y]?).getD y))
              (parentSweepH succ seed k).2.1 := by rw [hite]
      have hH3 : (parentSweepH succ seed (k + 1)).2.2
          = (((parentSweepH succ seed k).1.flatMap succ).foldl State.bfsStepFn
              ((parentSweepH succ seed k).2.2, [])).1 := by rw [hite]
      refine ⟨?_, ?_, ?_⟩
      · rw [hH1, hLay, hL1, ih1]
      · intro z
        rw [hH2, hLay, ih1, hL2,
          getElem?_foldl_insert_keys (fun y => ((firstPred succ frL)[y]?).getD y) _ _ z,
          find_foldl_insert (fun y => (parentOf succ frL y).getD y) _ _ z]
        by_cases hz : z ∈ State.bfsLayer succ accL frL
        · rw [if_pos hz, if_pos hz, firstPred_getElem?]
        · rw [if_neg hz, if_neg hz]; exact ih2 z
      · intro z
        rw [hH3, hVis z, hL3, ih1]

/-- The shipped witness-path extractor: the parent walk over the hash sweep. -/
def bfsPathH (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) : Option (List IssueId) :=
  if (parentSweepH succ seed fuel).2.2.contains cur
  then some (parentWalkH (parentSweepH succ seed fuel).2.1 (fuel + 1) cur [])
  else none

theorem bfsPathH_eq (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) : bfsPathH succ seed fuel cur = bfsPath succ seed fuel cur := by
  unfold bfsPathH bfsPath
  obtain ⟨_, hpar, hvis⟩ := parentSweepH_eq succ seed fuel
  by_cases hc : cur ∈ (parentSweep succ seed fuel).1
  · rw [if_pos (show (parentSweepH succ seed fuel).2.2.contains cur = true by
        rw [hvis cur, decide_eq_true_eq]; exact hc),
      if_pos hc,
      parentWalkH_eq (parentSweepH succ seed fuel).2.1 (parentSweep succ seed fuel).2.2.1 hpar]
  · rw [if_neg (show ¬ (parentSweepH succ seed fuel).2.2.contains cur = true by
        rw [hvis cur, decide_eq_true_eq]; exact hc),
      if_neg hc]

namespace State

/-- The bucketed `Blocks` successor (O(deg)-amortized per node via the
    source-adjacency bucket + present-set hash) is the spec `kindSucc .Blocks`
    (`blocksSucc` = present `Blocks`-dependents, defeq `kindSucc .Blocks`), so
    feeding it to the engine keeps the engine's O(V+E) per-node cost. -/
theorem blocksSuccB_kindSucc (s : State) :
    blocksSuccB (blocksBySource s.presentEdges) (hashSetOf s.presentIssues)
      = s.kindSucc .Blocks :=
  funext fun i => (blocksSuccB_eq s i).trans (by
    unfold State.blocksSucc State.kindSucc State.dependentsOf; rfl)

/-- `blocksPath s a b` (ADR-0004 thm 10 companion): a witness path `[a, …, b]`
    of present `blocks` edges (`a` transitively blocks `b`) when `b` is
    reach+-reachable from `a`, else `none`. Total on cyclic and dangling graphs.
    The seed is `a`'s direct blocks-successors and the bound is `|presentIssues|`
    (the saturating layer), so it agrees with `reachClosure`/`why`'s reach+. The
    engine runs over the *bucketed* `blocks` successor (`blocksSuccB`, O(deg) per
    node) — proved equal to `kindSucc .Blocks` — so a per-node successor query is
    not an O(E) edge rescan. -/
def blocksPath (s : State) (a b : IssueId) : Option (List IssueId) :=
  let succB := blocksSuccB (blocksBySource s.presentEdges) (hashSetOf s.presentIssues)
  (bfsPathH succB (succB a) s.presentIssues.length b).map (a :: ·)

/-- **`blocksPath` path validity**: a returned path is a real `blocks`-edge path
    `a ⇝ b` — head `a`, last `b`, every consecutive pair connected by a present
    `blocks` edge. -/
theorem blocksPath_valid (s : State) (a b : IssueId) (p : List IssueId)
    (h : s.blocksPath a b = some p) :
    p.head? = some a ∧ p.getLast? = some b ∧
      List.IsChain (fun u v => v ∈ s.kindSucc .Blocks u) p := by
  unfold State.blocksPath at h
  simp only [blocksSuccB_kindSucc] at h
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
    simp only [blocksSuccB_kindSucc] at hp
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
    simp only [blocksSuccB_kindSucc]
    rw [bfsPathH_eq]
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hwb
    rw [hq]; rfl

end State

end Tl.Kernel
