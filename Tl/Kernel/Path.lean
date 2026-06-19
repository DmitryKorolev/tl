/-
`Tl.Kernel.Path` — `blocksPath`: a TOTAL witness-path extractor over the
`blocks` edge graph, the ordered companion to `why`'s reach+ set (the cycle
witnesses in `Cycles`/`SccProps` are sorted node-SETS, not ordered paths, so a
genuinely new function is needed here). `blocksPath s a b` returns an actual
edge path `[a, …, b]` exactly when `b` is reach+-reachable from `a` over present
`blocks` edges (`a` transitively blocks `b`), and `none` otherwise.

It is built by a SINGLE FORWARD sweep (`pathState`): one accumulator carries the
growing layer (`= reachClosure succ k seed`, evolved by `reachStep`) and a
MATERIALIZED path map (`AMap`, not a closure) that hands every newly-reached node
the path of a discovering predecessor extended by that node. After
`|presentIssues|` rounds the path map is saturated; `blocksPath` reads off the
entry for `b` with a flat `AMap.find`. Because the map is materialized, the
layers are built ONCE and a lookup never re-walks them. Structural recursion on
the round count makes it total with no acyclicity precondition; dangling
endpoints are inert because `kindSucc` already drops non-present targets
(ADR-0003 §5). The invariant (`pathState_inv`) gives completeness (a node has a
path iff it is in the layer, which `mem_reachStep` keeps equal to `reachClosure`)
and soundness (every stored path is a real consecutive-edge chain from a `seed`
member). Mirrors `mem_why_iff` (ADR-0004 thm 10).

Direction (recorded): `kindSucc .Blocks i` is the present OUTGOING blocks
edges (the issues `i` blocks), consistent with `blocksSucc`/`unblocks`/critical;
`blocksPath a b` is therefore a chain `a` blocks … blocks `b`. The Mathlib
reachability/cardinality zone (ADR-0009) extends to this `Reach` dependent.

Cost (ADR-0023 tiering): one forward sweep with the path map built once. Measured
pure-kernel on a deep blocks chain, `bfsPath` runs at about 1.5× `reachClosure`
(the `why` baseline), versus about 344× for the retired closure-tower re-walk, so
the materialized path map is a lower-order term over the shared sweep rather than a
second traversal. The total stays superlinear and is recorded, not silently
optimal. The dominant factor is `reachStep`'s `dedup`, run once per round over a
growing accumulator for `|presentIssues|` rounds — `O(N³)` on a deep chain, the
same factor `why`/`weight`/cycles pay. Storing a full path per node (the `predPath`
`++ [node]` append plus the assoc-list `AMap.find`/`insert`) adds a further `O(N²)`
(`why` stores no paths). The driver is `|presentIssues|` (the fuel), not path
depth: `blocksPath` runs the full bound and does not adopt `why`'s early-saturation
exit, so a shallow `dep path` in a large project still pays the per-round cost.
Retiring all of this to `O(V+E)` — a frontier worklist with a `Std.HashSet`, a
parent-pointer map reconstructed once, and early saturation — is the tracked
reach-cone follow-up; at realistic project sizes a one-shot `dep path` is
sub-second.
-/
import Tl.Kernel.Reach
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

/-- The witness path the round-`k+1` sweep records for a freshly-reached node
    `y`: a discovering predecessor's stored path, extended by `y`. -/
def predPath (succ : IssueId → List IssueId)
    (prev : List IssueId × AMap IssueId (List IssueId)) (y : IssueId) : List IssueId :=
  ((prev.1.find? (fun u => decide (y ∈ succ u))).bind (fun u => prev.2.find u)).getD [] ++ [y]

/-- A SINGLE forward sweep with a MATERIALIZED path map: `(pathState succ seed k)`
    carries `(layer, paths)` where `layer` is the round-`k` closure
    (`= reachClosure succ k seed`) and `paths` is a finite map (`AMap`, not a
    closure) sending every node reachable in ≤ `k` steps to a witness path
    `[seedMember, …, node]`. One round grows the layer by `reachStep` (the layer
    evolves EXACTLY as `reachClosure`) and inserts, for each newly-reached node,
    a discovering predecessor's path extended by it (`predPath`). The map is built
    ONCE in the forward pass and a lookup is a flat `AMap.find` — no per-lookup
    re-descent. -/
def pathState (succ : IssueId → List IssueId) (seed : List IssueId) :
    Nat → List IssueId × AMap IssueId (List IssueId)
  | 0 => (seed, seed.foldl (fun m y => m.insert y [y]) AMap.empty)
  | k + 1 =>
    (State.reachStep succ (pathState succ seed k).1,
     ((State.reachStep succ (pathState succ seed k).1).filter
        (fun y => decide (y ∉ (pathState succ seed k).1))).foldl
       (fun m y => m.insert y (predPath succ (pathState succ seed k) y))
       (pathState succ seed k).2)

/-- The witness path to `cur` after `fuel` forward rounds (`none` if `cur` is not
    reach+-reachable in ≤ `fuel` steps). Total — `pathState` is structural on `fuel`. -/
def bfsPath (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) : Option (List IssueId) :=
  (pathState succ seed fuel).2.find cur

/-- The forward sweep's invariant: the carried layer IS `reachClosure`; a node
    has a path iff it is in that layer; and every stored path is a real
    consecutive-`succ` chain from a `seed` member ending at the node. Structural
    induction on the round count. -/
theorem pathState_inv (succ : IssueId → List IssueId) (seed : List IssueId) : ∀ (k : Nat),
    (pathState succ seed k).1 = State.reachClosure succ k seed ∧
    (∀ y, ((pathState succ seed k).2.find y).isSome ↔ y ∈ (pathState succ seed k).1) ∧
    (∀ y p, (pathState succ seed k).2.find y = some p →
      p ≠ [] ∧ p.getLast? = some y ∧ (∀ h, p.head? = some h → h ∈ seed) ∧
      List.IsChain (fun u v => v ∈ succ u) p) := by
  intro k
  induction k with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · intro y
      show ((seed.foldl (fun m y => m.insert y [y]) AMap.empty).find y).isSome ↔ y ∈ seed
      rw [find_foldl_insert (fun y => [y]) seed AMap.empty y]
      by_cases hy : y ∈ seed
      · rw [if_pos hy]; exact iff_of_true Option.isSome_some hy
      · rw [if_neg hy, AMap.find_empty]
        exact iff_of_false (fun h => Bool.false_ne_true (Option.isSome_none ▸ h)) hy
    · intro y p
      show (seed.foldl (fun m y => m.insert y [y]) AMap.empty).find y = some p → _
      rw [find_foldl_insert (fun y => [y]) seed AMap.empty y]
      by_cases hy : y ∈ seed
      · rw [if_pos hy, Option.some.injEq]; intro he; subst he
        refine ⟨List.cons_ne_nil _ _, rfl, ?_, List.isChain_singleton _⟩
        intro h hh; rw [List.head?_cons, Option.some.injEq] at hh; subst hh; exact hy
      · rw [if_neg hy, AMap.find_empty]; intro h; cases h
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    -- the materialized round-(k+1) lookup, expanded by `find_foldl_insert`
    have hfind : ∀ y, (pathState succ seed (k + 1)).2.find y =
        if y ∈ (State.reachStep succ (pathState succ seed k).1).filter
                 (fun y => decide (y ∉ (pathState succ seed k).1))
        then some (predPath succ (pathState succ seed k) y)
        else (pathState succ seed k).2.find y := fun y =>
      find_foldl_insert (predPath succ (pathState succ seed k))
        ((State.reachStep succ (pathState succ seed k).1).filter
          (fun y => decide (y ∉ (pathState succ seed k).1)))
        (pathState succ seed k).2 y
    have hnew : ∀ y, (y ∈ (State.reachStep succ (pathState succ seed k).1).filter
                 (fun y => decide (y ∉ (pathState succ seed k).1))) ↔
        (y ∈ State.reachStep succ (pathState succ seed k).1 ∧ y ∉ (pathState succ seed k).1) :=
      fun y => by rw [List.mem_filter, decide_eq_true_eq]
    have hlayer : (pathState succ seed (k + 1)).1 = State.reachStep succ (pathState succ seed k).1 :=
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hlayer, ih1]; exact (reachClosure_succ succ k seed).symm
    · intro y
      rw [hlayer, mem_reachStep, hfind y]
      by_cases hyf : y ∈ (State.reachStep succ (pathState succ seed k).1).filter
                 (fun y => decide (y ∉ (pathState succ seed k).1))
      · rw [if_pos hyf]
        exact iff_of_true Option.isSome_some (mem_reachStep.mp ((hnew y).mp hyf).1)
      · rw [if_neg hyf, ih2 y]
        rw [hnew, not_and_or, not_not] at hyf
        constructor
        · exact fun hin => Or.inl hin
        · rintro (hin | ⟨u, hu, hyu⟩)
          · exact hin
          · rcases hyf with hnr | hin
            · exact absurd (mem_reachStep.mpr (Or.inr ⟨u, hu, hyu⟩)) hnr
            · exact hin
    · intro y p
      rw [hfind y]
      by_cases hyf : y ∈ (State.reachStep succ (pathState succ seed k).1).filter
                 (fun y => decide (y ∉ (pathState succ seed k).1))
      · rw [if_pos hyf, Option.some.injEq]
        intro he; subst he
        obtain ⟨hyr, hynl⟩ := (hnew y).mp hyf
        obtain ⟨u, hu, hyu⟩ := (mem_reachStep.mp hyr).resolve_left hynl
        -- the predecessor search succeeds and reads a valid prefix path
        rcases Option.eq_none_or_eq_some
            ((pathState succ seed k).1.find? (fun w => decide (y ∈ succ w))) with hf | ⟨u', hf⟩
        · have hd : decide (y ∈ succ u) = true := by rw [decide_eq_true_eq]; exact hyu
          exact absurd hd (List.find?_eq_none.mp hf u hu)
        · have hu' : u' ∈ (pathState succ seed k).1 := List.mem_of_find?_eq_some hf
          have hyu' : y ∈ succ u' := by have := List.find?_some hf; rwa [decide_eq_true_eq] at this
          obtain ⟨pu, hpu⟩ := Option.isSome_iff_exists.mp ((ih2 u').mpr hu')
          obtain ⟨hne, hlast, hhead, hchain⟩ := ih3 u' pu hpu
          have hval : predPath succ (pathState succ seed k) y = pu ++ [y] := by
            unfold predPath; rw [hf, Option.bind_some, hpu, Option.getD_some]
          rw [hval]
          refine ⟨List.concat_ne_nil y pu, ?_, ?_, ?_⟩
          · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil y [])]; rfl
          · intro h hh; rw [List.head?_append_of_ne_nil _ hne] at hh; exact hhead h hh
          · refine List.IsChain.append hchain (List.isChain_singleton _) ?_
            intro a ha b hb
            rw [hlast, Option.mem_some_iff] at ha
            rw [List.head?_cons, Option.mem_some_iff] at hb
            subst ha; subst hb; exact hyu'
      · rw [if_neg hyf]; exact ih3 y p

/-- **Soundness**: a returned path is real — nonempty, ends at `cur`, starts at a
    `seed` member, every consecutive pair a `succ`-edge. -/
theorem bfsPath_sound (succ : IssueId → List IssueId) (seed : List IssueId)
    (fuel : Nat) (cur : IssueId) (p : List IssueId) (h : bfsPath succ seed fuel cur = some p) :
    p ≠ [] ∧ p.getLast? = some cur ∧
    (∀ h, p.head? = some h → h ∈ seed) ∧
    List.IsChain (fun u v => v ∈ succ u) p :=
  (pathState_inv succ seed fuel).2.2 cur p h

/-- **Completeness**: a node in the round-`k` closure has a witness path. -/
theorem bfsPath_complete (succ : IssueId → List IssueId) (seed : List IssueId)
    (k : Nat) (cur : IssueId) (h : cur ∈ State.reachClosure succ k seed) :
    (bfsPath succ seed k cur).isSome :=
  ((pathState_inv succ seed k).2.1 cur).mpr ((pathState_inv succ seed k).1.symm ▸ h)

namespace State

/-- `blocksPath s a b` (ADR-0004 thm 10 companion): a witness path `[a, …, b]`
    of present `blocks` edges (`a` transitively blocks `b`) when `b` is
    reach+-reachable from `a`, else `none`. Total on cyclic and dangling graphs.
    The seed is `a`'s direct blocks-successors and the bound is `|presentIssues|`
    (the saturating layer), so it agrees with `reachClosure`/`why`'s reach+. -/
def blocksPath (s : State) (a b : IssueId) : Option (List IssueId) :=
  (bfsPath (s.kindSucc .Blocks) (s.kindSucc .Blocks a)
      s.presentIssues.length b).map (a :: ·)

/-- **`blocksPath` path validity**: a returned path is a real `blocks`-edge path
    `a ⇝ b` — head `a`, last `b`, every consecutive pair connected by a present
    `blocks` edge. -/
theorem blocksPath_valid (s : State) (a b : IssueId) (p : List IssueId)
    (h : s.blocksPath a b = some p) :
    p.head? = some a ∧ p.getLast? = some b ∧
      List.IsChain (fun u v => v ∈ s.kindSucc .Blocks u) p := by
  unfold State.blocksPath at h
  rw [Option.map_eq_some_iff] at h
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
    rw [Option.map_eq_some_iff] at hp
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
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hwb
    rw [hq]; rfl

end State

end Tl.Kernel
