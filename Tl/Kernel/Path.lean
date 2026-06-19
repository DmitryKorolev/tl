/-
`Tl.Kernel.Path` — `blocksPath`: a TOTAL witness-path extractor over the
`blocks` edge graph, the ordered companion to `why`'s reach+ set (the cycle
witnesses in `Cycles`/`SccProps` are sorted node-SETS, not ordered paths, so a
genuinely new function is needed here). `blocksPath s a b` returns an actual
edge path `[a, …, b]` exactly when `b` is reach+-reachable from `a` over present
`blocks` edges (`a` transitively blocks `b`), and `none` otherwise.

It is built by walking BACK through the `reachClosure` layers (`wbPath`): from a
node in layer `k+1` a predecessor in layer `k` is found by a finite search over
`presentIssues`, peeling one layer per step until a seed member (a direct
`blocks`-successor of `a`) is reached. Structural recursion on the layer index
makes it total with no acyclicity precondition; dangling endpoints are inert
because `kindSucc` already drops non-present targets (ADR-0003 §5). Completeness
is free — extraction is only attempted at the saturated layer `|presentIssues|`,
where `mem_reachClosure_iff` characterizes membership — and soundness (the
returned list is a real consecutive-edge path with the right endpoints) is a
structural induction. Mirrors `mem_why_iff` (ADR-0004 thm 10).

Direction (recorded): `kindSucc .Blocks i` is the present OUTGOING blocks
edges (the issues `i` blocks), consistent with `blocksSucc`/`unblocks`/critical;
`blocksPath a b` is therefore a chain `a` blocks … blocks `b`. The Mathlib
reachability/cardinality zone (ADR-0009) extends to this `Reach` dependent.

Cost (ADR-0023 tiering — an ACCEPTED, recorded compromise, not silent): the
per-frame closure is bound once (no per-candidate / per-frame recompute), but
the back-walk still re-derives `reachClosure` at each decreasing layer index, so
`blocksPath` is ~O(N³) on a project of N present issues. `dep path` is a
one-shot, rarely-run cycle-breaking aid (not a hot read path like
`list`/`ready`/`why`), so this is acceptable; the single-pass forward
BFS-with-parent-map (O(V+E)) that would retire it is a tracked follow-up.
-/
import Tl.Kernel.Reach
import Mathlib.Data.List.Chain

namespace Tl.Kernel

open Tl.Crdt

variable {α : Type _}

/-- Walk back through the `reachClosure` layers to extract a witness path.
    `fuel` is the layer index being peeled; `present` bounds the predecessor
    search. Returns `[seedMember, …, cur]`: a list of consecutive `succ`-edges
    that starts at a `seed` member and ends at `cur`. Total — structural on
    `fuel`; both recursive calls shrink it. -/
def wbPath (succ : IssueId → List IssueId) (seed present : List IssueId) :
    Nat → IssueId → Option (List IssueId)
  | 0, cur => if cur ∈ seed then some [cur] else none
  | fuel + 1, cur =>
    if cur ∈ seed then some [cur]
    else
      -- bind the layer-`fuel` closure ONCE per frame: it is loop-invariant across
      -- the `find?` candidate scan, so recomputing it per candidate (or twice per
      -- frame) would make the back-walk needlessly super-quadratic (ADR-0023).
      let layer := State.reachClosure succ fuel seed
      if cur ∈ layer then
        -- `cur` was already reachable in ≤ `fuel` steps: peel a layer, same node
        wbPath succ seed present fuel cur
      else
        -- `cur` first appears at layer `fuel+1`: a predecessor sits in layer `fuel`
        (present.find? (fun x => decide (x ∈ layer) && decide (cur ∈ succ x))).bind
          (fun x => (wbPath succ seed present fuel x).map (· ++ [cur]))

/-- **Soundness**: a returned path is real — nonempty, ends at `cur`, starts at
    a `seed` member, and every consecutive pair is a `succ`-edge. Structural
    induction on `fuel`. -/
theorem wbPath_sound (succ : IssueId → List IssueId) (seed present : List IssueId) :
    ∀ (fuel : Nat) (cur : IssueId) (p : List IssueId),
      wbPath succ seed present fuel cur = some p →
        p ≠ [] ∧ p.getLast? = some cur ∧
        (∀ h, p.head? = some h → h ∈ seed) ∧
        List.IsChain (fun u v => v ∈ succ u) p := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur p hp
    rw [wbPath] at hp
    by_cases hc : cur ∈ seed
    · rw [if_pos hc, Option.some.injEq] at hp; subst hp
      refine ⟨List.cons_ne_nil _ _, rfl, ?_, List.isChain_singleton _⟩
      intro h hh
      rw [List.head?_cons, Option.some.injEq] at hh; subst hh; exact hc
    · rw [if_neg hc] at hp; exact absurd hp (by simp)
  | succ fuel ih =>
    intro cur p hp
    rw [wbPath] at hp
    by_cases hc : cur ∈ seed
    · rw [if_pos hc, Option.some.injEq] at hp; subst hp
      refine ⟨List.cons_ne_nil _ _, rfl, ?_, List.isChain_singleton _⟩
      intro h hh
      rw [List.head?_cons, Option.some.injEq] at hh; subst hh; exact hc
    · rw [if_neg hc] at hp
      by_cases hr : cur ∈ State.reachClosure succ fuel seed
      · rw [if_pos hr] at hp; exact ih cur p hp
      · rw [if_neg hr, Option.bind_eq_some_iff] at hp
        obtain ⟨x, hfind, hmap⟩ := hp
        rw [Option.map_eq_some_iff] at hmap
        obtain ⟨p', hwb, hpeq⟩ := hmap
        have hx := List.find?_some hfind
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hx
        obtain ⟨_, hcsx⟩ := hx
        obtain ⟨hne, hlast, hhead, hchain⟩ := ih x p' hwb
        subst hpeq
        refine ⟨by simp, ?_, ?_, ?_⟩
        · rw [List.getLast?_append_of_ne_nil _ (by simp)]; rfl
        · intro h hh
          rw [List.head?_append_of_ne_nil _ hne] at hh
          exact hhead h hh
        · refine List.IsChain.append hchain (List.isChain_singleton _) ?_
          intro u hu v hv
          rw [hlast, Option.mem_some_iff] at hu
          rw [List.head?_cons, Option.mem_some_iff] at hv
          subst hu; subst hv
          exact hcsx

/-- **Completeness**: if `cur` is in the layer-`k` closure, `wbPath` at fuel `k`
    finds a path. The seed/universe hypotheses keep every layer inside `present`,
    so the predecessor search succeeds. Induction on the layer index `k`. -/
theorem wbPath_complete (succ : IssueId → List IssueId) (seed present : List IssueId)
    (hsU : seed ⊆ present) (hU : ∀ x ∈ present, succ x ⊆ present) :
    ∀ (k : Nat) (cur : IssueId), cur ∈ State.reachClosure succ k seed →
      (wbPath succ seed present k cur).isSome := by
  intro k
  induction k with
  | zero =>
    intro cur hcur
    have hcs : cur ∈ seed := hcur
    rw [wbPath, if_pos hcs]; rfl
  | succ k ih =>
    intro cur hcur
    rw [wbPath]
    by_cases hc : cur ∈ seed
    · rw [if_pos hc]; rfl
    · rw [if_neg hc]
      by_cases hr : cur ∈ State.reachClosure succ k seed
      · rw [if_pos hr]; exact ih cur hr
      · rw [if_neg hr]
        rw [reachClosure_succ, mem_reachStep] at hcur
        rcases hcur with hcur | ⟨y, hy, hyc⟩
        · exact absurd hcur hr
        · have hyp : y ∈ present := reachClosure_subset_universe hsU hU k hy
          set P : IssueId → Bool := fun x =>
            decide (x ∈ State.reachClosure succ k seed) && decide (cur ∈ succ x) with hPdef
          have hPy : P y = true := by
            rw [hPdef]; rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨hy, hyc⟩
          cases hf : present.find? P with
          | none =>
            exact absurd ((List.find?_eq_none.mp hf) y hyp) (by rw [hPy]; simp)
          | some x' =>
            have hP' := List.find?_some hf
            rw [hPdef, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hP'
            obtain ⟨hx'layer, _⟩ := hP'
            obtain ⟨p'', hp''⟩ := Option.isSome_iff_exists.mp (ih x' hx'layer)
            show ((wbPath succ seed present k x').map (· ++ [cur])).isSome = true
            rw [hp'']; rfl

namespace State

/-- `blocksPath s a b` (ADR-0004 thm 10 companion): a witness path `[a, …, b]`
    of present `blocks` edges (`a` transitively blocks `b`) when `b` is
    reach+-reachable from `a`, else `none`. Total on cyclic and dangling graphs.
    The seed is `a`'s direct blocks-successors and the bound is `|presentIssues|`
    (the saturating layer), so it agrees with `reachClosure`/`why`'s reach+. -/
def blocksPath (s : State) (a b : IssueId) : Option (List IssueId) :=
  (wbPath (s.kindSucc .Blocks) (s.kindSucc .Blocks a) s.presentIssues
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
  obtain ⟨hne, hlast, hhead, hchain⟩ := wbPath_sound _ _ _ _ _ _ hq
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
    obtain ⟨hne, hlast, hhead, hchain⟩ := wbPath_sound _ _ _ _ _ _ hq
    refine ⟨q.head hne, hhead _ (List.head?_eq_some_head hne), ?_⟩
    have hrtg := List.relationReflTransGen_of_exists_isChain q hchain hne
    have hgl : q.getLast hne = b := by
      rw [List.getLast?_eq_some_getLast hne] at hlast; exact Option.some.inj hlast
    rwa [hgl] at hrtg
  · rintro ⟨c, hc, hrtg⟩
    have hmem : b ∈ State.reachClosure (s.kindSucc .Blocks) s.presentIssues.length
        (s.kindSucc .Blocks a) := reachable_mem_reachClosure hsU hU c hc hrtg
    have hwb := wbPath_complete (s.kindSucc .Blocks) (s.kindSucc .Blocks a) s.presentIssues
      hsU hU s.presentIssues.length b hmem
    unfold State.blocksPath
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hwb
    rw [hq]; rfl

end State

end Tl.Kernel
