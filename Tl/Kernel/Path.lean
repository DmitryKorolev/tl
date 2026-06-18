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
    else if cur ∈ State.reachClosure succ fuel seed then
      -- `cur` was already reachable in ≤ `fuel` steps: peel a layer, same node
      wbPath succ seed present fuel cur
    else
      -- `cur` first appears at layer `fuel+1`: a predecessor sits in layer `fuel`
      (present.find? (fun x =>
          decide (x ∈ State.reachClosure succ fuel seed) && decide (cur ∈ succ x))).bind
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

namespace State

/-- `blocksPath s a b` (ADR-0004 thm 10 companion): a witness path `[a, …, b]`
    of present `blocks` edges (`a` transitively blocks `b`) when `b` is
    reach+-reachable from `a`, else `none`. Total on cyclic and dangling graphs.
    The seed is `a`'s direct blocks-successors and the bound is `|presentIssues|`
    (the saturating layer), so it agrees with `reachClosure`/`why`'s reach+. -/
def blocksPath (s : State) (a b : IssueId) : Option (List IssueId) :=
  (wbPath (s.kindSucc .Blocks) (s.kindSucc .Blocks a) s.presentIssues
      s.presentIssues.length b).map (a :: ·)

end State

end Tl.Kernel
