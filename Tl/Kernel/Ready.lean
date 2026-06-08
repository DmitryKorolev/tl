/-
`Tl.Kernel.Ready` — `ready`, the critical-path `weight`, `why`, and `unblocks`
(ADR-0004 thm 4/5/7/10, ADR-0010).

`ready s now` answers the whole thesis — "what can I work on right now":
`i` is ready iff it is a materialized, `open`, non-epic, non-deferred issue every
one of whose blockers is discharged (closed by effective status, OR dangling —
inert, ADR-0003 §5). The list is returned in the total deterministic ranking
(priority ↑, critical-path weight ↓, createdAt ↑, id ↑), so replicas agree on the
ranked queue.

Reachability (the `weight` critical-path metric and the transitive `why` blockers)
is computed by an *iterated closure* — `reachStep` adds the successors of the
current set and dedups; iterating it `|presentIssues|` times saturates on any
graph, cyclic or dangling, with no acyclicity precondition and no well-founded
obligation (plain bounded iteration, my own `iterateN`). `weight` counts every reachable
*present* issue regardless of status (a structural metric); dangling targets
contribute no node. `why` follows only *live* (present, unclosed) blockers, so it
stops at a discharged blocker — consistent with `ready`.
-/
import Tl.Kernel.Rollup

namespace Tl.Kernel

open Tl.Crdt

/-- Deduplicate, keeping the first occurrence (no Mathlib `List.dedup`, ADR-0009). -/
def dedup {α : Type _} [DecidableEq α] (l : List α) : List α :=
  l.foldr (fun x acc => if x ∈ acc then acc else x :: acc) []

/-- Iterate `f` `n` times (total, structural on `n`). -/
def iterateN {α : Type _} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iterateN f n (f a)

namespace State

/-! ### Total reachability by iterated closure -/

/-- One closure step: add the successors of everything in `acc`, then dedup. -/
def reachStep (succ : IssueId → List IssueId) (acc : List IssueId) : List IssueId :=
  dedup (acc ++ acc.flatMap succ)

/-- Transitive closure of `seed` under `succ`, iterated `n` times. With
    `n = |presentIssues|` this saturates on any graph (each step adds ≥1 node until
    the present node set is exhausted), so it is total with no acyclicity
    precondition — plain bounded `iterateN`, no well-founded recursion. -/
def reachClosure (succ : IssueId → List IssueId) (n : Nat) (seed : List IssueId) : List IssueId :=
  iterateN (reachStep succ) n seed

/-! ### Critical-path weight (ADR-0004 thm 4) -/

/-- Successors for the weight/`unblocks` direction: the *present* issues `i`
    blocks (dangling targets contribute no node, ADR-0004 thm 4). -/
def blocksSucc (s : State) (i : IssueId) : List IssueId :=
  (s.dependentsOf i).filter (fun j => decide (s.hasIssue j))

/-- The issues transitively reachable from `i` over `blocks` edges, excluding `i`
    (closed issues included — a structural metric, ADR-0004 thm 4). -/
def reachableBlocks (s : State) (i : IssueId) : List IssueId :=
  (reachClosure (blocksSucc s) s.presentIssues.length [i]).erase i

/-- Critical-path weight: the number of distinct issues `i` transitively blocks
    (ADR-0004 thm 4). Total on cyclic graphs (a cycle yields a finite reach set). -/
def weight (s : State) (i : IssueId) : Nat := (s.reachableBlocks i).length

/-! ### Readiness (ADR-0004 thm 4, ADR-0010) -/

/-- The defer conjunct: not deferred past `now` (ADR-0010; absent ⇒ −∞, vacuous). -/
def deferOk (d : IssueData) (now : Instant) : Bool :=
  match d.deferUntilOf with
  | none => true
  | some t => decide (t ≤ now)

/-- A blocker `b` of some issue is *discharged*: dangling (inert, ADR-0003 §5) or
    closed by effective status (epics by rollup, ADR-0004 thm 4). -/
def blockerDischarged (s : State) (b : IssueId) : Bool :=
  !decide (s.hasIssue b) || s.effClosed b

/-- `i` is ready (ADR-0004 thm 4): a materialized, `open`, non-epic, non-deferred
    issue every blocker of which is discharged. -/
def isReady (s : State) (now : Instant) (i : IssueId) : Bool :=
  decide (s.hasIssue i)
  && decide ((s.issueData i).statusOf = Status.Open)
  && !s.isEpic i
  && deferOk (s.issueData i) now
  && (s.blockersOf i).all (s.blockerDischarged ·)

/-! ### Deterministic ranking (ADR-0004 thm 4, vision §Ready ordering) -/

/-- `createdAt` (ADR-0008): the HLC of the issue's `create` add-tag (the min add-tag
    HLC, for determinism if duplicated). -/
def createdAtOf (s : State) (i : IssueId) : Nat :=
  match (s.issues.tagsOf i).toList.map (fun p => p.1.hlc) with
  | [] => 0
  | h :: t => t.foldl Nat.min h

/-- The ranking order (`a` ranks before `b`): priority ↑, then weight ↓, then
    createdAt ↑, then the unique id ↑ — a total order. The queue is reproducible
    across replicas because `rankSort` is a deterministic *function* (so equal states
    give equal output — `rankSort_perm`/`mem_rankSort` pin membership); that its output
    is actually *sorted* by `readyLe` (`readyLe`-totality + insertion-sort sortedness)
    is provable but not yet proved — a tracked residual (overview Proof status).
    (ADR-0004 thm 4.) -/
def readyLe (s : State) (a b : IssueId) : Bool :=
  let pa := (s.issueData a).priorityOf.val
  let pb := (s.issueData b).priorityOf.val
  if pa ≠ pb then decide (pa < pb)
  else if s.weight a ≠ s.weight b then decide (s.weight b < s.weight a)
  else if s.createdAtOf a ≠ s.createdAtOf b then decide (s.createdAtOf a < s.createdAtOf b)
  else decide (TotalOrd.le a b)

/-- Insertion into a `readyLe`-sorted list. -/
def rankInsert (s : State) (x : IssueId) : List IssueId → List IssueId
  | [] => [x]
  | y :: ys => if s.readyLe x y then x :: y :: ys else y :: rankInsert s x ys

/-- Sort by the ranking order. -/
def rankSort (s : State) : List IssueId → List IssueId
  | [] => []
  | x :: xs => rankInsert s x (rankSort s xs)

/-- `ready s now`: the ranked list of workable items — the core feature. -/
def ready (s : State) (now : Instant) : List IssueId :=
  rankSort s (s.presentIssues.filter (s.isReady now ·))

/-! ### `why` and `unblocks` (ADR-0004 thm 10) -/

/-- Successors for `why`: the *live* (present, unclosed) blockers of `i`. -/
def liveBlockersSucc (s : State) (i : IssueId) : List IssueId :=
  (s.blockersOf i).filter (fun b => decide (s.hasIssue b) && !s.effClosed b)

/-- `why s i`: the transitive set of unclosed issues blocking `i` (ADR-0004 thm 10),
    following only live blockers so it stops at a discharged one. -/
def why (s : State) (i : IssueId) : List IssueId :=
  reachClosure (liveBlockersSucc s) s.presentIssues.length (s.liveBlockersSucc i)

/-- The state `s` with issue `i`'s materialized status forced to `Cancelled` — the
    *exact* "what if `i` were closed" projection (ADR-0004 thm 10). It overrides only
    `i`'s status register (`statusOf i` reads only the register value, so the stamp is
    irrelevant — a read-only projection, never merged into the CRDT fold), leaving
    issues, edges, and every other register identical. Manual-cancel precedence makes
    `effectiveStatus i = Cancelled` regardless of whether `i` is an epic, so this
    captures the close's *full* effect — including the rollup ripple through any epic
    ancestor of `i` — which a local "blocked only by `i`" check cannot. -/
def withClosed (s : State) (i : IssueId) : State :=
  let closed : IssueData := { s.issueData i with status := Reg.write ⟨0, 0, 0⟩ Status.Cancelled }
  { s with data := s.data.insert i closed }

/-- `unblocks s now i`: exactly the issues that closing `i` newly makes ready (ADR-0004
    thm 10) — the set difference `ready (withClosed s i) \ ready s`. Defined as the true
    diff (not a local heuristic), so soundness *and* completeness are unconditional
    (`mem_unblocks_iff`): it captures indirect unblocks via epic rollup, which a
    "directly blocked only by `i`" test would miss. -/
def unblocks (s : State) (now : Instant) (i : IssueId) : List IssueId :=
  let readyNow := s.ready now
  ((s.withClosed i).ready now).filter (fun j => decide (j ∉ readyNow))

end State

end Tl.Kernel
