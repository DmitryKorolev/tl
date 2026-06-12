/-
`Tl.Kernel.Rollup` — `effectiveStatus` and epic-ness (ADR-0003 §3).

An issue with present `parent`-children is an *epic*; its done-ness is *derived*,
not stored: manual cancel takes precedence, else it is Done iff every present
child is closed (by the child's own `effectiveStatus`, so the rollup descends
through nested epics), else Open. A non-epic's effective status is its stored
status.

Totality on cyclic/dangling parent graphs (ADR-0003 §3 / ADR-0004) is via
fuel-bounded recursion: the fuel is the present-issue count, which bounds any
acyclic parent chain, so the rollup is exact on acyclic graphs (proved:
`effectiveStatus_epic`, `RollupAcyclic.lean`). A parent *cycle* exhausts the fuel; at
exhaustion (fuel 0) the fallback is **conservative**: a manual `Cancelled` is honoured
(a deliberate close), a *non-epic* reads its stored status, and an *epic* falls back to
`Open` — **never** to its stored status, which a merge could have set to `Done`
(ADR-0002: cross-entity rules are reported, not enforced, so the CLI's status guard is
no merge invariant). `effStatusAux_epic_zero_ne_done`: an epic at fuel 0 is never
`Done`; since a non-closed child makes its parent non-`Done` too, a cycle-trapped epic
can never spuriously read `Done` or discharge a blocker. The cycle is also reported by
`dep cycles`. Dangling children are filtered out as inert
(ADR-0003 §5). The recursion only ever descends the `parent` graph and never calls
back into `ready`/`blockers`, so `ready`'s totality composes from this one.
-/
import Tl.Kernel.State

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-- The present children of `i` (parent edges to existing issues; a parent edge to
    a nonexistent child is inert, ADR-0003 §5). -/
def presentChildren (s : State) (i : IssueId) : List IssueId :=
  (s.childrenOf i).filter (fun c => decide (s.hasIssue c))

/-- `i` is an epic iff it has at least one present child (ADR-0003 §3). It is then
    excluded from `ready` and governed by rollup. -/
def isEpic (s : State) (i : IssueId) : Bool := !(s.presentChildren i).isEmpty

/-- Fuel-bounded rollup recursion (ADR-0003 §3); see the module header. At fuel 0
    (only reachable when the fuel — the present-issue count — is exhausted, i.e. on a
    parent *cycle*) an epic falls back *conservatively* to `Open`, never to its stored
    status: a merge can inject `Done` onto an epic (status legality is a courtesy guard,
    not a merge invariant — ADR-0002), and the rollup must never let a cycle-trapped
    epic read `Done` and so spuriously discharge blockers. A manual `Cancelled` still
    takes precedence (a deliberate close, always honoured); a non-epic still reads its
    stored status. -/
def effStatusAux (s : State) : Nat → IssueId → Status
  | 0, i =>
    if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
    else if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
    else Status.Open
  | fuel + 1, i =>
    if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
    else
      let kids := s.presentChildren i
      if kids.isEmpty then (s.issueData i).statusOf
      else if kids.all (fun c => Status.closed (effStatusAux s fuel c)) then Status.Done
      else Status.Open

/-- The effective (rolled-up) status (ADR-0003 §3), total on cyclic/dangling
    parent graphs. For a non-epic it equals the stored status. -/
def effectiveStatus (s : State) (i : IssueId) : Status :=
  effStatusAux s s.presentIssues.length i

/-- A blocker/child is *discharged* iff its effective status is closed
    (`done`/`cancelled`) — so an epic blocker discharges exactly when it rolls up. -/
def effClosed (s : State) (i : IssueId) : Bool := Status.closed (effectiveStatus s i)

/-! ## The memoized batched rollup (ADR-0003 §3 amendment)

`effectiveStatus` above is the *spec*: fuel-bounded, proved correct, but it
recomputes `presentIssues` (for the fuel) and `presentChildren` (a fresh
`presentEdges` scan) per node per call — Θ(N³) across a `list`. The shipped
read path is the memoized recursion below: the parent-edge view is hoisted
once per pass, `path` (the current descent chain) detects a parent cycle at
the exact node — a global visited set would mistake shared DAG children for
cycles — and `memo` caches completed statuses so each node is evaluated once
per pass. `effStatusAll_find` (RollupMemo.lean) proves the memo pointwise
equal to `effectiveStatus`, so every spec theorem transfers; the structural
once-per-pass property is `rollupVisit_find_hit`. -/

/-- The hoisted parent-edge view: `(parent, child)` for every present `Parent`
    edge whose child is present — computed once per rollup pass. -/
def parentEdges (s : State) : List (IssueId × IssueId) :=
  s.presentEdges.filterMap (fun e =>
    let (f, t, k) := e
    if decide (k = EdgeKind.Parent) && decide (s.hasIssue t) then some (f, t) else none)

/-- Children of `i` per the hoisted view (= `presentChildren i`,
    `kidsOfEdges_parentEdges`). -/
def kidsOfEdges (pe : List (IssueId × IssueId)) (i : IssueId) : List IssueId :=
  (pe.filter (fun p => p.1 == i)).map (·.2)

theorem length_kidsOfEdges_le (pe : List (IssueId × IssueId)) (i : IssueId) :
    (kidsOfEdges pe i).length ≤ pe.length := by
  unfold kidsOfEdges
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- Filter-length monotonicity under predicate implication. -/
theorem length_filter_le_of_imp {α : Type _} (p q : α → Bool)
    (h : ∀ a, q a = true → p a = true) :
    (l : List α) → (l.filter q).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | x :: xs => by
    by_cases hq : q x = true
    · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (h x hq),
        List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (length_filter_le_of_imp p q h xs)
    · rw [List.filter_cons_of_neg hq]
      by_cases hp : p x = true
      · rw [List.filter_cons_of_pos hp, List.length_cons]
        exact Nat.le_succ_of_le (length_filter_le_of_imp p q h xs)
      · rw [List.filter_cons_of_neg hp]
        exact length_filter_le_of_imp p q h xs

/-- Strict decrease of the unvisited measure: additionally excluding a member
    of the filtered list shortens it. -/
theorem length_filter_lt_of_mem {α : Type _} [BEq α] [LawfulBEq α]
    (p : α → Bool) (c : α) : (l : List α) → c ∈ l → p c = true →
    (l.filter (fun x => p x && x != c)).length < (l.filter p).length
  | x :: xs, hc, hpc => by
    have himp : ∀ a, ((fun x => p x && x != c) a = true) → p a = true := fun a ha =>
      ((Bool.and_eq_true ..).mp ha).1
    rcases List.mem_cons.mp hc with rfl | hmem
    · have hneg : ¬ ((fun x => p x && x != c) c = true) := by
        show ¬ ((p c && c != c) = true)
        rw [bne_self_eq_false, Bool.and_false]
        exact Bool.false_ne_true
      rw [List.filter_cons_of_neg (p := fun x => p x && x != c) hneg,
        List.filter_cons_of_pos hpc, List.length_cons]
      exact Nat.lt_succ_of_le (length_filter_le_of_imp p _ himp xs)
    · by_cases hpx : p x = true
      · by_cases hxc : (x != c) = true
        · have hpos : ((fun x => p x && x != c) x = true) := by
            show (p x && x != c) = true
            rw [hpx, hxc]
            rfl
          rw [List.filter_cons_of_pos (p := fun x => p x && x != c) hpos,
            List.filter_cons_of_pos hpx, List.length_cons, List.length_cons]
          exact Nat.succ_lt_succ (length_filter_lt_of_mem p c xs hmem hpc)
        · have hneg : ¬ ((fun x => p x && x != c) x = true) := by
            show ¬ ((p x && x != c) = true)
            intro h
            exact hxc ((Bool.and_eq_true ..).mp h).2
          rw [List.filter_cons_of_neg (p := fun x => p x && x != c) hneg,
            List.filter_cons_of_pos hpx, List.length_cons]
          exact Nat.lt_succ_of_lt (length_filter_lt_of_mem p c xs hmem hpc)
      · have hneg : ¬ ((fun x => p x && x != c) x = true) := fun h => hpx (himp x h)
        rw [List.filter_cons_of_neg (p := fun x => p x && x != c) hneg,
          List.filter_cons_of_neg hpx]
        exact length_filter_lt_of_mem p c xs hmem hpc

/-- Excluding the head of the path is the same filter as filtering by the
    extended path (the measure-preservation step of the descent). -/
theorem filter_path_cons (l : List IssueId) (path : List IssueId) (i : IssueId) :
    l.filter (fun x => !(i :: path).contains x)
      = l.filter (fun x => !path.contains x && x != i) := by
  apply List.filter_congr
  intro x _
  show (!(i :: path).contains x) = (!path.contains x && x != i)
  rw [List.contains_cons, Bool.not_or, Bool.and_comm]
  rfl

mutual

/-- Memoized rollup of one node. `path` is the descent chain (head = the
    immediate parent of `i`); a kid found on it closes a parent cycle of
    non-cancelled epics, whose members are `Open` by
    `effStatusAux_open_on_liveCycle` — so treating it as not-closed is exact,
    not just conservative. Entered only with `i ∉ path`. Terminates
    lexicographically: descending into a fresh present kid shrinks the
    unvisited-present set; walking the kid list shrinks the list. -/
def rollupVisit (s : State) (pe : List (IssueId × IssueId))
    (path : List IssueId) (memo : AMap IssueId Status) (i : IssueId) :
    AMap IssueId Status × Status :=
  match memo.find i with
  | some v => (memo, v)
  | none =>
    if (s.issueData i).statusOf = Status.Cancelled then
      (memo.insert i Status.Cancelled, Status.Cancelled)
    else
      let kids := kidsOfEdges pe i
      if kids.isEmpty then
        let v := (s.issueData i).statusOf
        (memo.insert i v, v)
      else
        let r := rollupKids s pe (i :: path) memo kids
        let v := if r.2 then Status.Done else Status.Open
        (r.1.insert i v, v)
termination_by
  ((s.presentIssues.filter (fun x => !path.contains x && x != i)).length, pe.length + 1)
decreasing_by
  -- visit → kids: the extended path absorbs `i` (equal measure), and the kid
  -- list is bounded by the hoisted edge list
  rw [← filter_path_cons]
  exact Prod.Lex.right _ (Nat.lt_succ_of_le (length_kidsOfEdges_le pe i))

/-- The kid loop: thread the memo left-to-right, conjoin closed-ness. A kid on
    the path is a cycle re-encounter (`Open`, exact — see `rollupVisit`); a
    non-present kid cannot arise from `kidsOfEdges` and reads its stored
    status without recursing (defensive arm, unreachable in `effStatusAll`). -/
def rollupKids (s : State) (pe : List (IssueId × IssueId))
    (path : List IssueId) (memo : AMap IssueId Status) (cs : List IssueId) :
    AMap IssueId Status × Bool :=
  match cs with
  | [] => (memo, true)
  | c :: cs' =>
    let r :=
      match memo.find c with
      | some v => (memo, v)
      | none =>
        if hcon : path.contains c then (memo, Status.Open)
        else if hpres : s.hasIssue c then rollupVisit s pe path memo c
        else (memo, (s.issueData c).statusOf)
    let r' := rollupKids s pe path r.1 cs'
    (r'.1, Status.closed r.2 && r'.2)
termination_by
  ((s.presentIssues.filter (fun x => !path.contains x)).length, cs.length)
decreasing_by
  · -- kids → visit: a fresh present kid strictly shrinks the unvisited set
    apply Prod.Lex.left
    apply length_filter_lt_of_mem
    · exact (Tl.Crdt.OrSet.mem_presentElements s.issues c).mpr hpres
    · show (!path.contains c) = true
      cases hb : path.contains c with
      | true => exact absurd hb hcon
      | false => rfl
  · -- kids → kids: same path, shorter list
    exact Prod.Lex.right _ (Nat.lt_succ_self _)

end

/-- The batched rollup: one memoized pass over every present issue. The
    shipped form for the read path (ADR-0003 §3 amendment); pointwise equal to
    `effectiveStatus` (`effStatusAll_find`, RollupMemo.lean). -/
def effStatusAll (s : State) : AMap IssueId Status :=
  let pe := s.parentEdges
  s.presentIssues.foldl (fun memo i => (rollupVisit s pe [] memo i).1) AMap.empty

/-- Effective status through a rollup map, with the spec as the (dangling-id)
    fallback. With `m = effStatusAll s` this *is* `effectiveStatus`
    (`effStatusWith_eq`), the map just makes it one lookup. -/
def effStatusWith (m : AMap IssueId Status) (s : State) (i : IssueId) : Status :=
  (m.find i).getD (s.effectiveStatus i)

/-- `effClosed` through a rollup map. -/
def effClosedWith (m : AMap IssueId Status) (s : State) (i : IssueId) : Bool :=
  Status.closed (effStatusWith m s i)

end State

end Tl.Kernel
