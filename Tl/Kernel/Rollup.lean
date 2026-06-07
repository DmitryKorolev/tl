/-
`Tl.Kernel.Rollup` — `effectiveStatus` and epic-ness (ADR-0003 §3).

An issue with present `parent`-children is an *epic*; its done-ness is *derived*,
not stored: manual cancel takes precedence, else it is Done iff every present
child is closed (by the child's own `effectiveStatus`, so the rollup descends
through nested epics), else Open. A non-epic's effective status is its stored
status.

Totality on cyclic/dangling parent graphs (ADR-0003 §3 / ADR-0004) is via
fuel-bounded recursion: the fuel is the present-issue count, which bounds any
acyclic parent chain, so the rollup is exact on acyclic graphs; a parent *cycle*
exhausts the fuel and falls back to the stored status — and since an epic cannot
be stored-Done, a cycle-trapped epic falls back to not-done (reported by `dep
cycles`, never silently wrong). Dangling children are filtered out as inert
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

/-- Fuel-bounded rollup recursion (ADR-0003 §3); see the module header. -/
def effStatusAux (s : State) : Nat → IssueId → Status
  | 0, i => (s.issueData i).statusOf
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

end State

end Tl.Kernel
