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

end State

end Tl.Kernel
