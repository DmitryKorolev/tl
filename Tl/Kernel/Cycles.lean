/-
`Tl.Kernel.Cycles` — the cycle diagnostic (ADR-0003 §2, ADR-0004 thm 6).

Acyclicity is reported, never enforced (a CRDT merge cannot reject the edge that
closes a cycle). `cycles s kind` reports, per kind `∈ {blocks, parent}`, one
witness — the node set of each strongly-connected component that contains a cycle.
`precCycles s` additionally reports *readiness-deadlock* `≺`-cycles (pure-`blocks`
or mixed blocks+parent through epic rollup, ADR-0004 thm 5/6), so a stuck live set
is never undiagnosed.

All detection is total on arbitrary graphs: a node is on a cycle iff it is
reachable from its own successors (bounded `reachClosure`), and SCCs are grouped
by mutual reachability — no acyclicity precondition, no well-founded obligation.
Witnesses are deterministic (present ids are sorted), so replicas agree.
-/
import Tl.Kernel.Ready

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ### Generic SCC detection over a successor relation -/

/-- The closure of `{v}` under `succ` (the nodes `v` reaches, plus `v`). -/
def reachSet (s : State) (succ : IssueId → List IssueId) (v : IssueId) : List IssueId :=
  reachClosure succ s.presentIssues.length [v]

/-- `u` and `v` are in the same SCC: each reaches the other. -/
def sameSCC (s : State) (succ : IssueId → List IssueId) (u v : IssueId) : Bool :=
  decide (u ∈ s.reachSet succ v) && decide (v ∈ s.reachSet succ u)

/-- `v` is on a cycle: reachable from one of its own successors. -/
def onCycle (s : State) (succ : IssueId → List IssueId) (v : IssueId) : Bool :=
  decide (v ∈ reachClosure succ s.presentIssues.length (succ v))

/-- Group the cyclic nodes into SCC witnesses, one per component, deterministically
    (input is id-sorted, each witness is a sorted sublist). -/
def groupSCCGo (s : State) (succ : IssueId → List IssueId) (cyclic : List IssueId) :
    List IssueId → List IssueId → List (List IssueId)
  | [], _ => []
  | v :: vs, covered =>
    if v ∈ covered then groupSCCGo s succ cyclic vs covered
    else
      let scc := cyclic.filter (fun u => s.sameSCC succ u v)
      scc :: groupSCCGo s succ cyclic vs (scc ++ covered)

/-- One witness (the node set) per cyclic SCC of `succ`. -/
def sccWitnesses (s : State) (succ : IssueId → List IssueId) : List (List IssueId) :=
  let cyclic := s.presentIssues.filter (s.onCycle succ)
  groupSCCGo s succ cyclic cyclic []

/-! ### Per-kind structural cycles (ADR-0003 §2, ADR-0004 thm 6) -/

/-- Successors over outgoing kind-`k` edges (`from = i`). -/
def kindSucc (s : State) (k : EdgeKind) (i : IssueId) : List IssueId :=
  (s.presentEdges.filter (fun e => decide (e.2.2 = k ∧ e.1 = i))).map (·.2.1)

/-- The cyclic SCCs of the kind-`k` edge graph (one node-set witness each). A
    `blocks` cycle is mutual blocking; a `parent` cycle is an epic that is its own
    ancestor (ADR-0003 §2). -/
def cycles (s : State) (k : EdgeKind) : List (List IssueId) :=
  s.sccWitnesses (s.kindSucc k)

/-! ### Readiness-deadlock `≺`-cycles (ADR-0004 thm 5/6) -/

/-- The live (present, unclosed) children of epic `i`. -/
def liveChildrenSucc (s : State) (i : IssueId) : List IssueId :=
  (s.presentChildren i).filter (fun c => !s.effClosed c)

/-- The `≺` wait relation's successors: `i` waits on its live `blocks`-blockers,
    and — if `i` is an epic — on its live children (rollup-wait). Descends through
    nested epics by the same parent walk `effectiveStatus` uses (ADR-0004 thm 5). -/
def precSucc (s : State) (i : IssueId) : List IssueId :=
  s.liveBlockersSucc i ++ (if s.isEpic i then s.liveChildrenSucc i else [])

/-- The readiness-deadlock `≺`-cycles — the only tool-pathological stuck states
    (ADR-0004 thm 5/6); pure-`blocks` or mixed blocks+parent. One witness per SCC. -/
def precCycles (s : State) : List (List IssueId) :=
  s.sccWitnesses s.precSucc

/-! ### Summary predicates -/

/-- Whether the kind-`k` graph has any cycle. -/
def hasCycle (s : State) (k : EdgeKind) : Bool := !(s.cycles k).isEmpty

/-- Whether the live working set is in a readiness deadlock. -/
def hasDeadlock (s : State) : Bool := !s.precCycles.isEmpty

end State

end Tl.Kernel
