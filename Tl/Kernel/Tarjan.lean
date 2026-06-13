/-
`Tl.Kernel.Tarjan` — the unverified fast SCC core.

This is an iterative Tarjan strongly-connected-components implementation
carrying no theorems. Its output is validated at runtime by the proved
certificate checker in `Tl/Kernel/SccFast.lean`, with fallback to the proved
slow path in `Tl/Kernel/CyclesFast.lean`, so kernel *correctness* never
depends on this file — only *speed* does, and that is covered by tests. The
obligations here are therefore totality and determinism: a bug may produce
wrong output (which the checker rejects), but never non-termination or a
panic. Hence the explicit fuel parameter, the absence of panicking lookups,
and iteration strictly in input-list order (never over a hash container).
-/
import Tl.Kernel.State
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

namespace Tl.Kernel

/-- Mutable-style state threaded through the iterative Tarjan loop. -/
private structure TarjanState where
  index : Std.HashMap IssueId Nat
  low : Std.HashMap IssueId Nat
  onStack : Std.HashSet IssueId
  stack : List IssueId
  next : Nat
  /-- Completed components, newest first; reversed once at the end so the
      result is in emission (pop) order. -/
  comps : List (List IssueId)

private def TarjanState.initial : TarjanState :=
  { index := ∅, low := ∅, onStack := ∅, stack := [], next := 0, comps := [] }

/-- Discover node `v`: assign it the next index, initialize its low-link,
    and push it on the Tarjan stack. -/
private def TarjanState.push (st : TarjanState) (v : IssueId) : TarjanState :=
  { st with
    index := st.index.insert v st.next
    low := st.low.insert v st.next
    onStack := st.onStack.insert v
    stack := v :: st.stack
    next := st.next + 1 }

/-- Pop the Tarjan stack down to and including root `v`, unmarking
    `onStack`. Returns the component (root first, then the rest in push
    order), the remaining stack, and the updated `onStack` set. The empty
    case is unreachable when `v` is on the stack — as the algorithm
    guarantees — and degrades to returning what was popped, keeping the
    function total either way. -/
private def tarjanPop (v : IssueId) :
    List IssueId → Std.HashSet IssueId → List IssueId →
      List IssueId × List IssueId × Std.HashSet IssueId
  | [], onStack, acc => (acc, [], onStack)
  | w :: rest, onStack, acc =>
    let onStack := onStack.erase w
    if w == v then (w :: acc, rest, onStack)
    else tarjanPop v rest onStack (w :: acc)

/-- One DFS worklist. Each frame is a discovered node paired with its
    not-yet-scanned successors (`succ` is called once, at push time). Every
    step consumes one fuel and either scans one pending successor (possibly
    pushing a new frame) or retires one finished frame, so fuel linear in
    nodes + edges suffices; on exhaustion the state so far is returned —
    truncated output, which the downstream certificate checker rejects. -/
private def tarjanLoop (succ : IssueId → List IssueId) :
    Nat → List (IssueId × List IssueId) → TarjanState → TarjanState
  | 0, _, st => st
  | _ + 1, [], st => st
  | fuel + 1, (v, []) :: parents, st =>
    -- Frame finished: emit an SCC if `v` is a root, then propagate the
    -- low-link to the parent frame, if any.
    let lowV := (st.low[v]?).getD 0
    let st :=
      if lowV == (st.index[v]?).getD 0 then
        let (comp, stack, onStack) := tarjanPop v st.stack st.onStack []
        { st with stack, onStack, comps := comp :: st.comps }
      else st
    match parents with
    | [] => tarjanLoop succ fuel [] st
    | (u, ws) :: rest =>
      let lowU := (st.low[u]?).getD 0
      let st := { st with low := st.low.insert u (Nat.min lowU lowV) }
      tarjanLoop succ fuel ((u, ws) :: rest) st
  | fuel + 1, (v, w :: ws) :: parents, st =>
    if st.index.contains w then
      -- Back edge into the current stack lowers `v`'s low-link; an edge to
      -- an already-emitted component is skipped.
      let st :=
        if st.onStack.contains w then
          let lowV := (st.low[v]?).getD 0
          let idxW := (st.index[w]?).getD 0
          { st with low := st.low.insert v (Nat.min lowV idxW) }
        else st
      tarjanLoop succ fuel ((v, ws) :: parents) st
    else
      tarjanLoop succ fuel ((w, succ w) :: (v, ws) :: parents) (st.push w)

/-- Strongly connected components, in Tarjan emission order, of the finite
    graph `V = nodes ∪ {edge targets}`, `E = {(v, w) | v ∈ nodes, w ∈ succ v}`.
    The world is closed over `nodes`: `succ` is consulted only for vertices in
    `nodes`, and a successor outside `nodes` (a dangling edge target) is
    visited as a sink — emitted as its own singleton SCC, never expanded.
    Emission order: for every edge `u → w`, the component of `w` appears at a
    position ≤ the component of `u`. Deterministic: roots in `nodes` order,
    successors in `succ` list order.

    Fuel: one unit per scanned successor plus one per retired frame. At most
    `|E| ≤ edges` successors are ever scanned and at most
    `|V| ≤ nodes + edges` frames retired, so `2 * (nodes + edges)`
    unconditionally over-covers any single root's DFS (and each root gets the
    full budget). -/
def tarjanSCC (nodes : List IssueId) (succ : IssueId → List IssueId) :
    List (List IssueId) :=
  let inNodes : Std.HashSet IssueId := nodes.foldl (·.insert ·) ∅
  -- Closed world: vertices outside `nodes` become sinks (frame `(w, [])`).
  let succ' := fun v => if inNodes.contains v then succ v else []
  let totalEdges := nodes.foldl (fun n v => n + (succ v).length) 0
  -- `2 * (nodes + edges)` over-covers any root's DFS (comment above); the
  -- `+ 8` is constant slack for the seed push and `fuel + 1`-shaped decrements,
  -- so exhaustion (→ truncated output → certificate rejection) is unreachable
  -- on a real graph, never an off-by-one.
  let fuel := 2 * (nodes.length + totalEdges) + 8
  let st := nodes.foldl (init := TarjanState.initial) fun st v =>
    if st.index.contains v then st
    else tarjanLoop succ' fuel [(v, succ' v)] (st.push v)
  st.comps.reverse

end Tl.Kernel
