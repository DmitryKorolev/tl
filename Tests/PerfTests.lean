/-
`Tests.PerfTests` — scaling assertions over synthetic logs (the standing
algorithmic-efficiency principle, CLAUDE.md Code rules, enforced in CI).

Every workhorse runs at two op scales (100 and 400, ×4) with a ratio
assertion: growth must stay far below quadratic (×16) — a generous ×12 with
a small-scale floor, so a regression to an accidental quadratic fails loudly
while honest machine noise on a near-linear path does not (the
timing-flake-proof intent; per-call counters would need kernel hooks the
proofs do not carry).

Covered: the COLD fold (`foldFast`, a full refold with no cache), the warm
cached materialize (the suffix-fold read path), the batched rollup
(`effStatusAll`), the fast queue (`readyFast`), the fast diagnostics
(`cyclesFast`/`precCyclesFast`), the provenance map, and the sync line-union.
The cold fold is now near-linear — batched canonical construction (mergeSort +
adjacent collapse, O(N log N), `foldFast_eq_fold`) replaced the per-op
positional insert (the old Θ(ops×issues)) — so it is asserted by the ×4-ops
ratio like the other fast paths.

The diagnostics run the certificate path (Tarjan + proved checker,
`SccFast.lean`/`CyclesFast.lean`) and get ratio rows measured twice: on the
healthy acyclic fixture (cyclic set empty — the dogfooding profile) and on
a blocks-ring over every id (one giant SCC — the shape the old per-node
closure was Θ(V·(V+E)) on). Both bench the SCC machinery over state views
hoisted once, with enough reps to clear the 30ms noise floor — real ratios,
not floor-masked. The FULL diagnostics command path additionally pays the
OR-Set view scans (`presentElements`), which are superlinear today and
tracked as their own task; that total is pinned by an explicit absolute
CEILING row, not a ratio. If the certificate were ever rejected, the
fallback's quadratic cost would blow the machinery ratios — and the
fast-branch-taken tests in `CrossTests` catch it sooner and by name.
-/
import Tl.Store.Cache
import Tl.Kernel.ReadyFast
import Tl.Kernel.CyclesFast
import Tl.Cli.Project
import Tl.Sync.Merge
import Tests.Harness

namespace Tl.Tests

open Tl.Store
open Tl.Format
open Tl.Kernel
open Tl.Cli (provenanceMap)
open Tl.Sync (unionLines)

private def stem : String := "0123456789abc"

private def synthNow : Nat := 2000000000000

/-- A synthetic id pool of `n` distinct 16-char Crockford ids. -/
private def synthId (k : Nat) : String :=
  toCrockford (10 ^ 18 + k) 16

/-- `n` ops: a create per id, a parent edge per non-root (chains of 8 with
    occasional extra parents — diamonds), a blocks edge per pair neighbor,
    and a close per eighth id — enough graph structure that every measured
    path does real work. -/
private def synthOps (n : Nat) : List ParsedOp :=
  let replicaVal := (ofCrockford? stem).getD 0
  let mk (idx : Nat) (op : WireOp) : ParsedOp :=
    { v := supportedVersion, op
      stamp := ⟨(synthNow - 100000 + idx) * 2 ^ 16, replicaVal, 10 ^ 9 + idx⟩
      actor := some "perf" }
  (List.range n).flatMap (fun k =>
    let id := synthId k
    let creat := mk (4 * k) (.create id { title := some s!"t{k}" })
    let parents :=
      if k % 8 == 0 then []
      else [mk (4 * k + 1) (.depAdd (synthId (k - 1), id, EdgeKind.Parent))]
        ++ (if k % 5 == 0 then
              [mk (4 * k + 2) (.depAdd (synthId (k / 2), id, EdgeKind.Parent))]
            else [])
    let blocks :=
      if k % 3 == 0 && k > 0 then
        [mk (4 * k + 3) (.depAdd (id, synthId (k - 1), EdgeKind.Blocks))]
      else []
    -- the open working set stays bounded (~32, the dogfooding profile): the
    -- epic's regressions were ops-growth at a small working set, and `ready`
    -- is inherently per-open-candidate work — an unbounded open set would
    -- measure the workload's size, not a regression
    let closes :=
      if k ≥ 32 then [mk (4 * n + k) (.close id .Done)] else []
    creat :: parents ++ blocks ++ closes)

/-- A blocks-ring over every id — one giant SCC, all issues open: the
    dense-cycle stress for the diagnostics. -/
private def ringOps (n : Nat) : List ParsedOp :=
  let replicaVal := (ofCrockford? stem).getD 0
  let mk (idx : Nat) (op : WireOp) : ParsedOp :=
    { v := supportedVersion, op
      stamp := ⟨(synthNow - 100000 + idx) * 2 ^ 16, replicaVal, 10 ^ 9 + idx⟩
      actor := some "perf" }
  (List.range n).flatMap (fun k =>
    [mk (2 * k) (.create (synthId k) { title := some s!"r{k}" }),
     mk (2 * k + 1) (.depAdd (synthId k, synthId ((k + 1) % n), EdgeKind.Blocks))])

private def segsOf (ops : List ParsedOp) : List SegmentData :=
  [{ replicaId := stem
     bytes := (ops.foldl (fun a p => a ++ renderLine p ++ "\n") "").toUTF8 }]

private def timeMs (act : IO Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← act
  let t1 ← IO.monoMsNow
  return (r, t1 - t0)

/-- Run `act` `reps` times, observing its Nat result so the work cannot be
    elided; returns total ms. -/
private def bench (reps : Nat) (act : Unit → Nat) : IO Nat := do
  let (acc, ms) ← timeMs (do
    let mut acc := 0
    for _ in [0:reps] do
      acc := acc + act ()
    return acc)
  -- consume acc through IO so the loop cannot be dropped
  if acc == 0xffffffff then IO.println "" else pure ()
  return ms

/-- One scaling row: the ×4-op growth must stay under ×12 (quadratic is ×16)
    with a 30ms floor against timer noise, plus a generous absolute ceiling. -/
private def ratioRow (name : String) (tSmall tBig : Nat) : Outcome :=
  let floor := max tSmall 30
  check s!"{name}: ×4 ops grows ≤ ×12 (small {tSmall}ms, big {tBig}ms)"
    (tBig ≤ 12 * floor && tBig ≤ 8000)
    s!"small={tSmall}ms big={tBig}ms"

def perfTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let scales := [(100, 4), (400, 4)]
  let mut results : List (Nat × List (String × Nat)) := []
  let mut fulls : List (Nat × Nat) := []
  for (n, reps) in scales do
    let ops := synthOps n
    let segs := segsOf ops
    -- setup: one cold fold per scale to seed the cache for the warm/rollup rows
    let (loaded, cache?) := materializeCached segs none false (some synthNow) (some stem)
    let cache := cache?.getD ⟨[], State.empty⟩
    let s := loaded.state
    let rollup := s.effStatusAll
    -- the COLD fold (no cache ⇒ a full refold through `foldFast`): now batched
    -- canonical construction (mergeSort + collapse, O(N log N)), so it is
    -- asserted near-linear like the other fast paths — the per-op positional
    -- insert (the old Θ(ops×issues)) is gone (foldFast_eq_fold)
    let cold ← bench reps (fun _ =>
      (materializeCached segs none false (some synthNow) (some stem)).1.ops.length)
    let warm ← bench reps (fun _ =>
      (materializeCached segs (some cache) false (some synthNow) (some stem)).1.ops.length)
    let roll ← bench reps (fun _ => (State.effStatusAll s).toList.length)
    let rdy ← bench 1 (fun _ => (State.readyFast rollup s synthNow).length)
    -- the diagnostics machinery (the certificate SCC path) over state views
    -- hoisted once: adjacency bucketing, presence/rollup hash views, Tarjan,
    -- the checker, and witness reconstruction — the cycleCount shape (three
    -- graphs). The full command path additionally pays the OR-Set view
    -- scans (presentIssues/presentEdges/parentEdges), superlinear today and
    -- tracked as their own work — the ceiling row below pins that total.
    let present := s.presentIssues
    let edges := s.presentEdges
    let pe := s.parentEdges
    let cyc ← bench 25 (fun _ =>
      let pset := hashSetOf present
      let succB := State.succOfAdj (State.kindAdj edges EdgeKind.Blocks) pset
      let succP := State.succOfAdj (State.kindAdj edges EdgeKind.Parent) pset
      let succPrec := State.precSuccH (hashAssoc rollup.toList)
        (State.blocksAdj edges) (bucketBy pe) pset s
      (State.sccWitnessesT present present.length succB).length
      + (State.sccWitnessesT present present.length succP).length
      + (State.sccWitnessesT present present.length succPrec).length)
    let fullCyc ← bench 1 (fun _ =>
      (State.cyclesFast s EdgeKind.Blocks).length
      + (State.cyclesFast s EdgeKind.Parent).length
      + (State.precCyclesFast rollup s).length)
    fulls := fulls ++ [(n, fullCyc)]
    -- the dense-cycle stress: one giant SCC over all ids
    let rsegs := segsOf (ringOps n)
    let (rloaded, _) := materializeCached rsegs none false (some synthNow) (some stem)
    let rs := rloaded.state
    let rrollup := rs.effStatusAll
    let rpresent := rs.presentIssues
    let redges := rs.presentEdges
    let rpe := rs.parentEdges
    let rcyc ← bench 10 (fun _ =>
      let pset := hashSetOf rpresent
      let succB := State.succOfAdj (State.kindAdj redges EdgeKind.Blocks) pset
      let succPrec := State.precSuccH (hashAssoc rrollup.toList)
        (State.blocksAdj redges) (bucketBy rpe) pset rs
      (State.sccWitnessesT rpresent rpresent.length succB).length
      + (State.sccWitnessesT rpresent rpresent.length succPrec).length)
    let prov ← bench reps (fun _ => (provenanceMap loaded.ops).toList.length)
    let uni ← bench reps (fun _ =>
      (unionLines (segs.head?.map (·.bytes) |>.getD ByteArray.empty)
        (segs.head?.map (·.bytes) |>.getD ByteArray.empty)).size)
    results := results ++ [(n, [("cold batched fold", cold),
      ("warm cached materialize", warm),
      ("batched rollup", roll), ("fast ready queue", rdy),
      ("fast diagnostics (SCC machinery)", cyc),
      ("giant-SCC diagnostics (machinery)", rcyc),
      ("provenance map", prov), ("sync line-union", uni)])]
  match results with
  | [(_, small), (_, big)] =>
    for ((name, tS), (_, tB)) in small.zip big do
      o := o ++ [ratioRow name tS tB]
    -- the full diagnostics command path = view scans + SCC machinery. The
    -- view scans (OR-Set presentElements) are superlinear today — tracked
    -- as their own task — so this is an explicit wall-clock CEILING, not a
    -- ratio dressed up by the noise floor.
    let fullBig := (fulls.getLast?.map (·.2)).getD 0
    o := o ++ [check
      s!"diagnostics command path (views + SCC) ≤ 2500ms absolute ceiling ({fullBig}ms)"
      (fullBig ≤ 2500) s!"big={fullBig}ms"]
    return o
  | _ => return [{ name := "perf scaling setup", passed := false,
                   msg := s!"expected two scales, got {results.length}" }]

end Tl.Tests
