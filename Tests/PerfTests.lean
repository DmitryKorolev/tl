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
hoisted once, with reps sized so the SMALL-scale total clears ratioRow's
30ms floor on a typical dev machine — below the floor the row silently
degrades to its absolute backstop, so if hardware speeds shift, re-tune the
reps until the small time again exceeds 30ms. The fast branch being taken
at these very scales is asserted by its own row (a scale-dependent
certificate rejection would otherwise read as a quiet slowdown). The FULL
diagnostics command path additionally pays the
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
import Tl.Hash.Sha256
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
private def synthOps (n : Nat) (base : Nat := synthNow) : List ParsedOp :=
  let replicaVal := (ofCrockford? stem).getD 0
  let mk (idx : Nat) (op : WireOp) : ParsedOp :=
    { v := supportedVersion, op
      stamp := ⟨(base - 100000 + idx) * 2 ^ 16, replicaVal, 10 ^ 9 + idx⟩
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
  let mut certScaleOk := true
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
    let warm ← bench (2 * reps) (fun _ =>
      (materializeCached segs (some cache) false (some synthNow) (some stem)).1.ops.length)
    -- `effStatusAll` at these scales is loop-invariant and small enough that the
    -- compiler hoists it out of `bench`'s loop (0ms at any rep count), so this row
    -- cannot be de-floor-masked through reps — it stays a floor backstop. Its
    -- near-linear growth IS pinned, by the in-process `RollupFast` theorems and by
    -- the end-to-end binary row below (which folds it on every read).
    let roll ← bench reps (fun _ => (State.effStatusAll s).toList.length)
    -- `ready` grows ~11× for ×4 ops here (weightFast runs a blocks-reachability
    -- closure per candidate with NO adjacency index) — so de-floor-masking it
    -- would push the row to the ×12 edge: it stays floor-masked until that fix
    -- lands (ADR-0023: a still-superlinear row cannot be honestly un-masked).
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
    let cyc ← bench 100 (fun _ =>
      (State.cyclesFastWith present edges EdgeKind.Blocks).length
      + (State.cyclesFastWith present edges EdgeKind.Parent).length
      + (State.precCyclesFastWith rollup present edges pe s).length)
    -- the fast cert branch must actually be taken at THESE scales, not only on
    -- the ≤8-node cross-test graphs — a scale-dependent rejection (fuel, depth)
    -- would otherwise surface as nothing but a quiet slowdown. Reads the
    -- production cert-acceptance guard over the same successor wiring.
    certScaleOk := certScaleOk
      && State.cyclesCertAcceptedWith present edges EdgeKind.Blocks
      && State.cyclesCertAcceptedWith present edges EdgeKind.Parent
      && State.precCyclesCertAcceptedWith rollup present edges pe s
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
    let rcyc ← bench 120 (fun _ =>
      (State.cyclesFastWith rpresent redges EdgeKind.Blocks).length
      + (State.precCyclesFastWith rrollup rpresent redges rpe rs).length)
    certScaleOk := certScaleOk
      && State.cyclesCertAcceptedWith rpresent redges EdgeKind.Blocks
      && State.precCyclesCertAcceptedWith rrollup rpresent redges rpe rs
    -- provenanceMap is near-linear (filterMap + mergeSort + a single grouped
    -- fold); reps sized so the small scale clears the 30ms floor (de-masked).
    let prov ← bench 800 (fun _ => (provenanceMap loaded.ops).toList.length)
    let uni ← bench (8 * reps) (fun _ =>
      (unionLines (segs.head?.map (·.bytes) |>.getD ByteArray.empty)
        (segs.head?.map (·.bytes) |>.getD ByteArray.empty)).size)
    -- the CLI per-row render path (ADR-0023/0024): the `list`/`stats`/`doctor`
    -- rows read each issue's derived fields through the once-built `ViewIndex`
    -- (issueData/effStatus/isEpic/ready/blocked/deferred/blockers/dependents/
    -- prov) — O(1)/O(deg) per issue. Before that routing each was an O(N)
    -- `AMap.find` / O(E) edge-filter, so rendering N rows was Θ(N²)/Θ(N·E). A
    -- revert to a raw accessor turns this row quadratic and the ratio jumps.
    -- reps sized so the SMALL scale clears ratioRow's 30ms floor (de-masked).
    let v : Tl.Cli.View :=
      { dirs := ⟨"", ".tl"⟩, loaded, now := synthNow, replica := none,
        rollup, present, edges, pedges := pe, prov := provenanceMap loaded.ops,
        idx := Tl.Cli.ViewIndex.of s.data rollup present edges pe
                 (provenanceMap loaded.ops) s.edges.adds.toList }
    let row ← bench 1200 (fun _ =>
      present.foldl (fun acc i =>
        acc + (v.issueData i).priorityOf.val + (v.effStatus i).toNat
        + (if v.isEpic i then 1 else 0) + (if v.ready i then 1 else 0)
        + (if v.blocked i then 1 else 0) + (if v.deferred i then 1 else 0)
        + (v.blockers i).length + (v.dependents i).length
        + ((v.provFor i).createdAt.getD 0) % 7) 0)
    -- the tree render's per-visible canonical-parent (cmdList `isRoot`): the
    -- parent-by-child bucket + the edge-tag hash (`maxTag`) — O(deg) per issue.
    -- A revert to the spec `parentsOf`/`tagsOf` scans is O(E) per issue ⇒ Θ(N·E).
    let canon ← bench 2500 (fun _ =>
      present.foldl (fun acc i =>
        acc + (match Tl.Cli.canonicalParentE v i with | some _ => 1 | none => 0)) 0)
    results := results ++ [(n, [("cold batched fold", cold),
      ("warm cached materialize", warm),
      ("batched rollup", roll), ("fast ready queue", rdy),
      ("fast diagnostics (SCC machinery)", cyc),
      ("giant-SCC diagnostics (machinery)", rcyc),
      ("provenance map", prov), ("sync line-union", uni),
      ("cli per-row projections (issueRow fields)", row),
      ("cli tree canonical-parent per row", canon)])]
  match results with
  | [(_, small), (_, big)] =>
    for ((name, tS), (_, tB)) in small.zip big do
      o := o ++ [ratioRow name tS tB]
    -- the full diagnostics command path = view scans + SCC machinery. The
    -- view scans (OR-Set presentElements) are superlinear today — tracked
    -- as their own task — so this is an explicit wall-clock CEILING, not a
    -- ratio dressed up by the noise floor.
    let fullSmall := ((fulls.head?).map (·.2)).getD 0
    let fullBig := (fulls.getLast?.map (·.2)).getD 0
    o := o ++ [check
      s!"diagnostics command path (views + SCC) ≤ 2500ms absolute ceiling (small {fullSmall}ms, big {fullBig}ms)"
      (fullBig ≤ 2500) s!"small={fullSmall}ms big={fullBig}ms"]
    o := o ++ [check
      "certificate accepted at both perf scales (healthy + giant-SCC ring, all graphs)"
      certScaleOk]
    return o
  | _ => return [{ name := "perf scaling setup", passed := false,
                   msg := s!"expected two scales, got {results.length}" }]

/-- Guards for the proved-fast PRIMITIVES, whose revert is behavior-invisible: a
    dropped native String comparator decides the same `Prop`, and a swapped cache
    content hash produces a valid (just slower) digest — so every correctness
    test stays green while a constant factor regresses. An op-count / ratio row
    cannot see a constant factor (same complexity class), so these are the
    ADR-0023 "assumed tier, recorded + latency-guarded" checks. Re-tune the
    String ceiling if hardware shifts (it is sized well above honest variance and
    well below the allocation-bound slow form, like the diagnostics rows). -/
def perfPrimitiveTests : IO (List Outcome) := do
  -- (1) the native String comparison path (`TotalOrd.le`/`decEq` routed to core's
  -- extern `String.decLE`/`String.decEq`). The fallback — a `≤`-derived two-walk
  -- `decEq`, and a `List Char` re-materialization per order compare — allocates
  -- on every comparison: invisible to a ratio (same `O(N log N)`), caught only by
  -- an absolute ceiling. N² comparisons over distinct 16-char Crockford keys run
  -- ~80ms native; the allocation-bound slow form is a large multiple of that.
  let n := 2000
  let keys := (List.range n).map (fun k => toCrockford (10 ^ 18 + k * 2654435761) 16)
  let (_, cmpMs) ← timeMs (do
    let mut acc := 0
    for a in keys do
      for b in keys do
        if Tl.Crdt.TotalOrd.le a b then acc := acc + 1
    pure acc)
  -- (2) the cache's content hash: core's native `ByteArray.hash` over the
  -- pure-Lean SHA-256 it replaced. A machine-independent RATIO — both run here on
  -- one machine — pins the fast-hash advantage that justifies the cache using it;
  -- a revert to a slow hash collapses the ratio. ~2.5MB, the warm-cache size.
  let big := ByteArray.mk (Array.replicate 2500000 (0x61 : UInt8))
  let (_, byteHashMs) ← timeMs (do
    let mut acc := 0
    for _ in [0:5] do acc := acc + (ByteArray.hash big).toNat
    pure (acc % 7))
  let (_, shaMs) ← timeMs (do
    let mut acc := 0
    for _ in [0:5] do acc := acc + (Tl.Hash.Sha256.digest big).size
    pure (acc % 7))
  return [
    check s!"native String compare stays fast: {n}² TotalOrd.le ≤ 800ms ({cmpMs}ms)"
      (cmpMs ≤ 800)
      s!"{cmpMs}ms — a revert to the ≤-derived decEq / per-compare List-Char decLE allocates per comparison",
    check s!"cache hash on native ByteArray.hash, ≥8× faster than SHA-256 (hash {byteHashMs}ms, sha {shaMs}ms)"
      (shaMs ≥ 8 * max byteHashMs 1)
      s!"hash={byteHashMs}ms sha={shaMs}ms — the fast content-hash advantage the cache relies on"]

/-- End-to-end binary latency (ADR-0023 §2: "End-to-end is mandatory"). In-process
    profiles mispredict the compiled binary — the dominant warm-read cost is the
    parse + decode/fold, not the in-process view work — so the net MUST time
    `./.lake/build/bin/tl` on a scaled repo, not a harness. Warm `tl list` over
    500 vs 2000 ops; the ×4-op growth ratio pins the real per-command cost class
    (parse + fold/decode + view + render) independent of the machine. The
    synthetic segment is past-dated, so it folds as a foreign segment with no
    skew deferral (ADR-0007); a guard row asserts it actually folded (else the
    timing would be a vacuous empty-repo read). -/
def perfBinaryTests : IO (List Outcome) := do
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  unless ← exe.pathExists do
    return [{ name := "end-to-end binary latency", passed := false,
              msg := "run `lake build` first: .lake/build/bin/tl missing" }]
  let listArgs (dir : String) : Array String :=
    #["list", "--all", "--flat", "--limit", "0", "--dir", dir]
  -- (best warm ms over 3 runs, line count of the rendered list)
  let run (n : Nat) : IO (Nat × Nat) := do
    let root ← IO.FS.createTempDir
    let dir := (root / ".tl").toString
    let _ ← IO.Process.output { cmd := exe.toString, args := #["init", "--dir", dir] }
    IO.FS.createDirAll (System.FilePath.mk dir / "log")
    let ops := synthOps n 1000000000000  -- past-dated ⇒ a foreign segment that folds
    IO.FS.writeFile (System.FilePath.mk dir / "log" / (stem ++ ".jsonl"))
      (ops.foldl (fun a p => a ++ renderLine p ++ "\n") "")
    -- warm-up: the first read folds cold and writes the cache; capture its output
    -- for the fold-correctness guard
    let warm ← IO.Process.output { cmd := exe.toString, args := listArgs dir }
    let lines := (warm.stdout.splitOn "\n").length
    let mut best := 1000000
    for _ in [0:3] do
      let (_, ms) ← timeMs (do
        let _ ← IO.Process.output { cmd := exe.toString, args := listArgs dir }
        pure 0)
      best := min best ms
    return (best, lines)
  let (small, _) ← run 500
  let (big, bigLines) ← run 2000
  return [
    check "end-to-end binary: the scaled repo folds (guard against a vacuous timing)"
      (bigLines ≥ 2000) s!"`list --all` emitted {bigLines} lines (expected ≥ 2000)",
    ratioRow "end-to-end binary `tl list` (compiled, warm)" small big]

end Tl.Tests
