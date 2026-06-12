/-
`Tests.CrossTests` — the two cross-checks that tie the proofs to the bytes
(ADR-0004, overview §Tested).

1. Encoding order-preservation: the kernel proves the LWW/OR-Set order over
   the decoded `(hlc, replica, nonce)` integer triple and *delegates to the
   shell* that the canonical wire strings compare bytewise in the same
   order — the linchpin between the proved order and the on-disk bytes.
   Checked over every pair of seeded triples (fixed widths mean the `.`
   separators never decide a comparison).

2. Compiled-kernel-vs-spec property cross-check: the theorems are proved
   over `Tl/Kernel`'s *source*; this re-checks their statements against the
   COMPILED functions on seeded random op multisets — a regression net over
   the executable (does compilation preserve the theorems?), never a
   substitute for the proofs (ADR-0004): order/duplicate-insensitivity of
   the fold, join commutativity/idempotence observed through a state
   fingerprint, the ready queue's soundness and proved sortedness, the
   `unblocks` = ready-diff identity, and rollup totality on random cyclic
   graphs.
-/
import Tl.Format.Codec
import Tl.Kernel.Apply
import Tl.Kernel.Ready
import Tl.Kernel.Rollup
import Tl.Kernel.Cycles
import Tl.Kernel.RollupFast
import Tl.Kernel.ReadyFast
import Tests.Harness

namespace Tl.Tests

open Tl.Format
open Tl.Kernel
open Tl.Crdt

/-! ## 1. Encoding order-preservation -/

private def sampleStamps (seed n : Nat) : List Stamp :=
  sample seed n (fun s =>
    let (s1, h) := nextNat s (2 ^ 64)
    let (s2, r) := nextNat s1 (2 ^ 64)
    let (s3, x) := nextNat s2 (2 ^ 128)
    ((⟨h, r, x⟩ : Stamp), s3))

/-- Wire order = decoded order, over all pairs of seeded stamps (plus the
    crafted near-ties that exercise each tie-break level). -/
def orderPreservationTests : List Outcome :=
  let crafted : List Stamp :=
    [⟨5, 5, 5⟩, ⟨5, 5, 6⟩, ⟨5, 6, 5⟩, ⟨6, 5, 5⟩,
     ⟨5, 5, 2 ^ 128 - 1⟩, ⟨5, 2 ^ 64 - 1, 0⟩, ⟨2 ^ 64 - 1, 0, 0⟩, ⟨0, 0, 0⟩]
  let stamps := crafted ++ sampleStamps 0xbeef 60
  let agree (a b : Stamp) : Bool :=
    let sa := tagOfStamp a
    let sb := tagOfStamp b
    (compare sa sb == .lt) == decide (TotalOrd.lt a b)
      && (sa == sb) == decide (a = b)
  [check "wire-string order = decoded Stamp order on all pairs"
    (stamps.all (fun a => stamps.all (fun b => agree a b)))]

/-! ## 2. Compiled-kernel-vs-spec properties -/

private def idPool : List IssueId :=
  ["a000000000000000", "b000000000000000", "c000000000000000", "d000000000000000",
   "e000000000000000", "f000000000000000", "g000000000000000", "h000000000000000"]

/-- A seeded random op (over a small id pool, so edges/cycles collide often). -/
private def genOp (s : Nat) : Op × Nat :=
  let (s1, kind) := nextNat s 7
  let (s2, i) := nextNat s1 idPool.length
  let (s3, j) := nextNat s2 idPool.length
  let (s4, h) := nextNat s3 1000
  let id := idPool.getD i ""
  let other := idPool.getD j ""
  let st : Stamp := ⟨h, s4 % 5, s4 % 97⟩
  let op := match kind with
    | 0 => Op.create id st {}
    | 1 => Op.setFields id st { status := some (if h % 2 == 0 then .Done else .InProgress) }
    | 2 => Op.edgeAdd (id, other, .Blocks) st
    | 3 => Op.edgeAdd (id, other, .Parent) st
    | 4 => Op.edgeRemove (id, other, .Blocks) (FinSet.singleton st)
    | 5 => Op.labelAdd id "tag" st
    | _ => Op.metaSet id st "k" (some "v")
  (op, s4)

private def genOps (seed n : Nat) : List Op := sample seed n genOp

/-- An observational fingerprint: equal fingerprints ⇔ equal materialized
    behavior on every projection a command reads. -/
private def fingerprint (s : State) : String :=
  let issues := s.presentIssues.map (fun i =>
    let d := s.issueData i
    s!"{i}|{statusWire d.statusOf}|{d.priorityOf.val}|{d.labels.presentElements}|" ++
    s!"{statusWire (s.effectiveStatus i)}")
  let edges := s.presentEdges.map (fun (f, t, k) => s!"{f}->{t}:{edgeKindWire k}")
  String.intercalate ";" issues ++ "#" ++ String.intercalate ";" edges

private def seeds : List Nat := (List.range 25).map (0xc0ffee + 7919 * ·)

def kernelSpecTests : List Outcome :=
  let rows := seeds.map (fun seed =>
    let ops := genOps seed 40
    let s := fold ops
    let now := 500
    let rdy := s.ready now
    -- order-insensitivity + idempotent re-delivery (thm 2/8, compiled)
    let orderOk := fingerprint (fold ops.reverse) == fingerprint s
    let dupOk := fingerprint (fold (ops ++ ops)) == fingerprint s
    -- join laws observed (thm 1, compiled)
    let half := fold (ops.take 20)
    let joinIdem := fingerprint (State.merge s s) == fingerprint s
    let joinComm := fingerprint (State.merge s half) == fingerprint (State.merge half s)
    -- ready soundness (thm 4, compiled): ready ⊆ present, open, non-epic,
    -- every blocker discharged
    let readySound := rdy.all (fun i =>
      s.presentIssues.contains i
      && (s.issueData i).statusOf == .Open
      && !s.isEpic i
      && (s.blockersOf i).all (s.blockerDischarged ·))
    -- the queue is sorted by the proved ranking order (Ranking, compiled)
    let rec sortedBy : List IssueId → Bool
      | a :: b :: rest => s.readyLe a b && sortedBy (b :: rest)
      | _ => true
    let readySorted := sortedBy rdy
    -- unblocks is exactly the ready-diff (thm 10, compiled)
    let unblocksOk := s.presentIssues.all (fun i =>
      s.unblocks now i ==
        ((s.withClosed i).ready now).filter (fun x => !(rdy.contains x)))
    -- rollup totality on whatever cyclic/dangling graph emerged (thm on
    -- effStatus: evaluating it must terminate and return a valid enum)
    let rollupTotal := s.presentIssues.all (fun i =>
      match s.effectiveStatus i with
      | .Open | .InProgress | .Done | .Cancelled => true)
    -- the COMPILED fast rollup agrees with the compiled spec (the proved
    -- refinement bridge, effStatusWith_eq/isReadyWith_eq, re-checked over
    -- the executable on cyclic/diamond graphs the generator produces)
    let rollupMap := s.effStatusAll
    let fastAgrees := s.presentIssues.all (fun i =>
      State.effStatusWith rollupMap s i == s.effectiveStatus i
      && State.isReadyWith rollupMap s now i == s.isReady now i)
    -- the COMPILED fast queue/echo/why agree with the compiled spec (the
    -- ReadyFast refinement bridge re-checked over the executable)
    let readyFastAgrees := State.readyFast rollupMap s now == s.ready now
    let echoFastAgrees := s.presentIssues.all (fun i =>
      State.unblocksFast s now i == s.unblocks now i
      && State.whyFast rollupMap s i == s.why i)
    (seed, orderOk && dupOk && joinIdem && joinComm && readySound && readySorted
      && unblocksOk && rollupTotal && fastAgrees && readyFastAgrees && echoFastAgrees))
  rows.map (fun (seed, ok) =>
    check s!"compiled kernel meets its spec on seed {seed}" ok)

def crossTests : List Outcome := orderPreservationTests ++ kernelSpecTests

end Tl.Tests
