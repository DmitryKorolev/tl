/-
`Tests.SyncTests` — the sync shared core (ADR-0001 §2/§5): the per-segment
line-union (pure) and `refs/tl/log` read/write via git plumbing (against a
real temporary git repo). The transport legs (local worktree, remote
fetch/push) build on these and are tested when they land.
-/
import Tl.Sync.Merge
import Tl.Sync.Ref
import Tests.Harness

namespace Tl.Tests

open Tl.Store
open Tl.Sync

private def seg (rid : String) (s : String) : SegmentData := { replicaId := rid, bytes := s.toUTF8 }
private def segStr (s : SegmentData) : String := String.fromUTF8! s.bytes

def syncMergeTests : List Outcome :=
  [checkEq "unionLines is the sorted, deduped line set"
     (String.fromUTF8! (unionLines "b\na\n".toUTF8 "b\nc\n".toUTF8)) "a\nb\nc\n",
   checkEq "unionLines drops a torn (newline-less) trailing fragment"
     (String.fromUTF8! (unionLines "a\nb".toUTF8 "c\n".toUTF8)) "a\nc\n",
   checkEq "unionLines of identical inputs is idempotent"
     (String.fromUTF8! (unionLines "x\ny\n".toUTF8 "x\ny\n".toUTF8)) "x\ny\n",
   -- unionSegments: per-replica union; the other replica taken whole
   (let u := unionSegments [seg "r1" "a\n"] [seg "r1" "b\n", seg "r2" "c\n"]
    check "unionSegments unions same-id segments and takes others whole"
      (u.length == 2
        && ((u.find? (·.replicaId == "r1")).map segStr) == some "a\nb\n"
        && ((u.find? (·.replicaId == "r2")).map segStr) == some "c\n")
      (String.intercalate "|" (u.map (fun s => s!"{s.replicaId}={segStr s}")))),
   (let u := unionSegments [] [seg "r2" "c\n"]
    check "unionSegments: a replica on only one side is taken whole"
      (u.length == 1 && ((u.head?.map segStr) == some "c\n")) "")]

/-- A throwaway git repo with a `.tl`-bearing `Dirs` pointing at it. -/
private def gitRepo : IO Dirs := do
  let root ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] }
  return { base := root.toString, tlRel := ".tl" }

private def runTl (act : TlM α) : IO (Except Tl.Error α) := act.run

def syncRefTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let d ← gitRepo
  -- inside a repo; an empty repo has no ref yet
  o := o ++ [check "inGitRepo true inside a repo" (← inGitRepo d)]
  o := o ++ [match ← runTl (refTip d) with
    | .ok none => { name := "refTip is none before any write", passed := true }
    | .ok (some t) => { name := "refTip none before write", passed := false, msg := s!"got {t}" }
    | .error e => { name := "refTip none before write", passed := false, msg := e.message }]
  -- write two segments, read them back byte-for-byte
  let segs := [seg "0123456789abc" "{\"a\":1}\n{\"b\":2}\n", seg "0123456789abd" "{\"c\":3}\n"]
  let tip ← runTl (writeRef d segs none)
  o := o ++ [match tip with
    | .ok _ => { name := "writeRef creates the ref", passed := true }
    | .error e => { name := "writeRef creates the ref", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (readRef d) with
    | .ok back =>
      let bySorted := back.mergeSort (fun a b => decide (a.replicaId ≤ b.replicaId))
      check "readRef round-trips the written segments"
        (bySorted.length == 2
          && (bySorted.map (fun s => (s.replicaId, segStr s)))
             == [("0123456789abc", "{\"a\":1}\n{\"b\":2}\n"), ("0123456789abd", "{\"c\":3}\n")])
        (String.intercalate "|" (bySorted.map (fun s => s!"{s.replicaId}={segStr s}")))
    | .error e => { name := "readRef round-trips", passed := false, msg := e.message }]
  -- refTip is now set
  o := o ++ [match ← runTl (refTip d) with
    | .ok (some _) => { name := "refTip is set after write", passed := true }
    | _ => { name := "refTip set after write", passed := false, msg := "expected some" }]
  -- compare-and-set: writing against a stale expected tip is rejected
  o := o ++ [match ← runTl (writeRef d [seg "0123456789abc" "{\"z\":9}\n"] (some "0000000000000000000000000000000000000000")) with
    | .error _ => { name := "writeRef CAS rejects a stale expected tip", passed := true }
    | .ok _ => { name := "writeRef CAS rejects stale tip", passed := false, msg := "unexpectedly succeeded" }]
  -- a second writeRef against the real tip chains a parent (history kept)
  let realTip ← runTl (refTip d)
  let chainCount ← (do
    match realTip with
    | .ok tipv =>
      match ← runTl (writeRef d (segs ++ [seg "0123456789abe" "{\"d\":4}\n"]) tipv) with
      | .ok _ =>
        let out ← (IO.Process.output
          { cmd := "git", args := #["-C", d.base, "rev-list", "--count", "refs/tl/log"] } : IO _)
        pure out.stdout.trimAscii.toString
      | .error e => pure s!"writeRef error: {e.message}"
    | .error e => pure s!"refTip error: {e.message}")
  o := o ++ [check "a second sync chains a parent commit (history kept)"
    (chainCount == "2") chainCount]
  -- outside any repo: inGitRepo is false (the no-upstream case the caller maps)
  let bare ← IO.FS.createTempDir
  o := o ++ [check "inGitRepo false outside a repo"
    (!(← inGitRepo { base := bare.toString, tlRel := ".tl" }))]
  return o

def syncTests : IO (List Outcome) := do
  return syncMergeTests ++ (← syncRefTests)

end Tl.Tests
