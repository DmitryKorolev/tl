/-
`Tests.SyncTests` — the sync shared core (ADR-0001 §2/§5): the per-segment
line-union (pure) and `refs/tl/log` read/write via git plumbing (against a
real temporary git repo), plus the transport legs built on them — the local
worktree leg and the remote fetch/union/push leg (against a bare remote).
-/
import Tl.Sync.Merge
import Tl.Sync.Ref
import Tl.Sync.Local
import Tl.Sync.Remote
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
      (u.length == 1 && ((u.head?.map segStr) == some "c\n")) ""),
   -- the sort+merge-join orders the result ascending by replica id regardless
   -- of input order (the eraseDups+find? shape it replaces did the same)
   (let u := unionSegments [seg "r3" "z\n", seg "r1" "a\n"] [seg "r2" "m\n"]
    check "unionSegments output is ascending by replica id"
      (u.map (·.replicaId) == ["r1", "r2", "r3"])
      (String.intercalate "," (u.map (·.replicaId)))),
   -- segsEquiv: per-replica content equality, order-independent, with an
   -- absent id equal to a present-but-empty one (the segBytesOf empty default)
   check "segsEquiv: identical sets (any order) are equal"
     (segsEquiv [seg "r1" "a\n", seg "r2" "b\n"] [seg "r2" "b\n", seg "r1" "a\n"]) "",
   check "segsEquiv: differing bytes are unequal"
     (!segsEquiv [seg "r1" "a\n"] [seg "r1" "b\n"]) "",
   check "segsEquiv: a present-but-empty segment equals an absent one"
     (segsEquiv [seg "r1" "a\n", seg "r2" ""] [seg "r1" "a\n"]) "",
   check "segsEquiv: an extra non-empty segment is unequal"
     (!segsEquiv [seg "r1" "a\n", seg "r2" "b\n"] [seg "r1" "a\n"]) "",
   -- byte-order discrete rows: a line that is a strict prefix of another
   -- sorts first; empty inputs union to empty
   checkEq "a prefix line sorts before its extension"
     (String.fromUTF8! (unionLines "ab\n".toUTF8 "a\n".toUTF8)) "a\nab\n",
   checkEq "the empty union is empty"
     (String.fromUTF8! (unionLines ByteArray.empty ByteArray.empty)) ""]

/-- The canonicalized union bytes must not move (a re-sync builds no churn
    commit) — pinned against a list-level reference of the original shape on
    seeded inputs with heavy duplication and shared prefixes (the cases that
    distinguish a wrong byte comparator or a non-adjacent dedup). -/
def syncMergeCanonicalProp : List Outcome :=
  let refLexLe : List UInt8 → List UInt8 → Bool := fun a b => Id.run do
    let rec go : List UInt8 → List UInt8 → Bool
      | [], _ => true
      | _ :: _, [] => false
      | x :: xs, y :: ys => if x < y then true else if y < x then false else go xs ys
    return go a b
  let refUnion (a b : ByteArray) : ByteArray :=
    let lines := completeLines a ++ completeLines b
    let sorted := lines.mergeSort (fun x y => refLexLe x.toList y.toList)
    sorted.eraseDups.foldl (fun acc l => acc ++ l ++ "\n".toUTF8) ByteArray.empty
  (List.range 12).map (fun k =>
    let seed := 0xd00d + 4099 * k
    -- lines drawn from a tiny alphabet with shared prefixes and many repeats
    let mkLine (s' : Nat) : String × Nat :=
      let (s1, len) := nextNat s' 4
      let (s2, c1) := nextNat s1 3
      let (s3, c2) := nextNat s2 3
      let body := String.ofList (List.replicate (len + 1) (Char.ofNat (97 + c1))) ++
        String.ofList (List.replicate 1 (Char.ofNat (97 + c2)))
      (body, s3)
    let (linesA, sA) := (List.range 9).foldl (fun (acc, st) _ =>
      let (l, st') := mkLine st
      (acc ++ [l], st')) (([] : List String), seed)
    let (linesB, _) := (List.range 9).foldl (fun (acc, st) _ =>
      let (l, st') := mkLine st
      (acc ++ [l], st')) (([] : List String), sA)
    let bytesOf (ls : List String) : ByteArray :=
      (ls.foldl (fun a l => a ++ l ++ "\n") "").toUTF8
    let a := bytesOf linesA
    let b := bytesOf linesB
    check s!"canonical union bytes unchanged (seed {k})"
      ((unionLines a b).toList == (refUnion a b).toList))

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
  -- a non-UTF-8 segment round-trips byte-for-byte (the union is a byte-level
  -- line set, ADR-0001 §5 — sync transports raw bytes; a String round-trip
  -- through git stdin/stdout would panic or mangle these)
  let raw : ByteArray := ⟨#[0x7b, 0xff, 0xfe, 0x0a]⟩  -- '{', 0xFF, 0xFE, LF
  let tipNow ← runTl (refTip d)
  o := o ++ [← do match tipNow with
    | .ok t =>
      match ← runTl (do let _ ← writeRef d [⟨"0123456789abf", raw⟩] t; readRef d) with
      | .ok segs => pure (check "a non-UTF-8 segment round-trips byte-for-byte through the ref"
          (match segs.find? (·.replicaId == "0123456789abf") with
           | some s => s.bytes.toList == raw.toList
           | none => false) "")
      | .error e => pure { name := "non-UTF-8 round-trip", passed := false, msg := e.message }
    | .error e => pure { name := "non-UTF-8 round-trip (tip)", passed := false, msg := e.message }]
  -- outside any repo: inGitRepo is false (the no-upstream case the caller maps)
  let bare ← IO.FS.createTempDir
  o := o ++ [check "inGitRepo false outside a repo"
    (!(← inGitRepo { base := bare.toString, tlRel := ".tl" }))]
  return o

/-- Read a file's bytes, `none` if absent. -/
private def readBytes (p : System.FilePath) : IO (Option ByteArray) := do
  try pure (some (← IO.FS.readBinFile p)) catch _ => pure none

/-- The local-first leg (ADR-0016 §1): publish own + absorb siblings through
    the shared `refs/tl/log`, modelled with two state dirs over one repo. -/
def syncLocalTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- (A) outside any git repo the local leg is a no-op (no shared ref)
  let nonRepo ← IO.FS.createTempDir
  o := o ++ [match ← runTl (syncLocal { base := nonRepo.toString, tlRel := ".tl" } none) with
    | .ok r => check "syncLocal is a no-op (ran=false) outside a git repo" (!r.ran && r.tip == none)
    | .error e => { name := "syncLocal no-op outside repo", passed := false, msg := e.message }]
  -- a repo whose refs/tl/log two state dirs share (the two-worktree model)
  let d ← gitRepo
  let ridA := (Tl.Clock.Replica.ofNat 1).id
  let ridB := (Tl.Clock.Replica.ofNat 2).id
  let logDir := System.FilePath.mk d.base / ".tl" / "log"
  IO.FS.createDirAll logDir
  IO.FS.createDirAll (System.FilePath.mk d.base / ".tl" / "local")  -- for the ref-mark
  IO.FS.writeBinFile (logDir / s!"{ridA}.jsonl") "{\"a\":1}\n".toUTF8
  -- (B) first sync publishes A's own segment and creates the ref
  o := o ++ [match ← runTl (syncLocal d (some ridA)) with
    | .ok r => check "first syncLocal publishes own + creates the ref"
        (r.ran && r.published && r.absorbed.isEmpty && r.tip.isSome) (toString (repr r))
    | .error e => { name := "first syncLocal publishes", passed := false, msg := e.message }]
  -- sync records the read-mark, so the very next read takes the fast path
  o := o ++ [match ← runTl (loadRefMark d), ← runTl (refTip d) with
    | .ok m, .ok t => check "syncLocal records the ref-mark at the reconciled tip" (m == t && m.isSome) s!"mark={m} tip={t}"
    | _, _ => { name := "syncLocal records the ref-mark", passed := false, msg := "unexpected" }]
  o := o ++ [match ← runTl (readRef d) with
    | .ok segs => check "the ref holds A's segment after publish"
        (segs.any (fun s => s.replicaId == ridA && segStr s == "{\"a\":1}\n")) ""
    | .error e => { name := "ref holds A's segment", passed := false, msg := e.message }]
  -- (C) a second sync with nothing new does not republish (tip unchanged)
  let tip1 ← runTl (refTip d)
  o := o ++ [match ← runTl (syncLocal d (some ridA)), tip1 with
    | .ok r, .ok t => check "a second syncLocal with nothing new does not republish"
        (r.ran && !r.published && r.tip == t) (toString (repr r))
    | _, _ => { name := "second syncLocal no-op", passed := false, msg := "unexpected error" }]
  -- (D) a sibling B publishes into the shared ref; A's next sync absorbs it
  let tip2 ← runTl (refTip d)
  let refNow ← runTl (readRef d)
  o := o ++ [← do match refNow, tip2 with
    | .ok rs, .ok t =>
      match ← runTl (writeRef d (rs ++ [seg ridB "{\"b\":2}\n"]) t) with
      | .ok _ => pure { name := "a sibling publishes B into the ref", passed := true }
      | .error e => pure { name := "sibling publishes B", passed := false, msg := e.message }
    | _, _ => pure { name := "sibling publishes B", passed := false, msg := "setup error" }]
  o := o ++ [match ← runTl (syncLocal d (some ridA)) with
    | .ok r => check "syncLocal absorbs only the sibling segment, not its own"
        (r.ran && r.absorbed == [ridB]) (toString (repr r))
    | .error e => { name := "syncLocal absorbs sibling", passed := false, msg := e.message }]
  o := o ++ [match ← readBytes (logDir / s!"{ridB}.jsonl") with
    | some bytes => check "the sibling segment is materialized into .tl/log/"
        (String.fromUTF8! bytes == "{\"b\":2}\n") (String.fromUTF8! bytes)
    | none => { name := "sibling materialized", passed := false, msg := "no file" }]
  -- A's own segment on disk is never overwritten from the ref
  o := o ++ [match ← readBytes (logDir / s!"{ridA}.jsonl") with
    | some bytes => check "A's own segment on disk is never overwritten by sync"
        (String.fromUTF8! bytes == "{\"a\":1}\n") (String.fromUTF8! bytes)
    | none => { name := "own segment untouched", passed := false, msg := "no file" }]
  return o

/-- Read-time refresh (ADR-0016 §3): the O(1) trigger, the materialize-on-move,
    the unchanged-skip, and the best-effort degrade on a read-only FS. -/
def syncRefreshTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- (A) no ref (here, not even a repo) → a no-op refresh that never fails
  let nonRepo ← IO.FS.createTempDir
  o := o ++ [match ← runTl (refreshFromRef { base := nonRepo.toString, tlRel := ".tl" } none) with
    | .ok r => check "refreshFromRef is a no-op when there is no ref"
        (!r.refreshed && r.tip == none && r.degraded == none) (toString (repr r))
    | .error e => { name := "refresh no-op (no ref)", passed := false, msg := e.message }]
  -- a repo where a sibling has already published a segment into the ref;
  -- .tl/local must exist (init guarantees it before any read — validate)
  let d ← gitRepo
  IO.FS.createDirAll (System.FilePath.mk d.base / ".tl" / "local")
  let logDir := System.FilePath.mk d.base / ".tl" / "log"
  let ridB := (Tl.Clock.Replica.ofNat 7).id
  let ridC := (Tl.Clock.Replica.ofNat 9).id
  let tipB ← runTl (do let t ← writeRef d [seg ridB "{\"b\":1}\n"] none; pure t)
  -- (B) the ref moved (no mark yet) → materialize the sibling + write the mark
  o := o ++ [match ← runTl (refreshFromRef d none) with
    | .ok r => check "refreshFromRef materializes a sibling when the ref moved"
        (r.refreshed && r.absorbed == [ridB] && r.degraded == none) (toString (repr r))
    | .error e => { name := "refresh materializes sibling", passed := false, msg := e.message }]
  o := o ++ [match ← readBytes (logDir / s!"{ridB}.jsonl") with
    | some b => check "the refreshed sibling segment is on disk" (String.fromUTF8! b == "{\"b\":1}\n") ""
    | none => { name := "refreshed sibling on disk", passed := false, msg := "no file" }]
  o := o ++ [match ← runTl (loadRefMark d), tipB with
    | .ok m, .ok t => check "the ref-mark records the materialized tip" (m == some t) s!"mark={m} tip={t}"
    | _, _ => { name := "ref-mark recorded", passed := false, msg := "unexpected" }]
  -- (C) mark == tip → a second refresh skips (no materialize)
  o := o ++ [match ← runTl (refreshFromRef d none) with
    | .ok r => check "refreshFromRef skips when the ref-mark already matches the tip"
        (!r.refreshed && r.absorbed.isEmpty) (toString (repr r))
    | .error e => { name := "refresh skips unchanged", passed := false, msg := e.message }]
  -- (D) the ref moves again, but the log dir is read-only → degrade, never throw.
  -- Root bypasses directory permissions, so under root we can only assert the
  -- invariant that always holds (refresh returns, never throws); a normal user
  -- additionally exercises the degrade branch.
  let uid ← (IO.Process.output { cmd := "id", args := #["-u"] } : IO _)
  let isRoot := uid.stdout.trimAscii.toString == "0"
  let _ ← runTl (do let _ ← writeRef d [seg ridB "{\"b\":1}\n", seg ridC "{\"c\":1}\n"] (← refTip d); pure ())
  let _ ← (IO.Process.output { cmd := "chmod", args := #["0500", logDir.toString] } : IO _)
  o := o ++ [match ← runTl (refreshFromRef d none) with
    | .ok r => check "refreshFromRef never throws when the log dir is read-only (degrades for non-root)"
        (if isRoot then true else (!r.refreshed && r.degraded.isSome)) (toString (repr r))
    | .error e => { name := "refresh degrades on read-only FS", passed := false, msg := s!"threw: {e.message}" }]
  let _ ← (IO.Process.output { cmd := "chmod", args := #["0700", logDir.toString] } : IO _)
  return o

/-- A working repo with `origin` pointing at a fresh bare remote. -/
private def repoWithRemote : IO (Dirs × String) := do
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["init", "--bare", "-q", bare.toString] }
  let work ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", work.toString, "init", "-q"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", work.toString, "remote", "add", "origin", bare.toString] }
  return ({ base := work.toString, tlRel := ".tl" }, bare.toString)

private def replicaIds (segs : List SegmentData) : List String :=
  (segs.map (·.replicaId)).mergeSort (· ≤ ·)

/-- The remote leg (ADR-0001 §5): resolution, fetch → union → push, no-upstream,
    and non-fast-forward rejection detection + recovery, against a bare remote. -/
def syncRemoteTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let ridA := (Tl.Clock.Replica.ofNat 1).id
  let ridC := (Tl.Clock.Replica.ofNat 3).id
  -- (A) no remote configured → resolveRemote none, syncRemote a reported no-op
  let dn ← gitRepo
  o := o ++ [match ← runTl (resolveRemote dn) with
    | .ok none => { name := "resolveRemote is none with no remote (no-upstream)", passed := true }
    | _ => { name := "resolveRemote none", passed := false, msg := "expected none" }]
  o := o ++ [match ← runTl (syncRemote dn) with
    | .ok r => check "syncRemote is a reported no-op with no remote" (!r.ran && !r.pushed && !r.pulled) (toString (repr r))
    | .error e => { name := "syncRemote no-upstream", passed := false, msg := e.message }]
  -- (B) push to a fresh remote: a local ref's segment lands on the bare
  let (d, bare) ← repoWithRemote
  let _ ← runTl (writeRef d [seg ridA "{\"a\":1}\n"] none)
  o := o ++ [match ← runTl (syncRemote d) with
    | .ok r => check "syncRemote pushes the local ref to a fresh remote"
        (r.ran && r.remote == "origin" && r.pushed) (toString (repr r))
    | .error e => { name := "syncRemote pushes", passed := false, msg := e.message }]
  let dBare : Dirs := { base := bare, tlRel := ".tl" }
  o := o ++ [match ← runTl (readRefAt dBare "refs/tl/log") with
    | .ok segs => check "the bare remote now carries the pushed segment"
        (segs.any (fun s => s.replicaId == ridA)) (String.intercalate "," (replicaIds segs))
    | .error e => { name := "remote carries segment", passed := false, msg := e.message }]
  -- (C) a second clone pulls it: empty local → syncRemote absorbs the remote
  let work2 ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", work2.toString, "init", "-q"] } : IO _)
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", work2.toString, "remote", "add", "origin", bare] } : IO _)
  let d2 : Dirs := { base := work2.toString, tlRel := ".tl" }
  o := o ++ [match ← runTl (syncRemote d2) with
    | .ok r => check "a second clone pulls the remote's content"
        (r.ran && r.pulled && !r.pushed) (toString (repr r))
    | .error e => { name := "second clone pulls", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (readRef d2) with
    | .ok segs => check "the pulled segment is in the second clone's local ref"
        (segs.any (fun s => s.replicaId == ridA)) (String.intercalate "," (replicaIds segs))
    | .error e => { name := "pulled into local ref", passed := false, msg := e.message }]
  -- (D) re-sync with nothing new is a no-op (converged)
  o := o ++ [match ← runTl (syncRemote d2) with
    | .ok r => check "a converged re-sync neither pushes nor pulls"
        (r.ran && !r.pushed && !r.pulled) (toString (repr r))
    | .error e => { name := "converged re-sync no-op", passed := false, msg := e.message }]
  -- (E) push-rejection detection: a divergent local ref (not descending from the
  -- remote tip) is rejected by a raw push; the full leg then recovers by
  -- fetching + unioning before re-pushing
  let work3 ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", work3.toString, "init", "-q"] } : IO _)
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", work3.toString, "remote", "add", "origin", bare] } : IO _)
  let d3 : Dirs := { base := work3.toString, tlRel := ".tl" }
  let tip3 ← runTl (writeRef d3 [seg ridC "{\"c\":3}\n"] none)  -- a local ref not descending from the remote
  let pushed3 ← match tip3 with
    | .ok t => runTl (pushRefLog d3 "origin" t)
    | .error e => pure (.error e)
  o := o ++ [match pushed3 with
    | .ok false => { name := "pushRefLog detects a non-fast-forward rejection", passed := true }
    | .ok true => { name := "pushRefLog rejection", passed := false, msg := "unexpectedly accepted a non-ff push" }
    | .error e => { name := "pushRefLog rejection", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (syncRemote d3) with
    | .ok r => check "the remote leg recovers from divergence (fetch+union, then push)"
        (r.ran && r.pushed && r.pulled) (toString (repr r))
    | .error e => { name := "remote leg recovers", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (readRefAt dBare "refs/tl/log") with
    | .ok segs => check "after recovery the remote carries BOTH replicas' segments"
        (segs.any (·.replicaId == ridA) && segs.any (·.replicaId == ridC))
        (String.intercalate "," (replicaIds segs))
    | .error e => { name := "remote has both after recovery", passed := false, msg := e.message }]
  -- (F) a remote pre-receive hook that declines every push is a POLICY decline,
  -- not a non-fast-forward race: the leg must NOT retry-then-misreport it as
  -- push-rejected ("remote moved, retry") — it surfaces the real reason instead
  let (df, baref) ← repoWithRemote
  IO.FS.writeFile (System.FilePath.mk baref / "hooks" / "pre-receive") "#!/bin/sh\nexit 1\n"
  let _ ← (IO.Process.output { cmd := "chmod", args := #["+x", (System.FilePath.mk baref / "hooks" / "pre-receive").toString] } : IO _)
  let _ ← runTl (writeRef df [seg ridA "{\"a\":1}\n"] none)
  o := o ++ [match ← runTl (syncRemote df) with
    | .error e => check "a hook/policy decline surfaces the real error, not a misleading push-rejected"
        (e.code != .pushRejected && (e.message.splitOn "declined").length > 1)
        s!"code={e.code.wire} msg={e.message}"
    | .ok r => { name := "hook decline → real error", passed := false, msg := s!"unexpectedly ok: {repr r}" }]
  -- (G) a fresh remote + an empty local repo (no ops): nothing to share, so the
  -- leg pushes NO empty-log churn commit
  let (de, baree) ← repoWithRemote
  o := o ++ [match ← runTl (syncRemote de) with
    | .ok r => check "an empty repo against a fresh remote pushes nothing (no churn)"
        (r.ran && !r.pushed && !r.pulled) (toString (repr r))
    | .error e => { name := "empty repo no churn", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (refTip { base := baree, tlRel := ".tl" }) with
    | .ok none => { name := "the fresh remote still has no refs/tl/log", passed := true }
    | .ok (some t) => { name := "fresh remote unchanged", passed := false, msg := s!"unexpected ref {t}" }
    | .error e => { name := "fresh remote unchanged", passed := false, msg := e.message }]
  return o

def syncTests : IO (List Outcome) := do
  return syncMergeTests ++ syncMergeCanonicalProp ++ (← syncRefTests) ++ (← syncLocalTests)
    ++ (← syncRefreshTests) ++ (← syncRemoteTests)

end Tl.Tests
