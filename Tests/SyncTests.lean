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
import release.Process

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
  let tip ← runTl (writeRef d segs [] none)
  o := o ++ [match tip with
    | .ok _ => { name := "writeRef creates the ref", passed := true }
    | .error e => { name := "writeRef creates the ref", passed := false, msg := e.message }]
  let ident ← IO.Process.output
    { cmd := "git", args := #["-C", d.base, "show", "-s", "--format=%an <%ae>|%cn <%ce>",
      "refs/tl/log"] }
  o := o ++ [checkEq "ref commit uses the neutral author and committer"
    ident.stdout.trimAscii.toString "tl-dev <tl-dev>|tl-dev <tl-dev>"]
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
  o := o ++ [match ← runTl (writeRef d [seg "0123456789abc" "{\"z\":9}\n"] [] (some "0000000000000000000000000000000000000000")) with
    | .error _ => { name := "writeRef CAS rejects a stale expected tip", passed := true }
    | .ok _ => { name := "writeRef CAS rejects stale tip", passed := false, msg := "unexpectedly succeeded" }]
  -- a second writeRef against the real tip chains a parent (history kept)
  let realTip ← runTl (refTip d)
  let chainCount ← (do
    match realTip with
    | .ok tipv =>
      match ← runTl (writeRef d (segs ++ [seg "0123456789abe" "{\"d\":4}\n"]) [] tipv) with
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
      match ← runTl (do let _ ← writeRef d [⟨"0123456789abf", raw⟩] [] t; readRef d) with
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
      match ← runTl (writeRef d (rs ++ [seg ridB "{\"b\":2}\n"]) [] t) with
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
  -- (E) a real write grows A's own segment: the publish-marker fast-out must not
  -- fire (the marker is keyed to the own segment's bytes), so the new op
  -- republishes — the no-lost-publish guarantee the fast-out must preserve
  IO.FS.writeBinFile (logDir / s!"{ridA}.jsonl") "{\"a\":1}\n{\"a\":3}\n".toUTF8
  o := o ++ [match ← runTl (syncLocal d (some ridA)) with
    | .ok r => check "a write growing the own segment republishes (no stale fast-out)"
        (r.ran && r.published) (toString (repr r))
    | .error e => { name := "grown own republishes", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (readRef d) with
    | .ok segs => check "the ref carries A's newly written op after the republish"
        (segs.any (fun s => s.replicaId == ridA && segStr s == "{\"a\":1}\n{\"a\":3}\n")) ""
    | .error e => { name := "ref has new op", passed := false, msg := e.message }]
  -- (F) after the publish the marker file is recorded; a third sync with nothing
  -- new fast-outs to the same no-op outcome (published := false, tip unchanged)
  o := o ++ [match ← readBytes (System.FilePath.mk d.base / ".tl" / "local" / "sync-pub") with
    | some bytes => check "the publish marker is recorded after a sync" (!bytes.isEmpty) ""
    | none => { name := "publish marker recorded", passed := false, msg := "no sync-pub file" }]
  let tipE ← runTl (refTip d)
  o := o ++ [match ← runTl (syncLocal d (some ridA)), tipE with
    | .ok r, .ok t => check "a converged third sync fast-outs (no republish, tip kept)"
        (r.ran && !r.published && r.absorbed.isEmpty && r.tip == t) (toString (repr r))
    | _, _ => { name := "third syncLocal fast-out", passed := false, msg := "unexpected error" }]
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
  let tipB ← runTl (do let t ← writeRef d [seg ridB "{\"b\":1}\n"] [] none; pure t)
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
  let _ ← runTl (do let _ ← writeRef d [seg ridB "{\"b\":1}\n", seg ridC "{\"c\":1}\n"] [] (← refTip d); pure ())
  let _ ← (IO.Process.output { cmd := "chmod", args := #["0500", logDir.toString] } : IO _)
  o := o ++ [match ← runTl (refreshFromRef d none) with
    | .ok r => check "refreshFromRef never throws when the log dir is read-only (degrades for non-root)"
        (if isRoot then true else (!r.refreshed && r.degraded.isSome)) (toString (repr r))
    | .error e => { name := "refresh degrades on read-only FS", passed := false, msg := s!"threw: {e.message}" }]
  let _ ← (IO.Process.output { cmd := "chmod", args := #["0700", logDir.toString] } : IO _)
  return o

/-- Set `protocol.file.allow=always` in a repo's *local* config so its `tl`
    sync over a local-path remote works regardless of the developer's global
    `protocol.file.allow` (a `never` there would otherwise fail every
    file-transport fixture — a hermeticity gap, not a tl bug: tl correctly
    respects the user's protocol policy in production). Local overrides global. -/
private def allowFileProto (dir : String) : IO Unit := do
  let _ ← IO.Process.output
    { cmd := "git", args := #["-C", dir, "config", "protocol.file.allow", "always"] }
  pure ()

/-- A working repo with `origin` pointing at a fresh bare remote. -/
private def repoWithRemote : IO (Dirs × String) := do
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["init", "--bare", "-q", bare.toString] }
  let work ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", work.toString, "init", "-q"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", work.toString, "remote", "add", "origin", bare.toString] }
  allowFileProto work.toString
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
  let noteN ← IO.mkRef ([] : List String)
  o := o ++ [match ← runTl (syncRemote dn (announce := fun rm => noteN.modify (· ++ [rm]))) with
    | .ok r => check "syncRemote is a reported no-op with no remote" (!r.ran && !r.pushed && !r.pulled) (toString (repr r))
    | .error e => { name := "syncRemote no-upstream", passed := false, msg := e.message }]
  o := o ++ [check "no progress notice fires when no remote resolves"
      ((← noteN.get).isEmpty) (String.intercalate "," (← noteN.get))]
  -- (A') option-injection guard: a `tl.remote` whose value starts with `-` (e.g.
  -- `--upload-pack=<cmd>`) resolves to none even though `origin` exists — it must
  -- never reach ls-remote/fetch/push as a positional that git parses as a flag
  let (dInj, _) ← repoWithRemote
  let cfgPath := System.FilePath.mk dInj.base / ".git" / "config"
  let existing ← IO.FS.readFile cfgPath
  IO.FS.writeFile cfgPath (existing ++ "[tl]\n\tremote = -upload-pack=evil\n")
  o := o ++ [match ← runTl (resolveRemote dInj) with
    | .ok none => { name := "resolveRemote rejects an option-injection remote name (leading '-')", passed := true }
    | .ok (some r) => { name := "resolveRemote rejects '-' remote", passed := false, msg := s!"resolved to {r}" }
    | .error e => { name := "resolveRemote rejects '-' remote", passed := false, msg := e.message }]
  -- (B) push to a fresh remote: a local ref's segment lands on the bare
  let (d, bare) ← repoWithRemote
  let _ ← runTl (writeRef d [seg ridA "{\"a\":1}\n"] [] none)
  let noteB ← IO.mkRef ([] : List String)
  o := o ++ [match ← runTl (syncRemote d (announce := fun rm => noteB.modify (· ++ [rm]))) with
    | .ok r => check "syncRemote pushes the local ref to a fresh remote"
        (r.ran && r.remote == "origin" && r.pushed) (toString (repr r))
    | .error e => { name := "syncRemote pushes", passed := false, msg := e.message }]
  o := o ++ [check "the progress notice fires once with the resolved remote before the network leg"
      ((← noteB.get) == ["origin"]) (String.intercalate "," (← noteB.get))]
  let dBare : Dirs := { base := bare, tlRel := ".tl" }
  o := o ++ [match ← runTl (readRefAt dBare "refs/tl/log") with
    | .ok segs => check "the bare remote now carries the pushed segment"
        (segs.any (fun s => s.replicaId == ridA)) (String.intercalate "," (replicaIds segs))
    | .error e => { name := "remote carries segment", passed := false, msg := e.message }]
  -- (C) a second clone pulls it: empty local → syncRemote absorbs the remote
  let work2 ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", work2.toString, "init", "-q"] } : IO _)
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", work2.toString, "remote", "add", "origin", bare] } : IO _)
  allowFileProto work2.toString
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
  allowFileProto work3.toString
  let d3 : Dirs := { base := work3.toString, tlRel := ".tl" }
  let tip3 ← runTl (writeRef d3 [seg ridC "{\"c\":3}\n"] [] none)  -- a local ref not descending from the remote
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
  -- (F) a remote pre-receive hook that declines every push is a policy decline,
  -- not a non-fast-forward race: the leg must not retry-then-misreport it as
  -- push-rejected ("remote moved, retry") — it surfaces the real reason instead
  let (df, baref) ← repoWithRemote
  IO.FS.writeFile (System.FilePath.mk baref / "hooks" / "pre-receive") "#!/bin/sh\nexit 1\n"
  let _ ← (IO.Process.output { cmd := "chmod", args := #["+x", (System.FilePath.mk baref / "hooks" / "pre-receive").toString] } : IO _)
  -- pin the receiving repo's hooks dir in its own (local) config: a developer's
  -- global `core.hooksPath` would otherwise point receive-pack elsewhere, the
  -- decline would never fire, and this row would silently test nothing
  let hooksDir := (System.FilePath.mk baref / "hooks").toString
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", baref, "config", "core.hooksPath", hooksDir] } : IO _)
  let _ ← runTl (writeRef df [seg ridA "{\"a\":1}\n"] [] none)
  o := o ++ [match ← runTl (syncRemote df) with
    | .error e => check "a hook/policy decline surfaces the real error, not a misleading push-rejected"
        (e.code != .pushRejected && (e.message.splitOn "declined").length > 1)
        s!"code={e.code.wire} msg={e.message}"
    | .ok r => { name := "hook decline → real error", passed := false, msg := s!"unexpectedly ok: {repr r}" }]
  -- (G) a fresh remote + an empty local repo (no ops): nothing to share, so the
  -- leg pushes no empty-log churn commit
  let (de, baree) ← repoWithRemote
  o := o ++ [match ← runTl (syncRemote de) with
    | .ok r => check "an empty repo against a fresh remote pushes nothing (no churn)"
        (r.ran && !r.pushed && !r.pulled) (toString (repr r))
    | .error e => { name := "empty repo no churn", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (refTip { base := baree, tlRel := ".tl" }) with
    | .ok none => { name := "the fresh remote still has no refs/tl/log", passed := true }
    | .ok (some t) => { name := "fresh remote unchanged", passed := false, msg := s!"unexpected ref {t}" }
    | .error e => { name := "fresh remote unchanged", passed := false, msg := e.message }]
  -- (H) the bounded retry is exhausted, surfacing the positive push-rejected throw
  -- (cases E and F assert only the negative). A push that signals non-fast-forward
  -- on every attempt (another clone winning the race each time) drives
  -- reconcileRemote through both attempts to the fuel-0 arm. The push is injected to
  -- return the race signal deterministically — the real fetch/union/CAS legs still
  -- run; a concurrent-writer race is avoided because the leg always builds a
  -- fast-forward merge, so a single genuine rejection recovers (case E) and only a
  -- never-converging race reaches here. The call counter pins the retry budget: the
  -- throw must follow exactly maxRemoteAttempts (2) push attempts, so a regression
  -- to a budget of 1 would fail this case.
  let (dh, _) ← repoWithRemote
  let _ ← runTl (writeRef dh [seg ridA "{\"a\":1}\n"] [] none)  -- local content worth pushing
  let pushCalls ← IO.mkRef 0
  let exhausted ← runTl (syncRemote dh
    (push := fun _ _ _ => do let _ ← (pushCalls.modify (· + 1) : IO Unit); pure false))
  let calls ← pushCalls.get
  o := o ++ [match exhausted with
    | .error e => check "an unrecoverable non-fast-forward race surfaces push-rejected once the retry budget is spent"
        (e.code == .pushRejected && e.code.wire == "push-rejected" && e.code.exitCode == 10
          && (e.message.splitOn "moved during the push").length > 1
          && (e.message.splitOn "run `tl sync` again").length > 1)
        s!"code={e.code.wire} exit={e.code.exitCode} msg={e.message}"
    | .ok r => { name := "push-rejected throw after retry exhaustion", passed := false, msg := s!"unexpectedly ok: {repr r}" }]
  o := o ++ [check "the throw follows the full retry budget (push attempted twice, = maxRemoteAttempts)"
      (calls == 2) s!"push called {calls} time(s), expected 2"]
  return o

/-- The git wall-clock timeout: `runBounded` kills a process that overruns
    (exit 124) and runs a fast one to completion; `0` disables the bound; and the
    bounds are overridable via `tl.gitTimeoutMs` / `tl.gitRemoteTimeoutMs` git
    config, falling back to the built-in defaults when unset. Exercised with
    `sleep`/`true` — no hung git needed. -/
def syncTimeoutTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let (c1, _, e1) ← runBounded { cmd := "sleep", args := #["5"] } .empty 200
  let (c2, _, _) ← runBounded { cmd := "true" } .empty 5000
  let (c3, _, _) ← runBounded { cmd := "sleep", args := #["1"] } .empty 0
  o := o ++
    [check "runBounded kills a process past its timeout (exit 124)" (c1 == 124) s!"c1={c1}",
     check "runBounded surfaces a timeout message" ((e1.splitOn "timed out").length > 1) e1,
     check "runBounded returns the real exit for a fast process" (c2 == 0) s!"c2={c2}",
     check "runBounded with 0 disables the bound (waits to completion)" (c3 == 0) s!"c3={c3}"]
  -- git config overrides the bounds; unset falls back to the defaults (5000/30000)
  let cfgRepo ← gitRepo
  let _ ← IO.Process.output { cmd := "git", args := #["-C", cfgRepo.base, "config", "tl.gitTimeoutMs", "7777"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", cfgRepo.base, "config", "tl.gitRemoteTimeoutMs", "88888"] }
  let (lo, re) ← readTimeoutsUncached cfgRepo
  let plainRepo ← gitRepo
  let (lo2, re2) ← readTimeoutsUncached plainRepo
  o := o ++
    [check "tl.gitTimeoutMs git-config overrides the local bound" (lo == 7777) s!"lo={lo}",
     check "tl.gitRemoteTimeoutMs git-config overrides the remote bound" (re == 88888) s!"re={re}",
     check "unset config falls back to the built-in defaults" (lo2 == 5000 && re2 == 30000) s!"lo2={lo2} re2={re2}"]
  return o

/-- The ADR-0012 subprocess environment scrub: the pinned variable set, the
    `none`-unsets shape, the scrub-first/caller-after composition order (a
    caller may deliberately re-set a scrubbed variable), and a control row
    demonstrating the rerouting behavior git exhibits when the scrub is
    absent (the vulnerability being closed). The inherited-environment
    behavior itself needs a process boundary, so those rows live with the
    spawned-binary tests (`cliGitEnvTests`). -/
def syncEnvScrubTests : IO (List Outcome) := do
  let pinned :=
    ["GIT_DIR", "GIT_WORK_TREE", "GIT_COMMON_DIR", "GIT_OBJECT_DIRECTORY",
     "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_INDEX_FILE", "GIT_NAMESPACE",
     "GIT_GRAFT_FILE", "GIT_SHALLOW_FILE", "GIT_REPLACE_REF_BASE",
     "GIT_CONFIG", "GIT_CONFIG_COUNT", "GIT_CONFIG_PARAMETERS",
     "GIT_CONFIG_SYSTEM", "GIT_CONFIG_GLOBAL", "XDG_CONFIG_HOME"]
  let mut o : List Outcome :=
    [checkEq "scrubbedGitVars pins the documented routing/config-injection set"
       scrubbedGitVars pinned,
     check "gitEnvScrub unsets every scrubbed variable"
       (gitEnvScrub.toList == scrubbedGitVars.map (fun v => (v, (none : Option String))))
       s!"gitEnvScrub={gitEnvScrub.toList.map (·.1)}"]
  -- entries apply left-to-right with the scrub prepended, so a caller can
  -- deliberately re-set even a *scrubbed* variable — the discriminating pin
  -- for the composition order (a scrub-last order would clobber this entry)
  let (c1, out1, _) ← runBounded
    { cmd := "sh", args := #["-c", "printf %s \"${GIT_DIR:-CLEAN}\""],
      env := #[("GIT_DIR", some "/deliberate")] } .empty 5000
  let echoed := (String.fromUTF8? out1).getD ""
  o := o ++ [check "caller env entries land after the scrub (left-to-right order)"
    (c1 == 0 && echoed == "/deliberate") s!"c1={c1} out={echoed}"]
  -- control: absent the scrub, GIT_DIR reroutes git away from the -C repo —
  -- the exact cross-repository hole the scrub closes; if git ever stops
  -- honoring GIT_DIR like this, the scrub (and its ADR text) can shrink
  let a ← gitRepo
  let b ← gitRepo
  let (c2, out2, _) ← runBounded
    { cmd := "sh",
      args := #["-c", s!"GIT_DIR=\"{b.base}/.git\" git -C \"{a.base}\" rev-parse --absolute-git-dir"] }
    .empty 5000
  let routed := (String.fromUTF8? out2).getD "" |>.trimAscii.toString
  let bReal ← IO.FS.realPath (b.base ++ "/.git")
  o := o ++ [check "control: an unscrubbed GIT_DIR reroutes git off the -C repository"
    (c2 == 0 && routed == bReal.toString) s!"routed={routed} expected={bReal}"]
  return o

/-- A ref-borne segment with a non-canonical name (crafted/junk tree entry) is
    excluded from the *segment* view by `readRefEntriesAt` (the `Replica.valid`
    filter), so junk never propagates through a union into a
    permanently-flagged on-disk file — but it is returned as a carried-unknown
    entry (ADR-0008 transport preserve-unknown), ref-only. -/
def syncRefNameValidationTests : IO (List Outcome) := do
  let d ← gitRepo
  let good := seg "0123456789abc" "{\"a\":1}\n"   -- a canonical 13-char replica id
  let junk := seg "tooshort" "{\"x\":9}\n"         -- not a valid replica id
  let _ ← runTl (writeRef d [good, junk] [] none)
  match ← runTl (readRefEntries d) with
  | .ok (back, foreign) =>
    return [check "the segment view excludes a non-canonical ref-borne segment name"
      (back.length == 1 && back.head?.map (·.replicaId) == some "0123456789abc")
      s!"got {back.map (·.replicaId)}",
     check "the non-canonical name is instead a carried-unknown entry"
      (foreign.map (·.name) == ["tooshort.jsonl"])
      s!"got {foreign.map (·.name)}"]
  | .error e => return [{ name := "readRef junk-name filter", passed := false, msg := e.message }]

/-- Blob-write helper: hash `content` into the repo's object store, returning
    the oid — the plumbing a test needs to craft a foreign tree entry. -/
private def hashBlob (d : Dirs) (content : String) : IO String := do
  let src := System.FilePath.mk d.base / "blob-src.tmp"
  IO.FS.writeFile src content
  let o ← IO.Process.output { cmd := "git", args := #["-C", d.base, "hash-object", "-w", src.toString] }
  IO.FS.removeFile src
  return o.stdout.trimAscii.toString

/-- The repo's empty tree object (written so `mktree` can reference it). -/
private def emptyTree (d : Dirs) : IO String := do
  let o ← IO.Process.output { cmd := "git", args := #["-C", d.base, "mktree"], stdin := .null }
  return o.stdout.trimAscii.toString

/-- The tree oid a ref commit points at (distinguishes churn commits from
    byte-identical content). -/
private def treeOf (d : Dirs) (ref : String) : IO String := do
  let o ← IO.Process.output { cmd := "git", args := #["-C", d.base, "rev-parse", s!"{ref}^\{tree}"] }
  return o.stdout.trimAscii.toString

/-- Transport preserve-unknown (ADR-0008): a `refs/tl/log` tree entry the
    binary does not recognize — a reserved future name like a compaction
    snapshot, a junk `.jsonl` name, a subtree — survives the local publish
    leg, the remote fetch/union/push legs, and push/CAS retries verbatim; it
    is never materialized into `.tl/log/`; same-name conflicts resolve
    deterministically and side-symmetrically; and equal content still builds
    an identical tree (no churn). -/
def syncForeignEntryTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let fe := fun (name raw : String) => ({ name, raw } : ForeignEntry)
  -- unionForeign (pure): disjoint names, dedup, deterministic symmetric conflict pick
  let a := fe "alpha" "100644 blob aaaa\talpha"
  let b := fe "beta" "100644 blob bbbb\tbeta"
  let b' := fe "beta" "100644 blob cccc\tbeta"
  o := o ++
    [checkEq "unionForeign unions disjoint names, name-sorted"
      ((unionForeign [b] [a]).map (·.name)) ["alpha", "beta"],
     checkEq "unionForeign dedups an identical entry" (unionForeign [a, b] [b]) [a, b],
     checkEq "unionForeign picks the greater raw line on a same-name conflict"
      (unionForeign [b] [b']) [b'],
     checkEq "unionForeign conflict pick is side-symmetric (opposite merge orders converge)"
      (unionForeign [b'] [b]) (unionForeign [b] [b'])]
  -- a repo whose ref carries a foreign entry alongside a real segment
  let d ← gitRepo
  let ridA := (Tl.Clock.Replica.ofNat 1).id
  let snapOid ← hashBlob d "{\"snapshot\":true}\n"
  let snapRaw := s!"100644 blob {snapOid}\tsnapshot"
  let _ ← runTl (writeRef d [seg ridA "{\"a\":1}\n"] [fe "snapshot" snapRaw] none)
  o := o ++ [match ← runTl (readRefEntries d) with
    | .ok (segs, foreign) => check "readRefEntries returns the foreign entry verbatim beside the segment"
        (segs.map (·.replicaId) == [ridA] && foreign == [fe "snapshot" snapRaw])
        s!"segs={segs.map (·.replicaId)} foreign={foreign.map (·.raw)}"
    | .error e => { name := "readRefEntries verbatim", passed := false, msg := e.message }]
  -- the local publish leg carries it: a new own op republishes; the snapshot
  -- entry survives with its oid untouched and never lands in .tl/log/
  let logDir := System.FilePath.mk d.base / ".tl" / "log"
  IO.FS.createDirAll logDir
  IO.FS.createDirAll (System.FilePath.mk d.base / ".tl" / "local")
  IO.FS.writeBinFile (logDir / s!"{ridA}.jsonl") "{\"a\":1}\n{\"a\":2}\n".toUTF8
  o := o ++ [match ← runTl (syncLocal d (some ridA)) with
    | .ok r => check "a publish over a foreign-bearing ref republishes own ops" (r.ran && r.published)
        (toString (repr r))
    | .error e => { name := "publish over foreign ref", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (readRefEntries d) with
    | .ok (segs, foreign) => check "the local leg carries the foreign entry through the publish verbatim"
        (foreign == [fe "snapshot" snapRaw]
          && segs.any (fun s => s.replicaId == ridA && segStr s == "{\"a\":1}\n{\"a\":2}\n"))
        s!"foreign={foreign.map (·.raw)}"
    | .error e => { name := "local leg carries foreign", passed := false, msg := e.message }]
  o := o ++ [check "the foreign entry is never materialized into .tl/log/"
      (!(← (logDir / "snapshot").pathExists)) ""]
  -- no churn: a converged re-sync moves nothing, and rebuilding the same
  -- content (chained on the new tip) builds the identical tree
  let tipA ← runTl (refTip d)
  o := o ++ [match ← runTl (syncLocal d (some ridA)), tipA with
    | .ok r, .ok t => check "a converged re-sync over a foreign-bearing ref is a no-op"
        (r.ran && !r.published && r.tip == t) (toString (repr r))
    | _, _ => { name := "converged foreign re-sync", passed := false, msg := "unexpected error" }]
  o := o ++ [← do match ← runTl (readRefEntries d), ← runTl (refTip d) with
    | .ok (segs, foreign), .ok (some t) =>
      match ← runTl (writeRef d segs foreign (some t)) with
      | .ok t2 => do
        let tr1 ← treeOf d t
        let tr2 ← treeOf d t2
        pure (check "rebuilding unchanged segments + foreign builds the identical tree"
          (tr1 == tr2) s!"{tr1} vs {tr2}")
      | .error e => pure { name := "identical tree rebuild", passed := false, msg := e.message }
    | _, _ => pure { name := "identical tree rebuild", passed := false, msg := "setup error" }]
  -- a subtree entry (a future format could shard a directory) is carried too
  let subOid ← emptyTree d
  let subRaw := s!"040000 tree {subOid}\tfuture-dir"
  let tipT ← runTl (refTip d)
  o := o ++ [← do match tipT with
    | .ok t =>
      match ← runTl (do
          let (segs, foreign) ← readRefEntries d
          let _ ← writeRef d segs (unionForeign foreign [fe "future-dir" subRaw]) t
          readRefEntries d) with
      | .ok (_, foreign) => pure (check "a tree-typed (subtree) foreign entry is carried verbatim"
          (foreign.any (· == fe "future-dir" subRaw)) s!"foreign={foreign.map (·.raw)}")
      | .error e => pure { name := "subtree entry carried", passed := false, msg := e.message }
    | .error e => pure { name := "subtree entry carried", passed := false, msg := e.message }]
  -- the collision guard: a segment-*named* non-blob entry is dropped outright
  -- (neither a segment nor a carried entry), so it can never collide with that
  -- replica's real segment in a later tree build
  let ridB := (Tl.Clock.Replica.ofNat 2).id
  let dTrap ← gitRepo
  let trapOid ← emptyTree dTrap
  let _ ← runTl (writeRef dTrap [seg ridA "{\"a\":1}\n"]
    [fe s!"{ridB}.jsonl" s!"040000 tree {trapOid}\t{ridB}.jsonl"] none)
  o := o ++ [match ← runTl (readRefEntries dTrap) with
    | .ok (segs, foreign) => check "a segment-named non-blob entry is dropped (collision guard)"
        (segs.map (·.replicaId) == [ridA] && foreign.isEmpty)
        s!"segs={segs.map (·.replicaId)} foreign={foreign.map (·.raw)}"
    | .error e => { name := "segment-named non-blob dropped", passed := false, msg := e.message }]
  -- the remote leg: a foreign entry travels push → bare → second clone's pull
  let (dr, bare) ← repoWithRemote
  let snapOidR ← hashBlob dr "{\"snapshot\":\"r\"}\n"
  let snapRawR := s!"100644 blob {snapOidR}\tsnapshot"
  let _ ← runTl (writeRef dr [seg ridA "{\"a\":1}\n"] [fe "snapshot" snapRawR] none)
  o := o ++ [match ← runTl (syncRemote dr) with
    | .ok r => check "the remote leg pushes a foreign-bearing ref" (r.ran && r.pushed) (toString (repr r))
    | .error e => { name := "remote push with foreign", passed := false, msg := e.message }]
  let dBare : Dirs := { base := bare, tlRel := ".tl" }
  o := o ++ [match ← runTl (readRefEntriesAt dBare "refs/tl/log") with
    | .ok (_, foreign) => check "the pushed remote carries the foreign entry verbatim"
        (foreign == [fe "snapshot" snapRawR]) s!"foreign={foreign.map (·.raw)}"
    | .error e => { name := "remote carries foreign", passed := false, msg := e.message }]
  let work2 ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", work2.toString, "init", "-q"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", work2.toString, "remote", "add", "origin", bare] }
  allowFileProto work2.toString
  let d2 : Dirs := { base := work2.toString, tlRel := ".tl" }
  o := o ++ [match ← runTl (do let _ ← syncRemote d2; readRefEntries d2) with
    | .ok (segs, foreign) => check "a second clone's pull carries the foreign entry into its local ref"
        (foreign == [fe "snapshot" snapRawR] && segs.map (·.replicaId) == [ridA])
        s!"foreign={foreign.map (·.raw)}"
    | .error e => { name := "pull carries foreign", passed := false, msg := e.message }]
  -- same-name conflict across clones: both sides converge on the greater raw
  -- line, whichever direction merges first (no ping-pong churn)
  let ridC := (Tl.Clock.Replica.ofNat 3).id
  let snapOid2 ← hashBlob d2 "{\"snapshot\":\"local2\"}\n"
  let snapRaw2 := s!"100644 blob {snapOid2}\tsnapshot"
  let expected := if decide (snapRawR ≤ snapRaw2) then snapRaw2 else snapRawR
  let tip2 ← runTl (refTip d2)
  o := o ++ [← do match tip2 with
    | .ok t =>
      match ← runTl (do
          let (segs, _) ← readRefEntries d2
          -- clone2 overwrites its snapshot entry (a newer binary would) + adds an op
          let _ ← writeRef d2 (unionSegments segs [seg ridC "{\"c\":1}\n"]) [fe "snapshot" snapRaw2] t
          let _ ← syncRemote d2
          readRefEntriesAt dBare "refs/tl/log") with
      | .ok (_, foreign) => pure (check "a same-name conflict pushes the deterministic pick to the remote"
          (foreign == [fe "snapshot" expected]) s!"foreign={foreign.map (·.raw)} expected={expected}")
      | .error e => pure { name := "conflict pick pushed", passed := false, msg := e.message }
    | .error e => pure { name := "conflict pick pushed", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (do let _ ← syncRemote dr; readRefEntries dr) with
    | .ok (_, foreign) => check "the other clone converges to the same pick on its next sync"
        (foreign == [fe "snapshot" expected]) s!"foreign={foreign.map (·.raw)}"
    | .error e => { name := "conflict convergence", passed := false, msg := e.message }]
  -- push/CAS retry exhaustion: even when every push attempt loses the race
  -- (injected), the locally CASed merge commits keep carrying the entry
  let (dh, _) ← repoWithRemote
  let snapOidH ← hashBlob dh "{\"snapshot\":\"h\"}\n"
  let snapRawH := s!"100644 blob {snapOidH}\tsnapshot"
  let _ ← runTl (writeRef dh [seg ridA "{\"a\":1}\n"] [fe "snapshot" snapRawH] none)
  let _ ← runTl (syncRemote dh (push := fun _ _ _ => pure false)) -- throws push-rejected
  o := o ++ [match ← runTl (readRefEntries dh) with
    | .ok (_, foreign) => check "the foreign entry survives push-retry exhaustion in the local ref"
        (foreign == [fe "snapshot" snapRawH]) s!"foreign={foreign.map (·.raw)}"
    | .error e => { name := "foreign survives retry exhaustion", passed := false, msg := e.message }]
  return o

/-- The lost-CAS retry branches carry foreign entries: a sibling that moves
    the ref between a leg's read and its compare-and-set (injected via the
    `beforeCas` seam, firing once) costs exactly one retry, whose re-read must
    pick up the sibling's segments AND carried-unknown entries — never a
    clobber of either. -/
def syncCasRetryForeignTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let fe := fun (name raw : String) => ({ name, raw } : ForeignEntry)
  -- (A) local leg: the publish loses its CAS to a sibling that also rewrote
  -- the carried entries; the retry re-reads and preserves both writers' work
  let d ← gitRepo
  let ridA := (Tl.Clock.Replica.ofNat 4).id
  let ridB := (Tl.Clock.Replica.ofNat 5).id
  let logDir := System.FilePath.mk d.base / ".tl" / "log"
  IO.FS.createDirAll logDir
  IO.FS.createDirAll (System.FilePath.mk d.base / ".tl" / "local")
  let snapOid ← hashBlob d "{\"snapshot\":1}\n"
  let snap := fe "snapshot" s!"100644 blob {snapOid}\tsnapshot"
  let _ ← runTl (writeRef d [seg ridA "{\"a\":1}\n"] [snap] none)
  IO.FS.writeBinFile (logDir / s!"{ridA}.jsonl") "{\"a\":1}\n{\"a\":2}\n".toUTF8
  let extraOid ← hashBlob d "{\"snapshot\":2}\n"
  let extra := fe "snapshot.next" s!"100644 blob {extraOid}\tsnapshot.next"
  let attempts ← IO.mkRef 0
  let beforeCas : TlM Unit := do
    let n ← (attempts.modifyGet (fun n => (n, n + 1)) : IO Nat)
    if n == 0 then
      -- the racing sibling: publishes its segment and a second carried entry
      let tip ← refTip d
      let (segs, foreign) ← readRefEntries d
      let _ ← writeRef d (unionSegments segs [seg ridB "{\"b\":1}\n"])
        (unionForeign foreign [extra]) tip
  o := o ++ [match ← runTl (syncLocal d (some ridA) beforeCas) with
    | .ok r => check "the local leg publishes through a lost CAS (sibling moved the ref)"
        (r.ran && r.published && r.absorbed == [ridB]) (toString (repr r))
    | .error e => { name := "local leg CAS retry", passed := false, msg := e.message }]
  o := o ++ [check "the lost local CAS cost exactly one retry (two attempts)"
      ((← attempts.get) == 2) s!"attempts={← attempts.get}"]
  o := o ++ [match ← runTl (readRefEntries d) with
    | .ok (segs, foreign) => check "the retry's re-read carries both writers' segments and foreign entries"
        (foreign == [snap, extra]
          && segs.any (fun s => s.replicaId == ridA && segStr s == "{\"a\":1}\n{\"a\":2}\n")
          && segs.any (fun s => s.replicaId == ridB && segStr s == "{\"b\":1}\n"))
        s!"segs={segs.map (·.replicaId)} foreign={foreign.map (·.name)}"
    | .error e => { name := "local CAS retry carries foreign", passed := false, msg := e.message }]
  -- (B) remote leg: the merge CAS loses to a concurrent local publisher; the
  -- retry's merge commit reaches the remote with both writers' entries
  let (dr, bare) ← repoWithRemote
  let ridC := (Tl.Clock.Replica.ofNat 6).id
  let snapROid ← hashBlob dr "{\"snapshot\":\"r1\"}\n"
  let snapR := fe "snapshot" s!"100644 blob {snapROid}\tsnapshot"
  let _ ← runTl (writeRef dr [seg ridA "{\"a\":1}\n"] [snapR] none)
  let sib2Oid ← hashBlob dr "{\"snapshot\":\"r2\"}\n"
  let sib2 := fe "snapshot.aux" s!"100644 blob {sib2Oid}\tsnapshot.aux"
  let rAttempts ← IO.mkRef 0
  let beforeCasR : TlM Unit := do
    let n ← (rAttempts.modifyGet (fun n => (n, n + 1)) : IO Nat)
    if n == 0 then
      let tip ← refTip dr
      let (segs, foreign) ← readRefEntries dr
      let _ ← writeRef dr (unionSegments segs [seg ridC "{\"c\":1}\n"])
        (unionForeign foreign [sib2]) tip
  o := o ++ [match ← runTl (syncRemote dr (beforeCas := beforeCasR)) with
    | .ok r => check "the remote leg pushes through a lost local CAS"
        (r.ran && r.pushed) (toString (repr r))
    | .error e => { name := "remote leg CAS retry", passed := false, msg := e.message }]
  o := o ++ [check "the lost merge CAS cost exactly one retry (two attempts)"
      ((← rAttempts.get) == 2) s!"attempts={← rAttempts.get}"]
  let dBare : Dirs := { base := bare, tlRel := ".tl" }
  o := o ++ [match ← runTl (readRefEntriesAt dBare "refs/tl/log") with
    | .ok (segs, foreign) => check "the pushed retry merge carries both writers' segments and foreign entries"
        (foreign == [snapR, sib2]
          && segs.any (·.replicaId == ridA) && segs.any (·.replicaId == ridC))
        s!"segs={segs.map (·.replicaId)} foreign={foreign.map (·.name)}"
    | .error e => { name := "remote CAS retry carries foreign", passed := false, msg := e.message }]
  return o

/-- A foreign-only difference is a deliberate no-op (ADR-0008): equal
    segments with differing carried-unknown entries build no commit, push
    nothing, pull nothing, and delete nothing on either side — a stable
    divergence that only the next segment-driven merge reconciles. -/
def syncForeignNoOpTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let fe := fun (name raw : String) => ({ name, raw } : ForeignEntry)
  let ridA := (Tl.Clock.Replica.ofNat 7).id
  let ridB := (Tl.Clock.Replica.ofNat 8).id
  let (d, bare) ← repoWithRemote
  let dBare : Dirs := { base := bare, tlRel := ".tl" }
  let aOid ← hashBlob d "{\"snapshot\":\"a\"}\n"
  let fA := fe "snapshot" s!"100644 blob {aOid}\tsnapshot"
  let _ ← runTl (writeRef d [seg ridA "{\"a\":1}\n"] [fA] none)
  let _ ← runTl (syncRemote d)   -- the bare now mirrors this tree
  -- a foreign writer replaces the snapshot on the remote only (same segments)
  let bOid ← hashBlob dBare "{\"snapshot\":\"b\"}\n"
  let fB := fe "snapshot" s!"100644 blob {bOid}\tsnapshot"
  let _ ← runTl (do
    let tip ← refTip dBare
    let (segs, _) ← readRefEntriesAt dBare "refs/tl/log"
    writeRef dBare segs [fB] tip)
  let tipBefore ← runTl (refTip d)
  o := o ++ [match ← runTl (syncRemote d), tipBefore with
    | .ok r, .ok t => check "a foreign-only remote difference is a full no-op (no pull, no push, no commit)"
        (r.ran && !r.pushed && !r.pulled && r.tip == t) (toString (repr r))
    | _, _ => { name := "foreign-only no-op", passed := false, msg := "unexpected error" }]
  o := o ++ [match ← runTl (readRefEntries d), ← runTl (readRefEntriesAt dBare "refs/tl/log") with
    | .ok (_, lf), .ok (_, rf) => check "the no-op deletes neither side's entry (a stable divergence)"
        (lf == [fA] && rf == [fB]) s!"local={lf.map (·.raw)} remote={rf.map (·.raw)}"
    | _, _ => { name := "no-op preserves both sides", passed := false, msg := "unexpected error" }]
  -- the next segment-driven merge reconciles the divergence to the one pick
  let expected := if decide (fA.raw ≤ fB.raw) then fB else fA
  let _ ← runTl (do
    let tip ← refTip d
    let (segs, foreign) ← readRefEntries d
    writeRef d (unionSegments segs [seg ridB "{\"b\":1}\n"]) foreign tip)
  o := o ++ [match ← runTl (syncRemote d) with
    | .ok r => check "a subsequent segment-driven sync builds and pushes the merge" (r.ran && r.pushed)
        (toString (repr r))
    | .error e => { name := "segment-driven merge", passed := false, msg := e.message }]
  o := o ++ [match ← runTl (readRefEntries d), ← runTl (readRefEntriesAt dBare "refs/tl/log") with
    | .ok (_, lf), .ok (_, rf) => check "the segment-driven merge reconciles both sides to the deterministic pick"
        (lf == [expected] && rf == [expected])
        s!"local={lf.map (·.raw)} remote={rf.map (·.raw)} expected={expected.raw}"
    | _, _ => { name := "merge reconciles divergence", passed := false, msg := "unexpected error" }]
  return o

private def fixtureGit (d : Dirs) (args : List String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args := #["-C", d.base] ++ args.toArray }

/-- Snapshot evidence stays attached to the resolved object even when its
    original ref moves. Tests use the public snapshot type, not reconstructed
    OID strings, so callers exercise the production capture/read boundary. -/
def syncSnapshotTests : IO (List Outcome) := do
  let d ← gitRepo
  let result ← runTl do
    let old ← writeRef d [seg "0123456789abc" "old\n"] [] none
    let pinned ← pinLogRef d
    let fresh ← writeRef d [seg "0123456789abd" "new\n"] [] (some old)
    let (captured, _) ← readPinnedEntries? d pinned
    let (current, _) ← readRefEntries d
    let missing ← pinRef d "refs/heads/absent"
    let (empty, emptyForeign) ← readPinnedEntries? d missing
    return [
      check "captured contents and identity survive movement of the source ref"
        (pinned.map (·.oid) == some old && fresh != old
          && captured.map segStr == ["old\n"] && current.map segStr == ["new\n"]),
      check "an absent snapshot has no identity or entries"
        (missing.isNone && empty.isEmpty && emptyForeign.isEmpty)]
  let outside ← IO.FS.createTempDir
  let failed ← runTl (pinLogRef { base := outside.toString, tlRel := ".tl" })
  let failure := match failed with
    | .error e => check "snapshot resolution reports operational Git failure"
        (e.code == .internal && (e.message.splitOn "rev-parse").length > 1)
    | .ok _ => check "snapshot resolution reports operational Git failure" false
  return (match result with
    | .ok rows => rows
    | .error e => [check "snapshot fixture completes" false e.message]) ++ [failure]

/-- Ordinary Git fetches and another transport fetch can overlap the private
    fetch lifetime without changing its evidence. Failures must not leak the
    temporary ref or turn missing/invalid evidence into an empty success. -/
def syncFetchIsolationTests : IO (List Outcome) := do
  let (d, bare) ← repoWithRemote
  let remote : Dirs := { base := bare, tlRel := ".tl" }
  let refs : TlM (List String) := do
    let out ← fixtureGit d ["for-each-ref", "--format=%(refname)", "refs/tl/incoming/"]
    if out.exitCode != 0 then throw (.mk' .internal out.stderr)
    return (out.stdout.splitOn "\n").filter (· != "")
  let result ← runTl do
    -- A separate ordinary branch with both a replica-shaped entry and an
    -- unknown file makes accidental import observable in both tree classes.
    let firstBranch ← writeRef remote [seg "0123456789abd" "branch\n"] [] none
    let branchListing ← fixtureGit remote ["ls-tree", firstBranch]
    let branchOid := (((branchListing.stdout.splitOn "\t").head!).splitOn " ")[2]!
    let ordinaryFile : ForeignEntry :=
      { name := "ordinary-file", raw := s!"100644 blob {branchOid}\tordinary-file" }
    let branch ← writeRef remote [seg "0123456789abd" "branch\n"] [ordinaryFile] (some firstBranch)
    let _ ← fixtureGit remote ["update-ref", "refs/heads/main", branch]
    let _ ← fixtureGit remote ["update-ref", "-d", "refs/tl/log"]
    let expected ← writeRef remote [seg "0123456789abc" "task\n"] [] none
    let _ ← fixtureGit d ["config", "--add", "remote.origin.fetch", "+refs/tl/log:refs/tl/log"]
    let overlap ← IO.mkRef false
    let (tip, segments, foreign) ← fetchRemoteLog d "origin" (afterFetch := do
      let outerRefs ← refs
      let (innerTip, innerSegs, _) ← fetchRemoteLog d "origin" (afterFetch := do
        let both ← refs
        overlap.set (both.length == 2 && both.eraseDups.length == 2
          && outerRefs.all both.contains))
      unless innerTip == some expected && innerSegs.map segStr == ["task\n"] do
        throw (.mk' .internal "nested fetch read the wrong snapshot")
      let ordinary ← fixtureGit d ["fetch", "origin", "refs/heads/main"]
      unless ordinary.exitCode == 0 do throw (.mk' .internal ordinary.stderr))
    let fetchHead ← pinRef d "FETCH_HEAD"
    let remaining ← refs
    let localPinned ← pinLogRef d
    let mut rows := [
      check "overlapping fetches use distinct live private refs" (← overlap.get),
      check "ordinary FETCH_HEAD replacement cannot change transport evidence"
        (tip == some expected && segments.map segStr == ["task\n"] && foreign.isEmpty
          && fetchHead.map (·.oid) == some branch),
      check "fetch removes its private refs without moving the local task-log ref"
        (remaining.isEmpty && localPinned.isNone)]
    -- Exception after the real fetch, while the temporary ref exists.
    let failed : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ← (fetchRemoteLog d "origin" (afterFetch :=
      throw (.mk' .internal "injected post-fetch failure"))).run
    rows := rows ++ [check "post-fetch failure is refused and cleans its private ref"
      ((match failed with | .error _ => true | .ok _ => false) && (← refs).isEmpty)]
    -- A disappeared private ref must never look like a fresh remote.
    let vanished : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ← (fetchRemoteLog d "origin" (afterFetch := do
      for name in ← refs do
        let _ ← fixtureGit d ["update-ref", "-d", name])).run
    rows := rows ++ [check "a vanished fetched ref is an error, not an empty remote"
      (match vanished with
       | .error e => (e.message.splitOn "disappeared").length > 1
       | .ok _ => false)]
    -- Both entropy error paths happen before a private ref can be allocated.
    let short : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ← (fetchRemoteLog d "origin" (entropy := fun _ => pure .empty)).run
    let unavailable : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ← (fetchRemoteLog d "origin" (entropy := fun _ =>
      throw (IO.userError "injected entropy failure"))).run
    rows := rows ++ [check "short and unavailable entropy refuse without leaking refs"
      ((match short with | .error _ => true | .ok _ => false) && (match unavailable with | .error _ => true | .ok _ => false) && (← refs).isEmpty)]
    -- Pinning succeeds for an object that cannot be read as a tree; the
    -- read error still traverses the same cleanup boundary.
    let badTree : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ← (fetchRemoteLog d "origin" (afterFetch := do
      let listing ← fixtureGit d ["ls-tree", expected]
      let oid := (((listing.stdout.splitOn "\t").head!).splitOn " ")[2]!
      for name in ← refs do
        let out ← fixtureGit d ["update-ref", name, oid]
        unless out.exitCode == 0 do throw (.mk' .internal out.stderr))).run
    rows := rows ++ [check "invalid fetched tree is refused and cleaned"
      ((match badTree with | .error _ => true | .ok _ => false) && (← refs).isEmpty)]
    let fetchFailed : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ←
      (fetchRemoteLog d "origin" (entropy := fun count => do
        let _ ← fixtureGit d ["config", "protocol.file.allow", "never"]
        Sys.entropy count)).run
    let _ ← fixtureGit d ["config", "protocol.file.allow", "always"]
    rows := rows ++ [check "a transport failure after allocation traverses cleanup"
      ((match fetchFailed with | .error e => e.code == .internal | .ok _ => false)
        && (← refs).isEmpty)]
    let cleanupFailed : Except Tl.Error (Option String × List SegmentData × List ForeignEntry) ←
      (fetchRemoteLog d "origin" (afterFetch := do
        for name in ← refs do
          IO.FS.writeFile (System.FilePath.mk d.base / ".git" / (name ++ ".lock")) "")).run
    rows := rows ++ [check "private-ref cleanup failures are reported rather than hidden"
      (match cleanupFailed with
       | .error e => e.code == .internal && (e.message.splitOn "update-ref").length > 1
       | .ok _ => false)]
    for name in ← refs do
      IO.FS.removeFile (System.FilePath.mk d.base / ".git" / (name ++ ".lock"))
      let _ ← fixtureGit d ["update-ref", "-d", name]
    return rows
  return match result with
  | .ok rows => rows
  | .error e => [check "fetch isolation fixture completes" false e.message]

/-- Recovery tests exercise durable bytes, identity changes, lock ordering,
    and failure cleanup. The selector's set algebra is proved in Recovery. -/
def syncRecoveryTests : IO (List Outcome) := do
  let d ← gitRepo
  let rid := "0123456789abc"
  let result ← runTl do
    liftSys (fun e => .mk' .internal (toString e)) (Sys.mkdirNoFollow d.base d.relLocal)
    writeLocalFile d d.relReplica (rid ++ "\n")
    appendOwnRaw d rid ["old".toUTF8] false
    let changed ← recoverOwnSegment d rid "old\npeer\n".toUTF8 (beforeLock := do
      let fd ← acquireLock d
      try appendOwnRaw d rid ["concurrent".toUTF8, "peer".toUTF8] false
      finally releaseLock fd)
    let bytes ← readSegment d rid
    let untouched ← recoverOwnSegment d rid "peer\n".toUTF8 (beforeLock :=
      throw (.mk' .internal "a no-op must not take the recovery lock"))
    let mut rows := [
      check "recovery rereads after the lock and preserves concurrent local appends"
        (!changed && bytes == "old\nconcurrent\npeer\n".toUTF8),
      check "already recovered lines need neither an append nor a lock" (!untouched)]
    let raw : ByteArray := ⟨#[0xff, 0xfe, 10]⟩
    let recovered ← recoverOwnSegment d rid raw
    rows := rows ++ [check "recovery appends unknown bytes without a UTF-8 round trip"
      (recovered && (← readSegment d rid) == bytes ++ raw)]
    let before := (← readSegment d rid)
    let mismatch : Except Tl.Error Bool ← (recoverOwnSegment d rid "later\n".toUTF8
      (beforeLock := writeLocalFile d d.relReplica "0123456789abd\n")).run
    rows := rows ++ [check "identity change under the recovery lock refuses without appending"
      ((match mismatch with | .error _ => true | .ok _ => false)
        && (← readSegment d rid) == before)]
    writeLocalFile d d.relReplica (rid ++ "\n")
    let held ← acquireLock d
    let busy : Except Tl.Error Bool ← (recoverOwnSegment d rid "later\n".toUTF8
      (timeoutMs := 0)).run
    releaseLock held
    rows := rows ++ [check "recovery honors lock contention and changes no bytes"
      ((match busy with | .error e => e.code == .lockBusy | .ok _ => false)
        && (← readSegment d rid) == before)]
    let failed : Except Tl.Error Bool ← (recoverOwnSegment d rid "later\n".toUTF8
      (syncMechanism := fun _ => throw (IO.userError "injected barrier failure"))).run
    let released ← acquireLock d 0
    releaseLock released
    rows := rows ++ [check "recovery reports a failed durability barrier and releases the lock"
      (match failed with | .error _ => true | .ok _ => false)]
    -- A crash fragment is closed using the same discipline as a local write.
    appendOwnRaw d rid [] false
    liftSys (fun e => .mk' .internal (toString e)) do
      Sys.withFd d.base (d.relSegment rid) Sys.flagAppend fun fd =>
        Sys.writeAll fd "tail".toUTF8
    let oldTail ← readSegment d rid
    let closed ← recoverOwnSegment d rid "final\n".toUTF8
    rows := rows ++ [check "recovery preserves and closes a torn tail before appending"
      (closed && (← readSegment d rid) == oldTail ++ "\nfinal\n".toUTF8)]
    -- Markers from the old recovery semantics cannot suppress a first read.
    writeLocalFile d d.relRefMark "old-tip\n"
    writeLocalFile d d.relSyncPub "old-tip 3 5\n"
    rows := rows ++ [check "legacy sync markers force recovery after upgrade"
      ((← loadRefMark d).isNone && (← loadSyncPub d).isNone)]
    writeLocalFile d d.relRefMark "2 too many fields\n"
    writeLocalFile d d.relSyncPub "2 tip invalid 5\n"
    rows := rows ++ [check "malformed current markers force reconciliation"
      ((← loadRefMark d).isNone && (← loadSyncPub d).isNone)]
    storeRefMark d "new-tip"
    storeSyncPub d "new-tip" before
    rows := rows ++ [check "current sync markers round-trip their evidence"
      ((← loadRefMark d) == some "new-tip"
        && (← loadSyncPub d) == some ("new-tip", before.size, ByteArray.hash before))]
    return rows
  return match result with
  | .ok rows => rows
  | .error e => [check "recovery I/O fixture completes" false e.message]

/-- Every pipe belongs to the deadline, even after successful child exit.
    Delayed descendants are finite so a regression fails instead of hanging
    the test suite; marker files also observe process-group cleanup. -/
private def inheritedPipeCorpus (label : String)
    (runner : IO.Process.SpawnArgs → ByteArray → Nat → IO (UInt32 × ByteArray × String))
    (withStdin : Bool) : IO (List Outcome) := do
  let root ← IO.FS.createTempDir
  let mut rows := []
  let streams := if withStdin then ["stdout", "stderr", "stdin"] else ["stdout", "stderr"]
  for stream in streams do
    let marker := root / stream
    let command := match stream with
      | "stdout" => "(sleep 2; echo survived > \"$1\") 2>/dev/null & exit 0"
      | "stderr" => "(sleep 2; echo survived > \"$1\") >/dev/null & exit 0"
      | _ => "exec 3<&0; (sleep 2; echo survived > \"$1\") <&3 >/dev/null 2>&1 & exit 0"
    let input := if stream == "stdin" then ByteArray.mk (Array.replicate 1048576 97) else .empty
    let started ← IO.monoMsNow
    let (code, _, error) ← runner
      { cmd := "sh", args := #["-c", command, "pipe-fixture", marker.toString] } input 100
    let elapsed := (← IO.monoMsNow) - started
    rows := rows ++ [check s!"{label}: the {stream} task remains inside the deadline after child exit"
      (code == 124 && elapsed < 1500 && (error.splitOn "timed out").length > 1)
      s!"code={code}, elapsed={elapsed}, error={error}"]
  IO.sleep 2200
  for stream in streams do
    rows := rows ++ [check s!"{label}: timeout terminates the descendant holding {stream}"
      (!(← (root / stream).pathExists))]
  let (code, out, err) ← runner
    { cmd := "sh", args := #["-c", "printf out; printf err >&2"] } .empty 5000
  rows := rows ++ [check s!"{label}: successful process completion preserves both streams"
    (code == 0 && out == "out".toUTF8 && err == "err")]
  return rows

def syncInheritedPipeTests : IO (List Outcome) := do
  let invalidZero ← Sys.terminateProcessGroup 0
  let invalidOne ← Sys.terminateProcessGroup 1
  let invalidRange ← Sys.terminateProcessGroup 4294967295
  let forming ← IO.Process.spawn { cmd := "sleep", args := #["2"] }
  let stoppedLeader ← Sys.terminateProcessGroup (Sys.childPid forming)
  let stoppedStatus ← forming.wait
  let product ← inheritedPipeCorpus "product" runBounded true
  let releaseRunner (cfg : IO.Process.SpawnArgs) (_ : ByteArray) (timeoutMs : Nat) := do
    match ← Release.run cfg.cmd cfg.args timeoutMs with
    | .completed output => pure (output.exitCode, output.stdout.toUTF8, output.stderr)
    | .timedOut _ _ => pure (124, ByteArray.empty, "timed out")
    | .unavailable _ detail => pure (127, ByteArray.empty, detail)
  let administration ← inheritedPipeCorpus "release" releaseRunner false
  -- Both supported hosts expose /dev/fd. Compare live descriptors rather
  -- than depending on the host's soft limit to make a leak fail eventually.
  let fdDirectory : System.FilePath := "/dev/fd"
  let descriptorsBefore := (← fdDirectory.readDir).size
  let mut repeatedSucceeded := true
  for _ in [0:100] do
    let (status, _, _) ← runBounded { cmd := "true" } .empty 5000
    repeatedSucceeded := repeatedSucceeded && status == 0
  let descriptorsAfter := (← fdDirectory.readDir).size
  let (unbounded, inherited, _) ← runBounded
    { cmd := "sh", args := #["-c", "(sleep 1; printf late) & exit 0"] } .empty 0
  return product ++ administration ++ [
    check "repeated process completion releases child pipe descriptors"
      (repeatedSucceeded && descriptorsAfter ≤ descriptorsBefore + 3)
      s!"before={descriptorsBefore}, after={descriptorsAfter}",
    check "group cleanup rejects unsafe ids without signalling"
      (!invalidZero && !invalidOne && !invalidRange),
    check "group cleanup can stop an owned leader before a group exists"
      (stoppedLeader && stoppedStatus != 0),
    check "product zero timeout waits for inherited streams to finish"
      (unbounded == 0 && inherited == "late".toUTF8)]

def syncTests : IO (List Outcome) := do
  return syncMergeTests ++ syncMergeCanonicalProp ++ (← syncRefTests) ++ (← syncLocalTests)
    ++ (← syncRefreshTests) ++ (← syncRemoteTests) ++ (← syncTimeoutTests)
    ++ (← syncRecoveryTests) ++ (← syncInheritedPipeTests)
    ++ (← syncSnapshotTests) ++ (← syncFetchIsolationTests)
    ++ (← syncEnvScrubTests)
    ++ (← syncRefNameValidationTests) ++ (← syncForeignEntryTests)
    ++ (← syncCasRetryForeignTests) ++ (← syncForeignNoOpTests)

end Tl.Tests
