/-
`Tl.Sync.Ref` — read/write the dedicated `refs/tl/log` via git plumbing
(ADR-0001 §2/§5). Stage-3 sharing's foundation; the transport legs (local
worktree, remote fetch/push) build on this and the line-union (`Merge`).

`tl` never touches the user's index, branch, or HEAD — only this ref, via
`hash-object` / `mktree` / `commit-tree` / `update-ref`. In-ref encoding
(decided here, ADR-0001): the ref commit's tree holds one blob per replica
named `<replica-id>.jsonl` at the root (the tree *is* the `log/` contents);
commits are parent-chained (so a non-fast-forward push is detectable);
the author/committer is a fixed neutral `tl <tl@localhost>` set via
`GIT_*` env, so a sync leaks no per-user git identity into ref metadata
(the actor already rides each op's envelope as provenance, ADR-0013).

git is shelled out (a runtime prerequisite, ADR-0006), never linked. Tested
I/O shell; no Mathlib. The full `tl sync` orchestration (local writeback +
the legs) is a separate command atop these primitives.
-/
import Tl.Store.Segment

namespace Tl.Sync

open Tl.Store

/-- The repo to run git in: the directory holding `.tl` (`""` ⇒ cwd). -/
private def repoOf (d : Dirs) : String := if d.base.isEmpty then "." else d.base

private def fixedIdentity : List (String × Option String) :=
  [("GIT_AUTHOR_NAME", some "tl"), ("GIT_AUTHOR_EMAIL", some "tl@localhost"),
   ("GIT_COMMITTER_NAME", some "tl"), ("GIT_COMMITTER_EMAIL", some "tl@localhost")]

/-- Run `git -C <repo> <args>` (optional stdin / extra env). -/
private def git (d : Dirs) (args : List String) (stdin : String := "")
    (env : List (String × Option String) := []) : IO IO.Process.Output :=
  IO.Process.output
    { cmd := "git", args := (#["-C", repoOf d] ++ args.toArray), env := env.toArray } stdin

/-- A git plumbing failure that isn't an expected condition is `internal`
    (the caller maps "not a repo" / "no remote" to no-upstream itself). -/
private def gitErr (op : String) (o : IO.Process.Output) : Tl.Error :=
  .mk' .internal s!"git {op} failed (exit {o.exitCode}): {o.stderr.trimAscii.toString}"

private def run (d : Dirs) (op : String) (args : List String) (stdin : String := "")
    (env : List (String × Option String) := []) : TlM String := do
  let o ← (git d args stdin env : IO _)
  if o.exitCode == 0 then return o.stdout.trimAscii.toString
  else throw (gitErr op o)

/-- Run git with raw-`ByteArray` stdin and stdout — the byte-faithful path for
    `hash-object`/`cat-file`. `IO.Process.output` decodes both streams as
    `String` (UTF-8, lossy / panicking), but a segment line may carry arbitrary
    bytes (the union is a *byte*-level line set, ADR-0001 §5; per-line UTF-8 is
    only checked later at decode). The stdin handle is written then dropped so
    git sees EOF before `wait` (mirroring the stdlib `IO.Process.output`),
    and stdout is read on a task so a full stdout pipe can't deadlock a large
    stdin write. Returns `(exitCode, stdout-bytes, stderr-text)`. -/
private def gitBytes (d : Dirs) (args : List String) (stdin : ByteArray := .empty) :
    IO (UInt32 × ByteArray × String) := do
  let spawned ← IO.Process.spawn
    { cmd := "git", args := #["-C", repoOf d] ++ args.toArray,
      stdin := .piped, stdout := .piped, stderr := .piped }
  let child ← do
    let (stdinH, child) ← spawned.takeStdin
    stdinH.write stdin
    stdinH.flush
    pure child  -- stdinH drops here ⇒ the child's stdin reaches EOF
  let outTask ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept outTask.get
  return (code, out, err)

/-- The `TlM` wrapper over `gitBytes`: a non-zero exit is an `internal` git
    failure carrying the stderr (the caller maps expected conditions itself). -/
private def runBytes (d : Dirs) (op : String) (args : List String)
    (stdin : ByteArray := .empty) : TlM ByteArray := do
  let (code, out, err) ← (gitBytes d args stdin : IO _)
  if code == 0 then return out
  else throw (.mk' .internal s!"git {op} failed (exit {code}): {err.trimAscii.toString}")

/-- Is the `.tl` directory inside a usable git repository? (The override /
    repo-less case has no ref transport — the caller reports `no-upstream`.) -/
def inGitRepo (d : Dirs) : IO Bool := do
  let o ← git d ["rev-parse", "--git-dir"]
  return o.exitCode == 0

/-- The current `refs/tl/log` commit oid, or `none` if the ref is unset. -/
def refTip (d : Dirs) : TlM (Option String) := do
  let o ← (git d ["rev-parse", "--verify", "--quiet", "refs/tl/log"] : IO _)
  if o.exitCode == 0 then return some o.stdout.trimAscii.toString else return none

/-- The segments stored in `refs/tl/log` (empty when the ref is unset). Reads
    the commit's tree: one `<replica-id>.jsonl` blob per replica. -/
def readRef (d : Dirs) : TlM (List SegmentData) := do
  match ← refTip d with
  | none => return []
  | some _ =>
    let listing ← run d "ls-tree" ["ls-tree", "refs/tl/log"]
    let entries := listing.splitOn "\n" |>.filter (· ≠ "")
    entries.filterMapM fun line => do
      -- "<mode> <type> <oid>\t<name>"
      match line.splitOn "\t" with
      | [info, name] =>
        if name.endsWith ".jsonl" then
          match info.splitOn " " with
          | [_, "blob", oid] =>
            -- the blob is the raw segment bytes (may be non-UTF-8) — read them
            -- byte-faithfully, never through a String stdout
            let bytes ← runBytes d "cat-file" ["cat-file", "blob", oid]
            return some { replicaId := (name.dropEnd 6).toString, bytes }
          | _ => return none
        else return none
      | _ => return none

/-- Build the new `refs/tl/log` commit (blob per segment, one tree, a
    parent-chained commit under the neutral identity) WITHOUT moving the ref —
    the caller does the compare-and-set `update-ref`. Returns the commit oid. -/
private def buildCommit (d : Dirs) (segs : List SegmentData) (expectedTip : Option String) :
    TlM String := do
  -- a blob per segment (raw bytes via stdin — never String.fromUTF8!, which
  -- panics on a non-UTF-8 segment line; the oid out is plain ASCII hex)
  let entries ← segs.mapM fun s => do
    let oidRaw ← runBytes d "hash-object" ["hash-object", "-w", "--stdin"] s.bytes
    let oid := ((String.fromUTF8? oidRaw).getD "").trimAscii.toString
    pure s!"100644 blob {oid}\t{s.replicaId}.jsonl"
  let tree ← run d "mktree" ["mktree"] (stdin := String.intercalate "\n" entries)
  let commitArgs := ["commit-tree", tree, "-m", "tl log"]
    ++ (match expectedTip with | some p => ["-p", p] | none => [])
  run d "commit-tree" commitArgs (env := fixedIdentity)

/-- The compare-and-set `update-ref` argv: require the ref still be
    `expectedTip` (or absent — the empty old-value). -/
private def casArgs (commit : String) (expectedTip : Option String) : List String :=
  ["update-ref", "refs/tl/log", commit]
    ++ (match expectedTip with | some p => [p] | none => [""])

/-- Write `segs` as the new `refs/tl/log` tip with a compare-and-set against
    `expectedTip` (the value `readRef` was based on), so a concurrent writer is
    not clobbered. Throws on a CAS rejection (a stale tip) like any git
    failure. Returns the new commit oid. -/
def writeRef (d : Dirs) (segs : List SegmentData) (expectedTip : Option String) : TlM String := do
  let commit ← buildCommit d segs expectedTip
  let _ ← run d "update-ref" (casArgs commit expectedTip)
  return commit

/-- Like `writeRef`, but distinguishes a *lost CAS race* (a sibling moved the
    ref between the read and this write — `none`, the local-leg retry signal)
    from a genuine git failure (still thrown). It disambiguates by re-reading
    the tip after a failed `update-ref`: a tip that no longer equals
    `expectedTip` was a concurrent move; an unchanged tip means the failure
    was something else (permissions, a corrupt object store). -/
def writeRefCas (d : Dirs) (segs : List SegmentData) (expectedTip : Option String) :
    TlM (Option String) := do
  let commit ← buildCommit d segs expectedTip
  let o ← (git d (casArgs commit expectedTip) : IO _)
  if o.exitCode == 0 then return some commit
  else if (← refTip d) != expectedTip then return none  -- a sibling moved it: retry
  else throw (gitErr "update-ref" o)

end Tl.Sync
