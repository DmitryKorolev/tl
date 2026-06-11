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
            let o ← (git d ["cat-file", "blob", oid] : IO _)
            if o.exitCode == 0 then
              return some { replicaId := (name.dropEnd 6).toString, bytes := o.stdout.toUTF8 }
            else throw (gitErr "cat-file" o)
          | _ => return none
        else return none
      | _ => return none

/-- Write `segs` as the new `refs/tl/log` tip: blob per segment, one tree,
    a parent-chained commit (neutral identity), then a compare-and-set
    `update-ref` against `expectedTip` (the value `readRef` was based on) so a
    concurrent writer is not clobbered. Returns the new commit oid. -/
def writeRef (d : Dirs) (segs : List SegmentData) (expectedTip : Option String) : TlM String := do
  -- a blob per segment (content via stdin; segments are UTF-8 JSONL, ADR-0008)
  let entries ← segs.mapM fun s => do
    let oid ← run d "hash-object" ["hash-object", "-w", "--stdin"]
      (stdin := String.fromUTF8! s.bytes)
    pure s!"100644 blob {oid}\t{s.replicaId}.jsonl"
  let tree ← run d "mktree" ["mktree"] (stdin := String.intercalate "\n" entries)
  let commitArgs := ["commit-tree", tree, "-m", "tl log"]
    ++ (match expectedTip with | some p => ["-p", p] | none => [])
  let commit ← run d "commit-tree" commitArgs (env := fixedIdentity)
  -- compare-and-set: require the ref still be `expectedTip` (or absent)
  let casArgs := ["update-ref", "refs/tl/log", commit]
    ++ (match expectedTip with | some p => [p] | none => [""])
  let _ ← run d "update-ref" casArgs
  return commit

end Tl.Sync
