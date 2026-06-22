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

/-- Local git plumbing is sub-second on tl's tiny ref; this short wall-clock
    bound catches a *hung* local git (a stale index/ref lock, a credential helper
    waiting on input) without false-timing a legitimately slow op. -/
private def localGitTimeoutMs : Nat := 5000

/-- The network legs (ls-remote / fetch / push) get a longer bound — a slow or
    congested network is normal; an unbounded wait on an unreachable remote is
    the failure to prevent. -/
private def remoteGitTimeoutMs : Nat := 30000

/-- Spawn `cfg` with `stdin`, waiting at most `timeoutMs` for it to exit. On
    expiry the child is SIGTERM-killed — so a hung git can never wedge a tl
    command — and the result is `(124, .empty, "timed out …")`: the conventional
    timeout exit, which every caller already treats as a git failure (→ a
    best-effort `degraded` note, or a thrown `internal`). Otherwise the real
    `(exitCode, stdout-bytes, stderr-text)`. Both pipes drain on tasks so a full
    stdout/stderr buffer can't deadlock the wait; the wait is a 10ms `tryWait`
    poll on the calling thread — no extra thread, ≤10ms fast-path latency, no
    busy-spin. Tested via `sleep`/`true`, no hung git needed. -/
def runBounded (cfg : IO.Process.SpawnArgs) (stdin : ByteArray) (timeoutMs : Nat) :
    IO (UInt32 × ByteArray × String) := do
  let spawned ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdinH, child) ← spawned.takeStdin
  -- drain stdout/stderr and write stdin on concurrent tasks before the wait. A child
  -- that interleaves a large stdout with reading a large stdin would otherwise deadlock
  -- against a synchronous stdin write (its stdout pipe fills with no reader, so it
  -- blocks writing stdout while we block writing stdin). The write task owns `stdinH`,
  -- so the handle closes (child stdin EOF) as soon as the write completes — not at
  -- function end — which the EOF-driven callers (hash-object/mktree) need; a broken
  -- pipe (the child already exited) is caught and benign.
  let outTask ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let errTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let _inTask ← IO.asTask
    (try (do stdinH.write stdin; stdinH.flush) catch _ => pure ())
    Task.Priority.dedicated
  let mut code? : Option UInt32 := none
  if timeoutMs == 0 then
    code? := some (← child.wait)  -- 0 ⇒ unbounded: the git-config opt-out
  else
    let stepMs := 10
    for _ in [0 : timeoutMs / stepMs + 1] do
      code? := (← child.tryWait)
      if code?.isSome then break
      IO.sleep (UInt32.ofNat stepMs)
  match code? with
  | some code =>
    let out ← IO.ofExcept outTask.get
    let err ← IO.ofExcept errTask.get
    return (code, out, err)
  | none =>
    child.kill
    return (124, ByteArray.empty,
      s!"timed out after {timeoutMs}ms — a hung git (a stale lock, a credential helper waiting on input, or an unreachable remote)")

/-- Per-repo memo of the resolved (local, remote) timeouts, so the git-config
    read happens at most once per repo per process (tl is one-shot; a process may
    touch several repos under test) — never once per git call. -/
initialize timeoutCache : IO.Ref (List (String × Nat × Nat)) ← IO.mkRef []

/-- Read one `tl.git*TimeoutMs` git-config value (ms), falling back to `dflt`
    when unset or non-numeric. The config read is itself bounded (the local
    default) so a hung git can't even wedge timeout resolution. `0` is legal — it
    disables the bound (see `runBounded`). -/
private def readTimeoutNat (d : Dirs) (key : String) (dflt : Nat) : IO Nat := do
  let (code, out, _) ← runBounded
    { cmd := "git", args := #["-C", repoOf d, "config", "--get", key] } .empty localGitTimeoutMs
  if code != 0 then return dflt
  return (((String.fromUTF8? out).getD "").trimAscii.toString.toNat?).getD dflt

/-- The (local, remote) git timeouts for `d`, read fresh from git config
    (`tl.gitTimeoutMs` / `tl.gitRemoteTimeoutMs`, ms; defaults `localGitTimeoutMs`
    / `remoteGitTimeoutMs`). Public for tests; production uses the cached
    `resolveTimeouts`. -/
def readTimeoutsUncached (d : Dirs) : IO (Nat × Nat) :=
  return (← readTimeoutNat d "tl.gitTimeoutMs" localGitTimeoutMs,
          ← readTimeoutNat d "tl.gitRemoteTimeoutMs" remoteGitTimeoutMs)

/-- The (local, remote) timeouts for `d`, memoized per repo (`timeoutCache`). -/
private def resolveTimeouts (d : Dirs) : IO (Nat × Nat) := do
  let key := repoOf d
  match (← timeoutCache.get).find? (fun e => e.1 == key) with
  | some (_, lo, re) => return (lo, re)
  | none =>
    let (lo, re) ← readTimeoutsUncached d
    timeoutCache.modify (fun c => (key, lo, re) :: c)
    return (lo, re)

/-- Run `git -C <repo> <args>` (optional stdin / extra env). The wall-clock bound
    is the configured local timeout, or the remote one when `remote` is set (the
    network legs). -/
private def git (d : Dirs) (args : List String) (stdin : String := "")
    (env : List (String × Option String) := []) (remote : Bool := false) :
    IO IO.Process.Output := do
  let (lo, re) ← resolveTimeouts d
  let (code, out, err) ← runBounded
    { cmd := "git", args := #["-C", repoOf d] ++ args.toArray, env := env.toArray }
    stdin.toUTF8 (if remote then re else lo)
  return { exitCode := code, stdout := (String.fromUTF8? out).getD "", stderr := err }

/-- A git plumbing failure that isn't an expected condition is `internal`
    (the caller maps "not a repo" / "no remote" to no-upstream itself). -/
private def gitErr (op : String) (o : IO.Process.Output) : Tl.Error :=
  .mk' .internal s!"git {op} failed (exit {o.exitCode}): {o.stderr.trimAscii.toString}"

private def run (d : Dirs) (op : String) (args : List String) (stdin : String := "")
    (env : List (String × Option String) := []) (remote : Bool := false) : TlM String := do
  let o ← (git d args stdin env remote : IO _)
  if o.exitCode == 0 then return o.stdout.trimAscii.toString
  else throw (gitErr op o)

/-- Run git with raw-`ByteArray` stdin and stdout — the byte-faithful path for
    `hash-object`/`cat-file` (a segment line may carry arbitrary bytes; the union
    is a *byte*-level line set, ADR-0001 §5). Bounded by `timeoutMs` (default the
    local bound) like the text `git`, via the shared `runBounded`. -/
private def gitBytes (d : Dirs) (args : List String) (stdin : ByteArray := .empty) :
    IO (UInt32 × ByteArray × String) := do
  let (lo, _) ← resolveTimeouts d
  runBounded { cmd := "git", args := #["-C", repoOf d] ++ args.toArray } stdin lo

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

/-- The segments stored at `ref` (empty when the ref is unset). Reads the
    commit's tree: one `<replica-id>.jsonl` blob per replica. -/
def readRefAt (d : Dirs) (ref : String) : TlM (List SegmentData) := do
  let o ← (git d ["rev-parse", "--verify", "--quiet", ref] : IO _)
  if o.exitCode != 0 then return []
  let listing ← run d "ls-tree" ["ls-tree", ref]
  let entries := listing.splitOn "\n" |>.filter (· ≠ "")
  entries.filterMapM fun line => do
    -- "<mode> <type> <oid>\t<name>"
    match line.splitOn "\t" with
    | [info, name] =>
      if name.endsWith ".jsonl" then
        let rid := (name.dropEnd 6).toString
        -- drop a non-canonical ref-borne name before it is materialized: locally
        -- produced names are always valid, so this filters only junk/crafted tree
        -- entries (mirroring `enumerateSegments`' on-disk check), stopping them
        -- propagating through unions into a permanently-flagged on-disk file.
        if !(Tl.Clock.Replica.mk rid).valid then return none
        match info.splitOn " " with
        | [_, "blob", oid] =>
          -- the blob is the raw segment bytes (may be non-UTF-8) — read them
          -- byte-faithfully, never through a String stdout
          let bytes ← runBytes d "cat-file" ["cat-file", "blob", oid]
          return some { replicaId := rid, bytes }
        | _ => return none
      else return none
    | _ => return none

/-- The segments stored in the local `refs/tl/log`. -/
def readRef (d : Dirs) : TlM (List SegmentData) := readRefAt d "refs/tl/log"

/-- Build a `refs/tl/log` commit (blob per segment, one tree, a commit under
    the neutral identity with `parents`) without moving any ref — the caller
    does the `update-ref` / `push`. Multiple parents let the remote leg make
    the merge commit descend from both the local and the fetched-remote tip, so
    the push fast-forwards (ADR-0001 §5). Returns the commit oid. -/
private def buildCommit (d : Dirs) (segs : List SegmentData) (parents : List String) :
    TlM String := do
  -- a blob per segment (raw bytes via stdin — never String.fromUTF8!, which
  -- panics on a non-UTF-8 segment line; the oid out is plain ASCII hex)
  let entries ← segs.mapM fun s => do
    let oidRaw ← runBytes d "hash-object" ["hash-object", "-w", "--stdin"] s.bytes
    let oid := ((String.fromUTF8? oidRaw).getD "").trimAscii.toString
    pure s!"100644 blob {oid}\t{s.replicaId}.jsonl"
  let tree ← run d "mktree" ["mktree"] (stdin := String.intercalate "\n" entries)
  let commitArgs := ["commit-tree", tree, "-m", "tl log"]
    ++ parents.flatMap (fun p => ["-p", p])
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
  let commit ← buildCommit d segs expectedTip.toList
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
  let commit ← buildCommit d segs expectedTip.toList
  let o ← (git d (casArgs commit expectedTip) : IO _)
  if o.exitCode == 0 then return some commit
  -- a timeout (exit 124) is a hung git, not a CAS race — surface it as the
  -- timeout it is rather than re-reading the tip and retrying as a lost race
  else if o.exitCode == 124 then throw (gitErr "update-ref" o)
  else if (← refTip d) != expectedTip then return none  -- a sibling moved it: retry
  else throw (gitErr "update-ref" o)

/-! ## Remote transport primitives (ADR-0001 §5) — used by `Tl.Sync.Remote` -/

/-- A `git config --get <key>` value, or `none` if unset. -/
def gitConfig (d : Dirs) (key : String) : TlM (Option String) := do
  let o ← (git d ["config", "--get", key] : IO _)
  if o.exitCode == 0 then return some o.stdout.trimAscii.toString else return none

/-- Set a local `git config <key> <value>`; returns whether it took. -/
def gitConfigSet (d : Dirs) (key value : String) : TlM Bool := do
  let o ← (git d ["config", key, value] : IO _)
  return o.exitCode == 0

/-- The git runtime floor (ADR-0006): `tl` shells out to git plumbing for the
    `refs/tl/log` transport and discovery, and requires git ≥ 2.17. -/
def gitFloor : Nat × Nat := (2, 17)

/-- Parse `git --version` output to `(major, minor)`. Scans every line for the
    `git version ` marker (so a prepended banner/warning line on stdout does not
    defeat it), tolerant of a build suffix (`git version 2.39.3 (Apple Git-145)`,
    `git version 2.45.2.windows.1`). `none` when no line carries the marker or its
    two leading components are not numeric. -/
def parseGitVersion (raw : String) : Option (Nat × Nat) := do
  let line ← (raw.splitOn "\n").find? (fun l => (l.splitOn "git version ").length ≥ 2)
  let rest ← (line.splitOn "git version ")[1]?
  let ver := (rest.trimAscii.toString.splitOn " ").head?.getD ""
  match ver.splitOn "." with
  | major :: minor :: _ =>
    match major.toNat?, minor.toNat? with
    | some mj, some mn => some (mj, mn)
    | _, _ => none
  | _ => none

/-- `v ≥ gitFloor` (major, then minor). -/
def gitMeetsFloor (v : Nat × Nat) : Bool :=
  gitFloor.1 < v.1 || (gitFloor.1 == v.1 && gitFloor.2 ≤ v.2)

/-- Run `git --version` (bounded) → `(major, minor)`, or `none` when git is absent
    on PATH or its output is unparseable. Needs no repo, so it takes no `Dirs`. -/
def gitVersion (timeoutMs : Nat := localGitTimeoutMs) : IO (Option (Nat × Nat)) := do
  match ← (runBounded { cmd := "git", args := #["--version"] } .empty timeoutMs).toBaseIO with
  | .ok (0, out, _) => return (String.fromUTF8? out).bind parseGitVersion
  | _ => return none

/-- True when `d` is inside a *linked* git worktree — its `--git-dir` differs
    from the shared `--git-common-dir`. This is exactly where auto-sync's local
    leg is free and cross-worktree sharing is the point (ADR-0016 §4); false in
    the main worktree or outside a repo. -/
def isLinkedWorktree (d : Dirs) : TlM Bool := do
  let gd ← (git d ["rev-parse", "--git-dir"] : IO _)
  let gcd ← (git d ["rev-parse", "--git-common-dir"] : IO _)
  if gd.exitCode != 0 || gcd.exitCode != 0 then return false
  return gd.stdout.trimAscii.toString != gcd.stdout.trimAscii.toString

/-- The current branch (`none` on a detached HEAD). -/
def currentBranch (d : Dirs) : TlM (Option String) := do
  let o ← (git d ["symbolic-ref", "--short", "-q", "HEAD"] : IO _)
  if o.exitCode == 0 then return some o.stdout.trimAscii.toString else return none

/-- Does the named remote exist (has a configured URL)? -/
def remoteExists (d : Dirs) (remote : String) : TlM Bool :=
  return (← gitConfig d s!"remote.{remote}.url").isSome

/-- Fetch the remote's `refs/tl/log` and return its tip + segments — `(none, [])`
    when the remote has no `refs/tl/log` yet (a fresh remote). A genuine
    transport failure (unreachable / auth) throws. The fetched tip is read from
    the per-worktree `FETCH_HEAD` (no shared scratch ref, so concurrent remote
    legs in sibling worktrees of one repo don't collide). -/
def fetchRemoteLog (d : Dirs) (remote : String) : TlM (Option String × List SegmentData) := do
  -- ls-remote first: empty ⇒ the remote has no tl log (nothing to fetch)
  let ls ← run d "ls-remote" ["ls-remote", remote, "refs/tl/log"] (remote := true)
  if ls.trimAscii.isEmpty then return (none, [])
  let _ ← run d "fetch" ["fetch", remote, "refs/tl/log"] (remote := true)  -- records FETCH_HEAD
  let o ← (git d ["rev-parse", "--verify", "--quiet", "FETCH_HEAD"] : IO _)
  if o.exitCode != 0 then return (none, [])
  return (some o.stdout.trimAscii.toString, ← readRefAt d "FETCH_HEAD")

/-- Build the merge commit (tree = `segs`, parents = `parents`) and compare-and-set
    the local `refs/tl/log` to it against `expectedLocalTip`. Returns the oid, or
    `none` if a concurrent local writer moved the ref (the caller retries — like
    `writeRefCas`, distinguished from a real failure by re-reading the tip). -/
def writeRefMergeCas (d : Dirs) (segs : List SegmentData) (parents : List String)
    (expectedLocalTip : Option String) : TlM (Option String) := do
  let commit ← buildCommit d segs parents
  let o ← (git d (casArgs commit expectedLocalTip) : IO _)
  if o.exitCode == 0 then return some commit
  else if o.exitCode == 124 then throw (gitErr "update-ref" o)  -- timeout, not a race
  else if (← refTip d) != expectedLocalTip then return none  -- local race: retry
  else throw (gitErr "update-ref" o)

/-- Push `commit` to the remote's `refs/tl/log`. Returns `true` on success,
    `false` only on a genuine non-fast-forward race (the caller re-fetches and
    retries — ADR-0001 §5). Classification uses `--porcelain`'s machine-readable
    status (`(non-fast-forward)` / `(fetch first)`), not a loose stderr scan: a
    hook/policy decline, a permission denial, or a transport failure is a real
    error thrown with its reason — never retried into a misleading push-rejected.
    Pushing the explicit oid (`<commit>:refs/tl/log`) rather than the ref name
    sends exactly what was just written, immune to a concurrent local move. -/
def pushRefLog (d : Dirs) (remote : String) (commit : String) : TlM Bool := do
  let o ← (git d ["push", "--porcelain", remote, s!"{commit}:refs/tl/log"]
            (remote := true) : IO _)
  if o.exitCode == 0 then return true
  -- --porcelain writes per-ref status to stdout; only these two reasons are the
  -- retryable race (a hook decline reads "(... hook declined)", an auth/transport
  -- failure has no porcelain status line at all)
  let status := o.stdout
  if (status.splitOn "non-fast-forward").length > 1 || (status.splitOn "fetch first").length > 1 then
    return false
  else throw (.mk' .internal
    s!"git push to '{remote}' failed (exit {o.exitCode}): {(status ++ o.stderr).trimAscii.toString}")

end Tl.Sync
