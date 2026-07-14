/-
`Tl.Store.Paths` — the `.tl/` layout and discovery (ADR-0001 §3, ADR-0012).

`Dirs` splits every state path into `(base, rel)` for the shim's two-part
open (ADR-0015 §6): the base — the project root, or the override's parent —
is opened with normal symlink semantics, while the `.tl` components are
walked no-follow. Discovery is the ADR-0012 walk-up: from the cwd to the
nearest ancestor with `.tl/`, stopped at the enclosing repo's root (`.git`
directory or file — a linked worktree/submodule is its own boundary) and at
`GIT_CEILING_DIRECTORIES`; `--dir`/`TL_DIR` skips discovery and names the
state directory itself. No command auto-inits: a missing/uninitialized state
directory is `no-project`.

The shell's failure channel is `TlM` (`ExceptT Tl.Error IO`): shim
`IO.Error`s are caught at this boundary and mapped to their structured codes
(`ELOOP`/`ENOTDIR` on a `.tl` component → `unsafe-path`, ADR-0014 T4).
-/
import Tl.Error
import Tl.Store.Sys

namespace Tl.Store

open System (FilePath)

/-- The shell's failure monad: structured `Tl.Error` over `IO`. -/
abbrev TlM := ExceptT Tl.Error IO

/-- Located state: every open composes `base` (normal symlink semantics)
    with a `rel` whose components are walked no-follow. -/
structure Dirs where
  /-- The directory the `.tl` components hang under (project root, or the
      override path's parent). Empty = the process's current directory. -/
  base : String
  /-- The state directory's path relative to `base` (`".tl"`, or the
      override's final component). -/
  tlRel : String
deriving Repr, Inhabited

namespace Dirs

/-- The state directory itself (for display/errors). -/
def tlPath (d : Dirs) : String :=
  if d.base.isEmpty then d.tlRel else d.base ++ "/" ++ d.tlRel

def relLocal (d : Dirs) : String := d.tlRel ++ "/local"
def relReplica (d : Dirs) : String := d.tlRel ++ "/local/replica"
def relClock (d : Dirs) : String := d.tlRel ++ "/local/clock"
def relLock (d : Dirs) : String := d.tlRel ++ "/local/lock"
/-- The read-time refresh marker (ADR-0016 §3): the `refs/tl/log` OID whose
    foreign segments are already materialized into `log/`. Gitignored, local-
    only, not part of the log format (no `v` bump) — a stale or absent value
    only forces a re-materialize, never a wrong read. -/
def relRefMark (d : Dirs) : String := d.tlRel ++ "/local/ref-mark"
/-- The auto-sync publish marker: the `refs/tl/log` OID this replica's own
    segment is published into, plus that segment's byte length and content hash
    at publish time. The local-sync leg fast-outs (skipping the whole-log union)
    when the ref still sits at this OID and the own segment is byte-identical —
    nothing to publish, nothing new to absorb. Local-only, gitignored, no log
    format impact: a stale/absent value only forces the full reconcile, never a
    wrong publish (it is written only after the own segment is in the tip). -/
def relSyncPub (d : Dirs) : String := d.tlRel ++ "/local/sync-pub"
/-- The last-sync marker `<ms> <tip>`: wall-clock time of the last `tl sync`
    (local epoch ms) and the `refs/tl/log` tip it left. Read by `doctor`'s sync
    posture and `ready`'s staleness advisory; written only by a sync. Local-only,
    gitignored, no log format impact — absent ⇒ "never synced", a safe default. -/
def relLastSync (d : Dirs) : String := d.tlRel ++ "/local/last-sync"
/-- The materialization fold cache (ADR-0022): the folded state keyed to
    per-segment log content. Local-only, never synced, no log format impact —
    absent/stale/corrupt only costs a rebuild from the segments, never a wrong
    read. It stays out of git via the single `*` self-ignore `init` writes to
    `.tl/.gitignore` (the whole `.tl/local/` subtree is covered) — that file is
    the only thing keeping the cache untracked. -/
def relCache (d : Dirs) : String := d.tlRel ++ "/local/cache"
/-- The stealth marker (ADR-0001 §7): present iff `tl init --stealth` created
    this state. While present, sharing is disabled — `tl sync` fails closed with
    `stealth-mode` and auto-sync never publishes — so the replica stays local-only
    with zero repo-visible trace. Gitignored, local-only, no log-format impact;
    removing it (then `tl sync`) is the whole of un-stealthing. -/
def relStealth (d : Dirs) : String := d.tlRel ++ "/local/stealth"
def relLog (d : Dirs) : String := d.tlRel ++ "/log"
def relSegment (d : Dirs) (replicaId : String) : String :=
  d.tlRel ++ "/log/" ++ replicaId ++ ".jsonl"

/-- The stealth marker's path *as the user must type it* — the real location,
    not the default-layout guess: under `--dir /custom/state` the marker is
    `/custom/state/local/stealth`, and an error that said `.tl/local/stealth`
    would teach a path that does not exist (ADR-0001 §7 / ADR-0012). -/
def stealthDisplayPath (d : Dirs) : String := d.tlPath ++ "/local/stealth"

/-- The generated primer's path, likewise resolved rather than assumed. -/
def readmeDisplayPath (d : Dirs) : String := d.tlPath ++ "/README.md"

/-- The log directory as an ordinary path (for `createDirAll`/`readDir`;
    every *open* under it still goes through the no-follow walk). -/
def logPath (d : Dirs) : FilePath := FilePath.mk (d.tlPath) / "log"

/-- The absolute path of a `.tl`-relative file (base empty = cwd) — for the
    atomic-replace `rename` (ADR-0015 §3), whose components above the final
    name are not the shim's concern (the temp open already rode no-follow). -/
def absOf (d : Dirs) (rel : String) : FilePath :=
  if d.base.isEmpty then FilePath.mk rel else FilePath.mk d.base / rel

end Dirs

/-- Map a shim failure on a `.tl` open to its structured code: a refused
    symlink (`ELOOP`, or `ENOTDIR` from an unfollowed link mid-walk) is the
    ADR-0015 §6 / T4 `unsafe-path` refusal; anything else is `internal`
    (the caller maps expected conditions — `ENOENT`, `EEXIST` — before this). -/
def mapSysError (rel : String) (e : IO.Error) : Tl.Error :=
  match Sys.errnoOf e with
  | some "ELOOP" =>
    { code := .unsafePath
      message := s!"refusing {rel}: a path component is a symlink — remove the link (or move the project) and retry; tl never follows links under .tl"
      context := [("path", .str rel), ("reason", .str "symlink")] }
  | some "ENOTDIR" =>
    { code := .unsafePath
      message := s!"refusing {rel}: a path component is not a real directory (a symlink is not followed under .tl) — repair the .tl layout and retry"
      context := [("path", .str rel), ("reason", .str "symlink")] }
  | some "ENOTOWNED" =>
    { code := .unsafePath
      message := s!"refusing {rel}: a path component is not owned by you — chown the .tl tree (or point --dir at your own state)"
      context := [("path", .str rel), ("reason", .str "ownership")] }
  | _ => .mk' .internal s!"unexpected I/O failure on {rel}: {e}"

/-- Run a shim action, mapping `IO.Error`s to structured errors via `f`. -/
def liftSys (f : IO.Error → Tl.Error) (act : IO α) : TlM α := do
  match ← act.toBaseIO with
  | .ok a => return a
  | .error e => throw (f e)

/-- The standard `no-project` error (ADR-0012: never auto-init). -/
def noProject (where_ : String) : Tl.Error :=
  .mk' .noProject s!"no tl project {where_}; run `tl init` at the project root (or pass --dir at an initialized state directory)"

/-- Validate a located state directory: the `.tl` component must be a real,
    caller-owned directory (no-follow + ownership, ADR-0015 §6) and look
    initialized (`local/` exists — an empty directory is `no-project`,
    ADR-0012). Returns the validated `Dirs`. -/
def validate (d : Dirs) : TlM Dirs := do
  -- the shim's component walk enforces no-follow and ownership on every
  -- open (ADR-0015 §6), so validation is just the opens themselves
  let fd ← liftSys (fun e =>
      match Sys.errnoOf e with
      | some "ENOENT" => noProject s!"at {d.tlPath}"
      | _ => mapSysError d.tlRel e)
    (Sys.openNoFollow d.base d.tlRel Sys.flagDirectory)
  liftSys (mapSysError d.tlRel) (Sys.close fd)
  -- initialized ⇔ local/ exists (init always creates it; an empty dir is not a project)
  let localFd ← liftSys (fun e =>
      match Sys.errnoOf e with
      | some "ENOENT" => noProject s!"at {d.tlPath} (no local/ — not an initialized state directory)"
      | _ => mapSysError d.relLocal e)
    (Sys.openNoFollow d.base d.relLocal Sys.flagDirectory)
  liftSys (mapSysError d.relLocal) (Sys.close localFd)
  return d

/-- Split an explicit state-directory path (the `--dir`/`TL_DIR` override, or
    `init`'s target) into the `(base, rel)` shape: the final component is the
    no-follow `rel`, everything above it the symlink-permitted base. -/
def Dirs.ofStatePath (path : String) : Dirs :=
  -- strip trailing separators first: "/a/b/.tl/" must split like "/a/b/.tl"
  -- (FilePath.fileName is none on a trailing slash, and the fallback would
  -- treat the absolute path as cwd-relative in the shim walk)
  let trimmed := String.ofList (path.toList.reverse.dropWhile (· == '/') |>.reverse)
  let path := if trimmed.isEmpty then path else trimmed
  match (FilePath.mk path).parent, (FilePath.mk path).fileName with
  | some parent, some name =>
    if parent.toString.isEmpty then { base := "", tlRel := name }
    else { base := parent.toString, tlRel := name }
  | _, _ => { base := "", tlRel := path }

/-- Does `dir` contain a git boundary marker (`.git` directory or file —
    a linked worktree/submodule gitfile bounds discovery too, ADR-0012)? -/
def hasGitBoundary (dir : FilePath) : IO Bool := do
  (dir / ".git").pathExists

/-- Does `dir` hold an entry named `name` — a regular file, a symlink (even a
    dangling one), anything but absent? Probed with the no-follow shim
    (`openNoFollow … flagDirectory`), never `readDir`: a usable but
    unlistable gitdir (mode `0711` — git can traverse it, `readDir` gets
    `EACCES`) must not read as "no HEAD" and let discovery climb out.
    `flagDirectory` also keeps the probe from blocking on a FIFO/device-shaped
    entry. The classification is one-sided toward "present" (a boundary
    over-stop is safe; a false absence is the cross-repository climb-out):
    `ENOENT` alone means absent; success (a `HEAD` directory), `ENOTDIR` (a
    regular file), `ELOOP` (a symlink, dangling included), and every other
    error (`EACCES`, `ENOTOWNED`, …) all mean present. -/
private def hasEntry (dir : FilePath) (name : String) : IO Bool := do
  match ← (Sys.withFd dir.toString name Sys.flagDirectory (fun _ => pure ())).toBaseIO with
  | .ok _ => return true
  | .error e => return Sys.errnoOf e != some "ENOENT"

/-- Is `dir` itself a git repository directory — a bare repository, or the
    inside of a `.git` dir? Recognized *structurally* — `objects/` is a
    directory, `refs/` is present, and a `HEAD` entry exists — deliberately
    **not** by re-validating `HEAD`'s content the way git's setup check does.
    Matching git's byte-level `HEAD` rules in hand-written code proved to be a
    reliable source of *under*-detection (uppercase hex, a symlink `HEAD`
    dangling after `pack-refs --prune` or on an unborn branch, `ref:` without a
    space, a hash with trailing text, an oversized `HEAD`, `refs` as an
    executable file) — and every miss is a real bare repo that git operates in
    while `tl` climbs *out* of it and binds, and writes to, an unrelated
    enclosing `.tl/` (the exact cross-repository hazard ADR-0012 forbids, in
    both the read and write directions). The structural test is at least as
    inclusive as git on each component, so `tl` never climbs out of a directory
    git treats as a gitdir. Its only cost is the safe direction: a committed
    fixture directory that happens to have `objects/`, `refs/`, and a `HEAD`
    also bounds the walk — a `no-project`, never a wrong bind; `--dir` is the
    override. (A linked worktree's private gitdir has `HEAD` but no `objects/`
    directory, so it does not match; its boundary is the `.git` file at the
    worktree root.)

    Each component is checked at-least-as-inclusively as git: `objects/` a
    directory; `refs/` merely *present* (git accepts an executable file there,
    not only a directory); `HEAD` present in any form via the no-follow shim
    (see `hasEntry` — works on an unlistable `0711` gitdir where `readDir`
    would not). -/
def isGitDirLayout (dir : FilePath) : IO Bool := do
  return (← (dir / "objects").isDir)
    && (← (dir / "refs").pathExists)
    && (← hasEntry dir "HEAD")

private def hasTl (dir : FilePath) : IO Bool := do
  let p := dir / ".tl"
  pure ((← p.pathExists) && (← p.isDir))

/-- The `GIT_CEILING_DIRECTORIES` entries, canonicalized like git does
    (realpath), so a logical/symlinked entry still matches the canonical walk
    dirs (`IO.currentDir` is already canonical, and `.parent` keeps it so);
    an entry that does not resolve falls back to its trailing-slash-trimmed
    text. Shared by `discover` and init/import placement — every filesystem
    walk honors the same ceilings, and like git applies them to *proper
    ancestors* only: the starting directory is always examined (ADR-0012). -/
def ceilingDirs : TlM (List String) := do
  let ceilings ← liftSys (fun e => .mk' .internal s!"environment read failed: {e}")
    (IO.getEnv "GIT_CEILING_DIRECTORIES")
  let raw := (ceilings.getD "").splitOn ":" |>.filter (· ≠ "")
  raw.mapM fun (c : String) => do
    match ← (IO.FS.realPath (FilePath.mk c)).toBaseIO with
    | .ok p => pure p.toString
    | .error _ =>
      pure (let t := String.ofList (c.toList.reverse.dropWhile (· == '/') |>.reverse)
            if t.isEmpty then c else t)

/-- ADR-0012 discovery. `override` is `--dir` (wins) or `TL_DIR`; otherwise
    walk up from `cwd` to the nearest `.tl/`, stopping at the repo boundary
    (a `.git` entry, or a bare-gitdir layout), and at any
    `GIT_CEILING_DIRECTORIES` entry among the *proper ancestors* (the
    starting directory is always examined, as in git).
    The result is validated (`validate`). -/
def discover (override : Option String := none) : TlM Dirs := do
  match override with
  | some path => validate (Dirs.ofStatePath path)
  | none =>
    let envDir ← liftSys (fun e => .mk' .internal s!"environment read failed: {e}")
      (IO.getEnv "TL_DIR")
    match envDir with
    | some path => validate (Dirs.ofStatePath path)
    | none =>
      let cwd ← liftSys (fun e => .mk' .internal s!"cannot read the working directory: {e}")
        IO.currentDir
      let ceilingList ← ceilingDirs
      let rec walk (dir : FilePath) (fuel : Nat) (atStart : Bool) : TlM Dirs := do
        match fuel with
        | 0 => throw (noProject "here (search depth exhausted)")
        | fuel + 1 =>
          -- ceilings bound the *ascent* (git semantics): the starting
          -- directory is always examined, a listed ancestor is not entered
          if !atStart && ceilingList.contains dir.toString then
            throw (noProject s!"here (GIT_CEILING_DIRECTORIES stops the search at {dir})")
          if ← liftSys (fun e => .mk' .internal s!"{e}") (hasTl dir) then
            validate { base := dir.toString, tlRel := ".tl" }
          else if ← liftSys (fun e => .mk' .internal s!"{e}") (hasGitBoundary dir) then
            -- the repo root is searched, never ascended past (ADR-0012)
            throw (noProject s!"in this repository (searched up to its root {dir})")
          else if ← liftSys (fun e => .mk' .internal s!"{e}") (isGitDirLayout dir) then
            -- a bare repo (or a .git interior) bounds the walk the same way a
            -- worktree root does: ascending past it could bind an unrelated
            -- enclosing .tl/ (ADR-0012)
            throw (noProject s!"here ({dir} is a git repository directory — bare repositories hold no tl state; run tl in a working tree, or pass --dir at an explicit state directory)")
          else
            match dir.parent with
            | some parent =>
              if parent == dir then throw (noProject "here")
              else walk parent fuel false
            | none => throw (noProject "here")
      walk cwd 256 true

end Tl.Store
