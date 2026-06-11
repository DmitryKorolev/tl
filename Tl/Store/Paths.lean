/-
`Tl.Store.Paths` — the `.tl/` layout and discovery (ADR-0001 §3, ADR-0012).

`Dirs` splits every state path into `(base, rel)` for the shim's two-part
open (ADR-0015 §6): the base — the project root, or the override's parent —
is opened with normal symlink semantics, while the `.tl` components are
walked no-follow. Discovery is the ADR-0012 walk-up: from the cwd to the
nearest ancestor with `.tl/`, stopped at the enclosing repo's root (`.git`
directory OR file — a linked worktree/submodule is its own boundary) and at
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
def relLog (d : Dirs) : String := d.tlRel ++ "/log"
def relSegment (d : Dirs) (replicaId : String) : String :=
  d.tlRel ++ "/log/" ++ replicaId ++ ".jsonl"

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
  -- the shim's component walk enforces no-follow AND ownership on every
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

/-- Does `dir` contain a git boundary marker (`.git` directory OR file —
    a linked worktree/submodule gitfile bounds discovery too, ADR-0012)? -/
def hasGitBoundary (dir : FilePath) : IO Bool := do
  (dir / ".git").pathExists

private def hasTl (dir : FilePath) : IO Bool := do
  let p := dir / ".tl"
  pure ((← p.pathExists) && (← p.isDir))

/-- ADR-0012 discovery. `override` is `--dir` (wins) or `TL_DIR`; otherwise
    walk up from `cwd` to the nearest `.tl/`, stopping at the repo boundary
    and at any `GIT_CEILING_DIRECTORIES` entry (a listed directory is not
    searched). The result is validated (`validate`). -/
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
      let ceilings ← liftSys (fun e => .mk' .internal s!"environment read failed: {e}")
        (IO.getEnv "GIT_CEILING_DIRECTORIES")
      -- canonicalize each ceiling entry like git does (realpath), so a
      -- logical/symlinked entry still matches the canonical walk dirs
      -- (`IO.currentDir` is already canonical, and `.parent` keeps it so);
      -- an entry that does not resolve falls back to its trailing-slash-
      -- trimmed text.
      let rawCeilings := (ceilings.getD "").splitOn ":" |>.filter (· ≠ "")
      let ceilingList ← rawCeilings.mapM fun (c : String) => do
        match ← (IO.FS.realPath (FilePath.mk c)).toBaseIO with
        | .ok p => pure p.toString
        | .error _ =>
          pure (let t := String.ofList (c.toList.reverse.dropWhile (· == '/') |>.reverse)
                if t.isEmpty then c else t)
      let rec walk (dir : FilePath) (fuel : Nat) : TlM Dirs := do
        match fuel with
        | 0 => throw (noProject "here (search depth exhausted)")
        | fuel + 1 =>
          if ceilingList.contains dir.toString then
            throw (noProject s!"here (GIT_CEILING_DIRECTORIES stops the search at {dir})")
          if ← liftSys (fun e => .mk' .internal s!"{e}") (hasTl dir) then
            validate { base := dir.toString, tlRel := ".tl" }
          else if ← liftSys (fun e => .mk' .internal s!"{e}") (hasGitBoundary dir) then
            -- the repo root is searched, never ascended past (ADR-0012)
            throw (noProject s!"in this repository (searched up to its root {dir})")
          else
            match dir.parent with
            | some parent =>
              if parent == dir then throw (noProject "here")
              else walk parent fuel
            | none => throw (noProject "here")
      walk cwd 256

end Tl.Store
