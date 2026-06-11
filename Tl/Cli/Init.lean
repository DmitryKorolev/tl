/-
`Tl.Cli.Init` — `tl init` (ADR-0001 §4).

Creates the gitignored `.tl/`, writes the `*` self-ignore (so `tl` never
touches the repo's own `.gitignore`/`.gitattributes`), mints the replica-id
from OS-CSPRNG entropy (ADR-0019, via the Store), and seeds the clock.
Idempotent: an existing state directory is left untouched (a re-mint would
fork identity). The `refs/tl/log` refspec + auto-sync (Stage 3) and the
generated `.tl/README.md` + discovery pointer (Stage 2) are deliberately not
here; repo-toplevel placement and `--dir`/`--json` live in the command layer
(`Tl/Cli/Commands.lean`'s `cmdInit`), which calls `initAt`.
-/
import Tl.Store.Local

namespace Tl.Cli

open Tl.Store

/-- Initialize the state directory at `path`. Returns the minted replica,
    or `none` if it was already initialized. Idempotence keys on the
    replica file, not bare existence: an interrupted or hand-made empty
    `.tl` is *completed*, never reported as already-done (only an existing
    replica id must never be re-minted — that would fork identity). -/
def initAt (path : System.FilePath) : TlM (Option Tl.Clock.Replica) := do
  let exists_ ← liftSys (fun e => .mk' .internal s!"{e}") path.pathExists
  if exists_ then
    unless ← liftSys (fun e => .mk' .internal s!"{e}") path.isDir do
      throw (.mk' .usage
        s!"a file named {path} is in the way — remove or rename it, then rerun `tl init`")
  let dirs := Dirs.ofStatePath path.toString
  let already ← if exists_ then
      (do pure (← loadReplica dirs).isSome)
    else pure false
  if already then
    return none
  liftSys (fun e => .mk' .internal s!"cannot create {path}: {e}") do
    IO.FS.createDirAll (path / "local")
    IO.FS.writeFile (path / ".gitignore") "*\n"
  let replica ← mintReplica dirs
  persistClock dirs Tl.Clock.Hlc.zero
  return some replica

/-- The bare `tl init` entry (cwd-relative; the dispatch layer adds toplevel
    placement and `--json`). -/
def init (dir : System.FilePath := ".tl") : IO UInt32 := do
  match ← (initAt dir).run with
  | .ok none =>
    IO.println s!"tl: {dir} already initialized — nothing to do (idempotent)"
    return 0
  | .ok (some replica) =>
    IO.println s!"Initialized tl in {dir}/ (replica {replica.id})"
    return 0
  | .error e =>
    IO.eprintln s!"tl: {e.message}"
    return e.code.exitCode

end Tl.Cli
