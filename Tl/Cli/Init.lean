/-
`Tl.Cli.Init` — the Stage-0 `tl init` (ADR-0001 §4).

Creates the gitignored `.tl/`, writes the `*` self-ignore (so `tl` never touches
the repo's own `.gitignore`/`.gitattributes`), mints the replica-id, and seeds the
clock. The `refs/tl/log` refspec + auto-sync (Stage 3), the generated
`.tl/README.md` + discovery pointer (Stage 2), and repo-toplevel placement +
`--dir` (Stage 1, with the discovery wiring — ADR-0001 §4; this Stage-0 init is
cwd-relative) are deliberately not here. `init` is
idempotent and does not require a git repo. Tested-shell tier (ADR-0004), but its own
IO test (temp-dir idempotency + replica/clock/gitignore file checks) is **pending** —
to land with the Stage-1 CLI test buildout.
-/
import Tl.Clock.Replica
import Tl.Clock.Hlc

namespace Tl.Cli

open Tl.Clock

/-- Run `tl init` in `dir` (default `.tl`). Idempotent: if it already exists, the
    replica/clock are left untouched (never re-minted — a re-mint would fork
    identity). -/
def init (dir : System.FilePath := ".tl") : IO UInt32 := do
  if ← dir.pathExists then
    IO.println s!"tl: {dir} already initialized — nothing to do (idempotent)"
    return 0
  IO.FS.createDirAll (dir / "local")
  IO.FS.writeFile (dir / ".gitignore") "*\n"
  let replica ← Replica.mint
  IO.FS.writeFile (dir / "local" / "replica") (replica.id ++ "\n")
  IO.FS.writeFile (dir / "local" / "clock") (Hlc.zero.toHex ++ "\n")
  IO.println s!"Initialized tl in {dir}/ (replica {replica.id})"
  return 0

end Tl.Cli
