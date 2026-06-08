/-
`tl` executable entry point (I/O shell, tested — ADR-0004).

Stage 0 ships `tl init` and `tl version` (vision §Staged implementation); the
work-loop verbs (`create`, `ready`, `claim`, …) land in `Tl.Cli` as they are
built. Importing only `Tl.Cli.Init` keeps this Stage-0 binary Mathlib-free; the
kernel (and its Mathlib-backed proofs) join the build with the work-loop verbs.
-/
import Tl.Cli.Init

def usage : String :=
  "tl — a dependency-aware task tracker for agents\n\n" ++
  "usage:\n" ++
  "  tl init       create the gitignored .tl/, mint the replica-id, seed the clock\n" ++
  "  tl version    print the product version\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["init"] => Tl.Cli.init
  | ["version"] => do IO.println "tl 0.1.0"; return 0
  | ["help"] | ["--help"] | [] => do IO.print usage; return 0
  | _ => do
    IO.eprintln s!"tl: unknown command {args}\n"
    IO.eprint usage
    return 2
