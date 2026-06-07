/-
`tl` executable entry point (I/O shell, tested — ADR-0004).

Stage 0 ships only a minimal `tl init` and `tl version` (vision §Staged
implementation); the full command dispatch lands in `Tl.Cli.Main` as the work
loop is built. This stub keeps the executable target compiling against the
verified library from the first commit.
-/
import Tl

def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] => do
    IO.println "tl 0.1.0"
    return 0
  | _ => do
    IO.eprintln "tl: not yet implemented (Stage 0 scaffold)"
    return 1
