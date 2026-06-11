/-
`tl` executable entry point (I/O shell, tested — ADR-0004). All real work —
dispatch, parsing, streams, exit codes — lives in `Tl.Cli.Main` so the test
suite drives the same code path the binary runs.
-/
import Tl.Cli.Main

def main (args : List String) : IO UInt32 :=
  Tl.Cli.run args
