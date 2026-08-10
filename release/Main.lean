/-
The `tlrelease` entry point, and nothing else.

Kept to three lines on purpose, the same way `Verify/Launcher.lean` is: a root
that defines `main` cannot be imported by a test module that also reaches
`Tests/Main.lean`, because two top-level `main` declarations collide. Every
decision therefore lives in `release/Cli.lean` and the modules it imports,
where the tests can drive it in-process — including the branches a release step
would hit at the worst moment, which spawning a binary tests less directly and
covers less completely.
-/
import release.Cli

def main (args : List String) : IO UInt32 := Release.dispatch args
