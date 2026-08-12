/-
`tlrelease` — the release decision layer, as a separately built executable.

Why this exists at all. Three review rounds over the release pipeline produced
63 + 8 + 15 confirmed findings, and nearly every recurring one had a single
shape: POSIX shell discarding a non-zero status, so a check that could not run
reported success. `note $?` after `set -e` had already exited; `fail` inside a
command substitution exiting only the subshell; `status=$(cmd; echo $?)`;
`VAR="$(f)" prog` swallowing the substitution's failure; a nested substitution
where the outer status wins; `$(gh api … || echo '')` turning an error into an
absent value; `sha256sum "$f" | cut -d' ' -f1` returning `cut`'s status. It was
fixed twice and reintroduced four more times *while the author was actively
trying not to*. Shell's default on error is to continue with something
plausible; this pipeline's job is to fail closed. That is a language problem,
not an author problem, and moving the decisions into a language with `Except`
and total functions is the response to it.

What this is not. Being written in Lean does not make it verified. Almost all
of it is tested I/O-shell code (ADR-0004 tiering) that happens to compile in
Lean, and it is **not part of the product TCB**: `release/` imports nothing
from `Tl/`, so release administration cannot reach the shipped binary. Only
small pure verdict functions — the ones whose failure mode is a silent false
negative rather than an odd answer — carry theorems, in the `Verify/Proofs.lean`
style. This tool makes no new proved claim in docs/overview.md and adds no
landmark theorem.

Why `release/` and not `Release/`. The repository already tracks a lowercase
`release/` holding `identity.json`, `targets.json` and `plan.json`. This
checkout's filesystem is case-insensitive, so a sibling `Release/` would *be*
that same directory: the trust verifier's claim list compares paths as strings,
so it would scan the directory it had not claimed and report every module here
as an unclaimed source, while Linux CI saw two directories and disagreed. One
directory for all release administration — its data and the decisions over it —
also matches `scripts/`, whose lowercase claim and `scripts.GenLicenses` module
name are the same trade.

The boundaries that stay native, deliberately: `install.sh` is piped from curl
and has no checkout to read; `Formula/tl.rb` is a Ruby DSL because Homebrew
formulas are; and `scripts/verify-release-artifacts.sh` stays shell because a
precompiled verifier must not become the only way to authenticate the release
that contains it.
-/

import release.Certificate
import release.Identity
import release.Manifest
import release.Metadata
import release.Plan
import release.Sbom

namespace Release

/-- Every subcommand `tlrelease` offers, contributed by the module that owns
    each decision.

    A table rather than a `match`, so `help` is generated from the same list
    dispatch reads: a subcommand that exists but is undocumented, or documented
    but unreachable, is not representable. -/
def commands : List Command :=
  certificateCommands ++ identityCommands ++ manifestCommands ++ metadataCommands ++ planCommands ++ sbomCommands

def usage : String :=
  let header :=
    "tlrelease — release decisions for the tl pipeline\n\n\
     usage: tlrelease <command> [arguments]\n\n"
  let body :=
    if commands.isEmpty then
      "No subcommands are wired yet; they land with the port, one decision at a \
       time. Until then every invocation is a usage error, which is the correct \
       answer: a release step must never read \"did nothing\" as success.\n"
    else
      "commands:\n" ++ String.join (commands.map fun command =>
        s!"  {command.name} {command.arguments}\n      {command.summary}\n")
  header ++ body

/-- Dispatch. Separated from `main` so its branches are reachable from tests
    without spawning a process: the usage and unknown-command paths are exactly
    the ones a release step would hit at the worst moment. -/
def dispatch (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprint usage
      IO.eprintln "tlrelease: no command given. Pass one of the commands above, or --help."
      return 2
  | name :: rest =>
      if name == "--help" || name == "-h" || name == "help" then
        IO.print usage
        return 0
      match commands.find? (·.name == name) with
      | some command => command.run rest
      | none =>
          IO.eprint usage
          IO.eprintln s!"tlrelease: unknown command '{name}'. Pass --help to list the commands this build offers."
          return 2

end Release
