/-
`Tl.Build.Provenance` — what the stamped build provenance *means*, kept apart
from the generated `Tl.Build.Stamp` constants so it can be read and tested as
ordinary code (`Stamp.lean` is machine-written; nothing but data belongs there).

`tl version --json` reports this (ADR-0006 "Tool versioning"; the additive
`build` field ADR-0020 left room for). It answers one question for whoever
holds a binary: *which source does this correspond to?*

Deliberately **not** answered here: whether the binary is an official release.
A binary cannot attest that about itself — anyone can stamp a commit and build.
The release claim is carried by the Sigstore certificate identity pinned in
`release/identity.json`, verified per `VERIFYING.md`. So the strongest thing
`Kind` says is `clean`: this binary corresponds exactly to a named commit.

Tested I/O shell (ADR-0004): pure, total, and covered branch-by-branch in
`Tests/ReleaseTests.lean`.
-/
import Tl.Build.Stamp

namespace Tl.Build

/-- How much the binary can say about its own source. -/
inductive Kind where
  /-- No commit was stamped: a local `lake build` of an unidentified tree. -/
  | development
  /-- A commit was stamped, but the tree had uncommitted changes on top of it,
      so the binary does *not* correspond to that commit. -/
  | dirty
  /-- Stamped from a clean checkout: the binary corresponds to that commit. -/
  | clean
  deriving DecidableEq, Repr

/-- The stable wire spelling (`--json`) and human word for a kind. -/
def Kind.name : Kind → String
  | .development => "development"
  | .dirty => "dirty"
  | .clean => "clean"

/-- The build provenance of a binary. A record rather than four loose
    constants so the derivation and both renderings are total functions of it,
    testable at every kind without rebuilding. -/
structure Provenance where
  /-- The stamped source commit, or `""` for a development build. -/
  commit : String
  /-- Whether the stamped tree carried uncommitted changes. -/
  dirty : Bool
  /-- The `lean-toolchain` pin the binary was compiled with. -/
  toolchain : String
  /-- SHA-256 of `lake-manifest.json`: the resolved dependency set. -/
  manifestDigest : String
  deriving DecidableEq, Repr

/-- What this binary was built from. -/
def current : Provenance :=
  { commit := stampCommit, dirty := stampDirty,
    toolchain := stampToolchain, manifestDigest := stampManifestDigest }

/-- An empty commit is the development stamp; `dirty` only discriminates once
    there is a commit to be dirty *relative to*, which is why a development
    build never reports `dirty` however messy the tree that produced it was. -/
def Provenance.kind (p : Provenance) : Kind :=
  if p.commit.isEmpty then .development
  else if p.dirty then .dirty
  else .clean

/-- The short commit form for human output — the leading 12 hex characters,
    matching what `git log --abbrev-commit` shows at this repository's size.
    `""` for a development build, whose human line names no commit at all. -/
def Provenance.shortCommit (p : Provenance) : String :=
  (p.commit.take 12).toString

end Tl.Build
