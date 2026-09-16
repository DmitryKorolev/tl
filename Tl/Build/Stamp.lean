/-
`Tl.Build.Stamp` — the build provenance baked into this binary.

GENERATED FILE — do not edit by hand. Regenerate with

    tlrelease stamp --root .              # development stamp (this copy)
    tlrelease stamp --root . --commit     # stamp the current git HEAD

The checked-in copy is deliberately the *development* stamp: `commit` is empty,
so a plain `lake build` produces a binary that reports itself as an
unidentified local build rather than claiming a source commit it may not match.
`lake exe tltest` regenerates this file from a copy of the repository's inputs
and compares the committed bytes with the result, so a stamped copy cannot reach
main. The release workflow stamps a clean checkout of the tagged commit before
building, which is what puts a real commit here.

`toolchain` and `manifestDigest` are the pins in effect for *this* checkout and
are the same in the development and stamped copies; `Tests/ReleaseTests.lean`
fails when either drifts from `lean-toolchain` / `lake-manifest.json` on disk.
-/

namespace Tl.Build

/-- The full source commit the binary was built from, or `""` when no commit
    was stamped (a development build). -/
def stampCommit : String := ""

/-- Whether the working tree carried uncommitted changes when `stampCommit`
    was taken. Meaningless — and always `false` — when `stampCommit` is `""`. -/
def stampDirty : Bool := false

/-- The `lean-toolchain` pin the binary was compiled with. -/
def stampToolchain : String := "leanprover/lean4:v4.34.0"

/-- The SHA-256 of `lake-manifest.json`, lowercase hex: the identity of the
    resolved dependency set (ADR-0009 pins are immutable commits, so this
    digest fixes every dependency revision at once). -/
def stampManifestDigest : String :=
  "5f3eea7c7d80b4d835ca0f4445c867c9175f07862c24c79de5c4c75842a180bb"

end Tl.Build
