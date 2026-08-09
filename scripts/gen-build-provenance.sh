#!/bin/sh
# Regenerate Tl/Build/Stamp.lean — the build provenance compiled into the
# binary and reported by `tl version` (ADR-0006 "Tool versioning").
#
#   scripts/gen-build-provenance.sh            development stamp: no commit.
#                                              This is the copy checked in.
#   scripts/gen-build-provenance.sh --stamp    stamp the current git HEAD and
#                                              working-tree cleanliness. The
#                                              release workflow runs this on a
#                                              clean checkout of the tag before
#                                              building.
#
# Run from the repository root. The output is a pure function of `lean-toolchain`,
# `lake-manifest.json`, and (under --stamp) the git state, so an independent
# rebuilder reproduces the same file — and therefore the same binary — from the
# same commit.
set -eu

stamp=0
case "${1-}" in
  '') ;;
  --stamp) stamp=1 ;;
  *)
    echo "gen-build-provenance: unknown argument '$1' — pass --stamp or nothing" >&2
    exit 2
    ;;
esac

for required in lean-toolchain lake-manifest.json; do
  if [ ! -f "$required" ]; then
    echo "gen-build-provenance: $required not found — run this from the repository root" >&2
    exit 2
  fi
done

# SHA-256 of a file as lowercase hex. coreutils ships sha256sum; macOS ships
# shasum. Both print "<hex>  <name>", so the first field is the digest.
sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    echo "gen-build-provenance: no sha256sum or shasum on PATH — cannot digest $1" >&2
    exit 2
  fi
}

toolchain=$(tr -d ' \t\r\n' < lean-toolchain)
manifest_digest=$(sha256_of lake-manifest.json)

commit=''
dirty='false'
if [ "$stamp" -eq 1 ]; then
  if ! command -v git >/dev/null 2>&1; then
    echo "gen-build-provenance: --stamp needs git on PATH" >&2
    exit 2
  fi
  if ! commit=$(git rev-parse HEAD 2>/dev/null); then
    echo "gen-build-provenance: --stamp needs a git checkout with a commit at HEAD" >&2
    exit 2
  fi
  # Untracked files count: they can change what gets compiled.
  if [ -n "$(git status --porcelain 2>/dev/null)" ]; then
    dirty='true'
  fi
fi

# Every value lands inside a Lean string literal. These are machine-produced
# (hex digests, a git object id, a toolchain line), so anything outside the
# expected shape means the input is not what this script thinks it is —
# refuse rather than emit a file that will not compile or, worse, will.
check_plain() {
  case "$2" in
    *[!0-9A-Za-z./:_-]* | '')
      echo "gen-build-provenance: refusing to embed $1 value '$2' — expected only [0-9A-Za-z./:_-]" >&2
      exit 2
      ;;
  esac
}
check_plain toolchain "$toolchain"
check_plain manifest-digest "$manifest_digest"
[ -z "$commit" ] || check_plain commit "$commit"

cat > Tl/Build/Stamp.lean <<LEAN
/-
\`Tl.Build.Stamp\` — the build provenance baked into this binary.

GENERATED FILE — do not edit by hand. Regenerate with

    scripts/gen-build-provenance.sh              # development stamp (this copy)
    scripts/gen-build-provenance.sh --stamp      # stamp the current git HEAD

The checked-in copy is deliberately the *development* stamp: \`commit\` is empty,
so a plain \`lake build\` produces a binary that reports itself as an
unidentified local build rather than claiming a source commit it may not match.
The release workflow runs \`--stamp\` on a clean checkout of the tagged commit
before building, which is what puts a real commit here.

\`toolchain\` and \`manifestDigest\` are the pins in effect for *this* checkout and
are the same in the development and stamped copies; \`Tests/ReleaseTests.lean\`
fails when either drifts from \`lean-toolchain\` / \`lake-manifest.json\` on disk.
-/

namespace Tl.Build

/-- The full source commit the binary was built from, or \`""\` when no commit
    was stamped (a development build). -/
def stampCommit : String := "$commit"

/-- Whether the working tree carried uncommitted changes when \`stampCommit\`
    was taken. Meaningless — and always \`false\` — when \`stampCommit\` is \`""\`. -/
def stampDirty : Bool := $dirty

/-- The \`lean-toolchain\` pin the binary was compiled with. -/
def stampToolchain : String := "$toolchain"

/-- The SHA-256 of \`lake-manifest.json\`, lowercase hex: the identity of the
    resolved dependency set (ADR-0009 pins are immutable commits, so this
    digest fixes every dependency revision at once). -/
def stampManifestDigest : String :=
  "$manifest_digest"

end Tl.Build
LEAN

echo "gen-build-provenance: wrote Tl/Build/Stamp.lean (commit='${commit:-<development>}' dirty=$dirty toolchain=$toolchain)"
