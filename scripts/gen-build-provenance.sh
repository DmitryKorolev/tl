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
#   scripts/gen-build-provenance.sh --selftest prove the refusal paths still
#                                              fire, in throwaway directories.
#                                              Writes nothing to this checkout.
#
# Run from the repository root. The output is a pure function of
# `lean-toolchain`, `lake-manifest.json`, and (under --stamp) the git state, so
# an independent rebuilder gets the same *stamp* from the same commit. That is
# a claim about this file alone: whether the compiled binary comes out
# bit-identical depends on the Lean and system toolchains, which this script
# does not touch and the project does not yet check — ADR-0006 "Release
# integrity and provenance" carries reproducible builds as an open item.
#
# Everything here fails closed. A stamp saying `clean` is read as "this binary
# corresponds exactly to that commit", so a step that cannot establish what it
# is asserting refuses instead of assuming the favorable answer.
set -eu

self=$0
stamp=0
selftest=0
case "${1-}" in
  '') ;;
  --stamp) stamp=1 ;;
  --selftest) selftest=1 ;;
  *)
    echo "gen-build-provenance: unknown argument '$1' — pass --stamp, --selftest, or nothing" >&2
    exit 2
    ;;
esac

# The generated file, relative to the repository root. Named once: the
# dirtiness probe has to exclude exactly the path the writer writes.
output='Tl/Build/Stamp.lean'

# ---------------------------------------------------------------------------
# Selftest: a gate that quietly stopped refusing would pass forever, so it
# proves it can still refuse before its silence is believed (the discipline
# scripts/check-task-ids.sh --selftest already follows).
# ---------------------------------------------------------------------------
if [ "$selftest" -eq 1 ]; then
  case "$self" in
    /*) script=$self ;;
    *) script="$(pwd -P)/$self" ;;
  esac
  if [ ! -f lean-toolchain ] || [ ! -f lake-manifest.json ]; then
    echo "gen-build-provenance: --selftest needs the repository root as the working directory (it copies lean-toolchain and lake-manifest.json into its fixtures)" >&2
    exit 2
  fi
  if ! command -v git >/dev/null 2>&1; then
    echo "gen-build-provenance: --selftest needs git on PATH — the refusal paths it exercises are git ones" >&2
    exit 2
  fi
  root=$(pwd -P)
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  failures=0

  # A directory holding the two inputs the generator reads, and nothing else.
  fixture() {
    d="$work/$1"
    mkdir -p "$d/Tl/Build"
    cp "$root/lean-toolchain" "$root/lake-manifest.json" "$d/"
    echo "$d"
  }
  git_fixture() {
    d=$(fixture "$1")
    git -C "$d" init -q .
    git -C "$d" config user.email selftest@example.invalid
    git -C "$d" config user.name selftest
    echo "$d"
  }
  # Run the script in $1, assert its exit status is $2. $3 names the case.
  expect_status() {
    dir=$1; want=$2; name=$3; shift 3
    got=0
    ( cd "$dir" && "$script" "$@" >"$work/out" 2>"$work/err" ) || got=$?
    if [ "$got" -ne "$want" ]; then
      echo "  FAIL $name: expected exit $want, got $got" >&2
      sed 's/^/    /' "$work/err" >&2
      failures=$((failures + 1))
      return 0
    fi
    echo "  ok   $name (exit $got)"
  }
  # Assert the generated file in $1 contains $2.
  expect_output_contains() {
    if grep -q "$2" "$1/$output"; then
      echo "  ok   $3"
    else
      echo "  FAIL $3: $output does not contain '$2'" >&2
      sed 's/^/    /' "$1/$output" >&2
      failures=$((failures + 1))
    fi
  }

  echo "gen-build-provenance --selftest:"

  d=$(fixture argument); expect_status "$d" 2 "an unknown argument is refused" --nope
  d=$(fixture missing-toolchain); rm "$d/lean-toolchain"
  expect_status "$d" 2 "a missing lean-toolchain is refused"
  d=$(fixture missing-manifest); rm "$d/lake-manifest.json"
  expect_status "$d" 2 "a missing lake-manifest.json is refused"

  # A toolchain line outside the permitted character class must not be spliced
  # into a Lean string literal.
  d=$(fixture bad-toolchain); printf 'leanprover/lean4:v4.32.2"; evil\n' > "$d/lean-toolchain"
  expect_status "$d" 2 "a toolchain line with unexpected characters is refused"

  d=$(fixture no-repo)
  expect_status "$d" 2 "--stamp outside a git repository is refused" --stamp
  d=$(git_fixture no-commit)
  expect_status "$d" 2 "--stamp with no commit at HEAD is refused" --stamp

  # A source tree unpacked *inside* someone else's checkout must not inherit
  # that checkout's commit.
  d=$(git_fixture outer); git -C "$d" commit -q --allow-empty -m outer
  mkdir -p "$d/unpacked/Tl/Build"
  cp "$root/lean-toolchain" "$root/lake-manifest.json" "$d/unpacked/"
  expect_status "$d/unpacked" 2 "--stamp below an unrelated repository is refused" --stamp

  # The development stamp: no commit, never dirty, whatever the tree looks like.
  d=$(fixture development)
  expect_status "$d" 0 "a development stamp needs no git at all"
  expect_output_contains "$d" 'stampCommit : String := ""' "the development stamp carries no commit"
  expect_output_contains "$d" 'stampDirty : Bool := false' "the development stamp is not dirty"

  d=$(git_fixture clean)
  cp "$root/$output" "$d/$output"
  git -C "$d" add -A && git -C "$d" commit -q -m seed
  expect_status "$d" 0 "--stamp on a clean checkout succeeds" --stamp
  expect_output_contains "$d" 'stampDirty : Bool := false' "a clean checkout stamps clean"
  # Idempotence: the file the first run wrote must not make the second run
  # call the tree dirty.
  expect_status "$d" 0 "--stamp is idempotent" --stamp
  expect_output_contains "$d" 'stampDirty : Bool := false' "a second --stamp still stamps clean"

  d=$(git_fixture modified)
  cp "$root/$output" "$d/$output"
  git -C "$d" add -A && git -C "$d" commit -q -m seed
  printf 'leanprover/lean4:v9.99.9\n' > "$d/lean-toolchain"
  expect_status "$d" 0 "--stamp on a modified tracked file succeeds" --stamp
  expect_output_contains "$d" 'stampDirty : Bool := true' "a modified tracked file stamps dirty"

  # Untracked files change what gets compiled, so they count — even when the
  # repository's own config tells git to hide them.
  d=$(git_fixture untracked-hidden)
  cp "$root/$output" "$d/$output"
  git -C "$d" add -A && git -C "$d" commit -q -m seed
  git -C "$d" config status.showUntrackedFiles no
  : > "$d/EXTRA.c"
  expect_status "$d" 0 "--stamp with hidden untracked files succeeds" --stamp
  expect_output_contains "$d" 'stampDirty : Bool := true' \
    "an untracked file counts even under status.showUntrackedFiles=no"

  # A git that cannot report must not be read as a clean tree.
  d=$(git_fixture broken-index)
  cp "$root/$output" "$d/$output"
  git -C "$d" add -A && git -C "$d" commit -q -m seed
  printf 'leanprover/lean4:v9.99.9\n' > "$d/lean-toolchain"
  printf 'garbage' > "$d/.git/index"
  expect_status "$d" 2 "--stamp refuses when git status cannot run" --stamp

  if [ "$failures" -ne 0 ]; then
    echo "gen-build-provenance: --selftest found $failures broken case(s). The generator no longer refuses what it claims to refuse — repair it before trusting a stamp it produces." >&2
    exit 1
  fi
  echo "gen-build-provenance: --selftest passed"
  exit 0
fi

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
    echo "gen-build-provenance: no sha256sum or shasum on PATH — cannot digest $1. Install coreutils (Linux) or use the system shasum (macOS); the stamp cannot name the dependency set without it." >&2
    exit 2
  fi
}

toolchain=$(tr -d ' \t\r\n' < lean-toolchain)
manifest_digest=$(sha256_of lake-manifest.json)

commit=''
dirty='false'
if [ "$stamp" -eq 1 ]; then
  if ! command -v git >/dev/null 2>&1; then
    echo "gen-build-provenance: --stamp needs git on PATH to read the source commit. Install git, or run without --stamp for a development stamp." >&2
    exit 2
  fi
  if ! commit=$(git rev-parse HEAD 2>/dev/null); then
    echo "gen-build-provenance: --stamp needs a git checkout with a commit at HEAD — this directory is not in a repository, or the repository has no commits yet. Clone or commit the source first, or run without --stamp for a development stamp." >&2
    exit 2
  fi
  # `git rev-parse` walks up to the nearest ancestor repository, so a source
  # tree merely sitting *inside* an unrelated checkout would otherwise be
  # stamped with that checkout's commit — a `clean` claim naming a commit that
  # does not contain this source at all.
  toplevel=$(git rev-parse --show-toplevel 2>/dev/null || true)
  if [ "$toplevel" != "$(pwd -P)" ]; then
    echo "gen-build-provenance: --stamp found a git repository at '${toplevel:-<unknown>}', not this directory — the source here is not what that repository tracks. Clone or unpack the source as its own git checkout, or run without --stamp for a development stamp." >&2
    exit 2
  fi
  # Untracked files count: they can change what gets compiled. Two deviations
  # from a bare `git status --porcelain`:
  #   - the config is pinned, because a repository or user setting of
  #     status.showUntrackedFiles=no would hide exactly the files this line
  #     says must count;
  #   - this script's own output is excluded, since it is overwritten a few
  #     lines below and so cannot affect the build. Without the exclusion a
  #     second --stamp in one checkout would call the tree dirty on account of
  #     the first run's stamp.
  # The status is checked rather than discarded: a git that cannot report is
  # not evidence of a clean tree.
  if ! status=$(git -c status.showUntrackedFiles=normal status --porcelain \
                  -- . ":(exclude)$output" 2>&1); then
    echo "gen-build-provenance: git status failed, so working-tree cleanliness is unknown:" >&2
    echo "$status" | sed 's/^/  /' >&2
    echo "Repair the checkout (a corrupt index is the usual cause) and re-run. A stamp must not claim 'clean' for a tree it could not read." >&2
    exit 2
  fi
  if [ -n "$status" ]; then
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
      echo "gen-build-provenance: refusing to embed $1 value '$2' — expected only [0-9A-Za-z./:_-]. Check the file it came from; a value with other characters would be spliced into a Lean string literal." >&2
      exit 2
      ;;
  esac
}
check_plain toolchain "$toolchain"
check_plain manifest-digest "$manifest_digest"
[ -z "$commit" ] || check_plain commit "$commit"

cat > "$output" <<LEAN
/-
\`Tl.Build.Stamp\` — the build provenance baked into this binary.

GENERATED FILE — do not edit by hand. Regenerate with

    scripts/gen-build-provenance.sh              # development stamp (this copy)
    scripts/gen-build-provenance.sh --stamp      # stamp the current git HEAD

The checked-in copy is deliberately the *development* stamp: \`commit\` is empty,
so a plain \`lake build\` produces a binary that reports itself as an
unidentified local build rather than claiming a source commit it may not match.
CI regenerates this file and diffs it, so a stamped copy cannot reach main. The
release workflow runs \`--stamp\` on a clean checkout of the tagged commit before
building, which is what puts a real commit here.

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

echo "gen-build-provenance: wrote $output (commit='${commit:-<development>}' dirty=$dirty toolchain=$toolchain)"
