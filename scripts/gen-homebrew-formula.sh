#!/bin/sh
# Fill Formula/tl.rb in with a release's version and per-platform digests.
#
#   scripts/gen-homebrew-formula.sh <version> <sums-file> [<output>]
#   scripts/gen-homebrew-formula.sh --selftest
#
# <version> is the SemVer number without the leading `v`. <sums-file> is the
# release's SHA256SUMS — the *signed* one, already verified by
# scripts/verify-release-artifacts.sh, since every digest written here is taken
# from it on trust. <output> defaults to Formula/tl.rb.
#
# The formula in git carries placeholder digests, so the checked-in copy cannot
# be installed by accident: a placeholder digest matches nothing Homebrew would
# ever download. The release workflow runs this and pushes the result to the
# tap.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
TARGETS='darwin-arm64 darwin-x64 linux-arm64 linux-x64'
PLACEHOLDER='0000000000000000000000000000000000000000000000000000000000000000'

usage() {
  echo "usage: $0 <version> <sums-file> [<output>] | $0 --selftest" >&2
  exit 2
}

fail() {
  echo "gen-homebrew-formula: $1" >&2
  exit 1
}

generate() {
  version=$1
  sums=$2
  output=${3:-"$repo_root/Formula/tl.rb"}
  template="$repo_root/Formula/tl.rb"

  [ -f "$template" ] || fail "$template not found — run this from a checkout that has the formula."
  [ -f "$sums" ] || fail "$sums not found. Pass the release's SHA256SUMS, and verify it first with scripts/verify-release-artifacts.sh: every digest written into the formula is copied from that file on trust."
  case $version in
    [0-9]*) ;;
    *) fail "'$version' is not a version number — pass it without the leading 'v' (for example 0.1.0)." ;;
  esac

  tmp=$(mktemp)
  cp "$template" "$tmp"

  # The version first, so the url interpolations below resolve to the right tag.
  python3 - "$tmp" "$version" <<'PYEOF'
import pathlib, re, sys
path, version = pathlib.Path(sys.argv[1]), sys.argv[2]
text = path.read_text()
new, count = re.subn(r'^  version "[^"]*"$', f'  version "{version}"', text, count=1, flags=re.M)
if count != 1:
    sys.exit("gen-homebrew-formula: could not find the version line in the formula template")
path.write_text(new)
PYEOF

  # Then each platform digest, matched to the url immediately above it. The
  # formula lists the four blocks in a fixed order; rather than depend on that,
  # each substitution is anchored to its own asset's url.
  for target in $TARGETS; do
    digest=$(awk -v want="tl-$target" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' "$sums") \
      || fail "$sums has no entry for tl-$target. A formula cannot pin a digest for an asset the release did not publish; if that target was deliberately skipped, remove its block from the formula in the same change."
    case $digest in
      *[!0-9a-f]* | '') fail "the digest for tl-$target in $sums is not lowercase hex ('$digest') — the sums file is malformed." ;;
    esac
    [ "${#digest}" -eq 64 ] || fail "the digest for tl-$target in $sums is ${#digest} characters, not 64."
    python3 - "$tmp" "$target" "$digest" "$PLACEHOLDER" <<'PYEOF'
import pathlib, re, sys
path, target, digest, placeholder = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
text = path.read_text()
pattern = re.compile(
    r'(url "[^"]*/tl-' + re.escape(target) + r'"\n(\s*)sha256 ")' + re.escape(placeholder) + r'(")'
)
new, count = pattern.subn(lambda m: m.group(1) + digest + m.group(3), text, count=1)
if count != 1:
    sys.exit(
        f"gen-homebrew-formula: could not find the placeholder sha256 under the tl-{target} url. "
        "Either the formula was already filled in (regenerate from the committed template) or its "
        "shape changed and this generator needs updating alongside it."
    )
path.write_text(new)
PYEOF
  done

  if grep -q "$PLACEHOLDER" "$tmp"; then
    fail "the generated formula still contains a placeholder digest, so at least one platform was not filled in. Do not publish it."
  fi
  mv "$tmp" "$output"
  echo "gen-homebrew-formula: wrote $output for v$version"
}

selftest() {
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  failures=0
  note() {
    if [ "$1" -eq 0 ]; then echo "  ok   $2"; else echo "  FAIL $2" >&2; failures=$((failures + 1)); fi
  }

  echo "gen-homebrew-formula --selftest:"

  sums="$work/SHA256SUMS"
  : > "$sums"
  i=1
  for target in $TARGETS; do
    printf '%s  tl-%s\n' "$(printf '%063d%d' 0 "$i")" "$target" >> "$sums"
    i=$((i + 1))
  done

  out="$work/tl.rb"
  if "$0" 1.2.3 "$sums" "$out" >/dev/null 2>"$work/err"; then
    note 0 "a complete sums file fills the formula in"
  else
    note 1 "a complete sums file fills the formula in"
    sed 's/^/    /' "$work/err" >&2
  fi
  note "$(grep -q 'version "1.2.3"' "$out" && echo 0 || echo 1)" "the version is written"
  note "$(! grep -q "$PLACEHOLDER" "$out" && echo 0 || echo 1)" "no placeholder digest survives"
  for target in $TARGETS; do
    note "$(grep -A1 "tl-${target}\"" "$out" | grep -q 'sha256 "0*[0-9]' && echo 0 || echo 1)" \
      "tl-$target gets a digest"
  done
  # Each digest must land under its own url, not merely somewhere in the file.
  note "$(grep -A1 'tl-linux-x64"' "$out" | grep -q '00004' && echo 0 || echo 1)" \
    "each digest lands under its own asset's url"

  # The checked-in template must still be a placeholder formula: an accidentally
  # committed filled-in copy would pin a stale release.
  note "$(grep -c "$PLACEHOLDER" "$repo_root/Formula/tl.rb" | grep -qx 4 && echo 0 || echo 1)" \
    "the committed formula still carries four placeholder digests"

  # Refusals.
  short="$work/short"
  grep -v 'tl-linux-x64' "$sums" > "$short"
  got=0; ( "$0" 1.2.3 "$short" "$work/o2" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'no entry for tl-linux-x64' "$work/err" && echo 0 || echo 1)" \
    "a sums file missing an asset is refused and names it"
  bad="$work/bad"
  sed 's/^0*1 /not-a-digest /' "$sums" > "$bad"
  printf 'nothex  tl-darwin-arm64\n' > "$bad"
  for target in darwin-x64 linux-arm64 linux-x64; do grep "tl-$target" "$sums" >> "$bad"; done
  got=0; ( "$0" 1.2.3 "$bad" "$work/o3" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && echo 0 || echo 1)" "a malformed digest is refused"
  got=0; ( "$0" v1.2.3 "$sums" "$work/o4" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'without the leading' "$work/err" && echo 0 || echo 1)" \
    "a version with a leading v is refused and says so"
  got=0; ( "$0" 1.2.3 "$work/nope" "$work/o5" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && echo 0 || echo 1)" "a missing sums file is refused"
  for args in "" "--bogus" "1.2.3"; do
    got=0
    # shellcheck disable=SC2086
    ( "$0" $args >/dev/null 2>&1 ) || got=$?
    note "$([ "$got" -eq 2 ] && echo 0 || echo 1)" "'$args' is a usage error (exit $got)"
  done

  if [ "$failures" -ne 0 ]; then
    echo "gen-homebrew-formula: --selftest found $failures broken case(s)." >&2
    exit 1
  fi
  echo "gen-homebrew-formula: --selftest passed"
  exit 0
}

case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  -*) usage ;;
  *)
    [ "$#" -ge 2 ] && [ "$#" -le 3 ] || usage
    generate "$@"
    ;;
esac
