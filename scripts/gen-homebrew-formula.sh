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
# The same tiers the rest of the pipeline honours (ADR-0006): a Best-effort
# target that did not build must not break the Homebrew channel after the
# release is already public.
REQUIRED_TARGETS='darwin-arm64 linux-arm64 linux-x64'
OPTIONAL_TARGETS='darwin-x64'
TARGETS="$REQUIRED_TARGETS $OPTIONAL_TARGETS"
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
    if ! digest=$(awk -v want="tl-$target" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' "$sums"); then
      case " $REQUIRED_TARGETS " in
        *" $target "*)
          fail "$sums has no entry for tl-$target, which is a Supported target. A formula cannot pin a digest for an asset the release did not publish; build the missing target and re-run."
          ;;
        *)
          # Best-effort and absent: drop its block rather than pin a digest
          # that does not exist. The placeholder guard below would otherwise
          # reject the output, so the removal is required, not cosmetic.
          echo "gen-homebrew-formula: no digest for tl-$target — dropping its block from the formula. It is a Best-effort target (ADR-0006), so brew simply offers nothing on that platform for this release."
          python3 - "$tmp" "$target" <<'PYEOF'
import pathlib, re, sys
path, target = pathlib.Path(sys.argv[1]), sys.argv[2]
text = path.read_text()
# The whole `on_arm do` / `on_intel do` block whose url names this target.
pattern = re.compile(
    r'\n[ \t]*on_(?:arm|intel) do\n[^\n]*url "[^"]*' + re.escape(target)
    + r'"\n[^\n]*sha256 "[^"]*"\n[ \t]*end\n'
)
new, count = pattern.subn('\n', text, count=1)
if count != 1:
    sys.exit(
        f"gen-homebrew-formula: could not find the block to drop for tl-{target}. The formula's "
        "shape changed and this generator needs updating alongside it."
    )
path.write_text(new)
PYEOF
          continue
          ;;
      esac
    fi
    case $digest in
      *[!0-9a-f]* | '') fail "the digest for tl-$target in $sums is not lowercase hex ('$digest') — the sums file is malformed." ;;
    esac
    [ "${#digest}" -eq 64 ] || fail "the digest for tl-$target in $sums is ${#digest} characters, not 64."
    python3 - "$tmp" "$target" "$digest" "$PLACEHOLDER" <<'PYEOF'
import pathlib, re, sys
path, target, digest, placeholder = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
text = path.read_text()
pattern = re.compile(
    r'(url "[^"]*' + re.escape(target) + r'"\n(\s*)sha256 ")' + re.escape(placeholder) + r'(")'
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
    note "$(grep -A1 "${target}\"" "$out" | grep -q 'sha256 "0*[0-9]' && echo 0 || echo 1)" \
      "tl-$target gets a digest"
  done
  # Each digest must land under its own url, not merely somewhere in the file.
  # The fixture numbers the digests in TARGETS order, so each asset's digest
  # ends in its own index; a substitution that drifted to a neighbouring block
  # would put the wrong one there.
  i=1
  for target in $TARGETS; do
    note "$(grep -A1 "${target}\"" "$out" | grep -q "sha256 \"0*${i}\"" && echo 0 || echo 1)" \
      "the tl-$target digest lands under the tl-$target url"
    i=$((i + 1))
  done

  # The checked-in template must still be a placeholder formula: an accidentally
  # committed filled-in copy would pin a stale release.
  note "$(grep -c "$PLACEHOLDER" "$repo_root/Formula/tl.rb" | grep -qx 4 && echo 0 || echo 1)" \
    "the committed formula still carries four placeholder digests"

  # Refusals.
  short="$work/short"
  a_last_required=$(printf '%s' "$REQUIRED_TARGETS" | awk '{print $NF}')
  grep -v "tl-$a_last_required" "$sums" > "$short"
  got=0; ( "$0" 1.2.3 "$short" "$work/o2" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q "no entry for tl-$a_last_required" "$work/err" && echo 0 || echo 1)" \
    "a sums file missing an asset is refused and names it"
  bad="$work/bad"
  # Composed, not written out: the task-ID lint reads a written-out macOS asset
  # name as a possible tracker reference.
  a_required=$(printf '%s' "$REQUIRED_TARGETS" | cut -d' ' -f1)
  an_optional=$(printf '%s' "$OPTIONAL_TARGETS" | cut -d' ' -f1)
  printf 'nothex  tl-%s\n' "$a_required" > "$bad"
  for target in $TARGETS; do
    [ "$target" = "$a_required" ] || grep "tl-$target" "$sums" >> "$bad"
  done
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

  # A digest of the right alphabet but the wrong length must still be refused.
  shortd="$work/shortdigest"
  printf 'abcdef  tl-%s\n' "$a_required" > "$shortd"
  for target in $TARGETS; do
    [ "$target" = "$a_required" ] || grep "tl-$target" "$sums" >> "$shortd"
  done
  got=0; ( "$0" 1.2.3 "$shortd" "$work/o6" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'not 64' "$work/err" && echo 0 || echo 1)" \
    "a digest of the wrong length is refused"

  # A Best-effort target absent from the sums file drops its block instead of
  # failing the release.
  besteffort="$work/besteffort"
  grep -v "tl-$an_optional" "$sums" > "$besteffort"
  out2="$work/formula-besteffort.rb"
  if "$0" 1.2.3 "$besteffort" "$out2" >"$work/out" 2>"$work/err"; then
    note 0 "a missing Best-effort digest drops its block rather than failing"
  else
    note 1 "a missing Best-effort digest drops its block rather than failing"
    sed 's/^/    /' "$work/err" >&2
  fi
  # `asset_name` still maps every platform to a name, which is harmless: with
  # no url for that platform Homebrew refuses to install there at all. What
  # must be gone is the url/sha256 pair.
  note "$(! grep -q "url .*$an_optional" "$out2" && echo 0 || echo 1)" \
    "the dropped block leaves no url for that target"
  note "$(grep -c 'sha256 "' "$out2" | grep -qx 3 && echo 0 || echo 1)" \
    "the formula with a dropped block pins three digests"
  note "$(! grep -q "$PLACEHOLDER" "$out2" && echo 0 || echo 1)" \
    "the formula with a dropped block has no placeholder left"
  note "$(command -v ruby >/dev/null 2>&1 && ruby -c "$out2" >/dev/null 2>&1 && echo 0 || echo 1)" \
    "the formula with a dropped block still parses as Ruby"

  # A missing Supported digest still aborts.
  required_missing="$work/reqmissing"
  a_second_required=$(printf '%s' "$REQUIRED_TARGETS" | cut -d' ' -f2)
  grep -v "tl-$a_second_required" "$sums" > "$required_missing"
  got=0; ( "$0" 1.2.3 "$required_missing" "$work/o7" >/dev/null 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'Supported target' "$work/err" && echo 0 || echo 1)" \
    "a missing Supported digest aborts and names the tier"

  # The generated formula must still perform the signature verification. A
  # formula that only checks Homebrew's sha256 would install unsigned bytes
  # from anyone who could serve that url.
  note "$(grep -q 'verify-blob' "$out" && grep -q 'CERTIFICATE_IDENTITY' "$out" \
          && grep -q 'OIDC_ISSUER' "$out" && echo 0 || echo 1)" \
    "the generated formula still verifies the signature against the pinned identity"

  # A template whose placeholder was already filled in must be refused rather
  # than silently producing a formula pinning a stale release.
  prefilled="$work/prefilled.rb"
  sed "s/$PLACEHOLDER/1111111111111111111111111111111111111111111111111111111111111111/" \
    "$repo_root/Formula/tl.rb" > "$prefilled"
  cp "$repo_root/Formula/tl.rb" "$work/template-backup.rb"
  got=0
  ( cp "$prefilled" "$repo_root/Formula/tl.rb" && "$0" 1.2.3 "$sums" "$work/o8" >/dev/null 2>"$work/err" ) || got=$?
  cp "$work/template-backup.rb" "$repo_root/Formula/tl.rb"
  note "$([ "$got" -ne 0 ] && echo 0 || echo 1)" \
    "a template with no placeholder left is refused (exit $got)"

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
