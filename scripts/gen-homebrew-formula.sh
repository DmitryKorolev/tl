#!/bin/sh
# Fill Formula/tl.rb in with a release's version and per-platform digests.
#
#   scripts/gen-homebrew-formula.sh [--template <file>] <version> <sums-file> [<output>]
#   scripts/gen-homebrew-formula.sh --selftest
#
# <version> is the SemVer number without the leading `v`. <sums-file> is the
# release's SHA256SUMS — the *signed* one, already verified by
# scripts/verify-release-artifacts.sh, since every digest written here is taken
# from it on trust. <output> defaults to Formula/tl.rb, and <--template> to the
# same file.
#
# The formula in git carries placeholder digests, so the checked-in copy cannot
# be installed by accident: a placeholder digest matches nothing Homebrew would
# ever download. The release workflow runs this and pushes the result to the
# tap.
#
# `--template` exists because the selftest used to have no way to run without
# overwriting the tracked Formula/tl.rb in the developer's checkout, restoring
# it only by reaching the next line — while its EXIT trap deleted the only
# backup. A Ctrl-C, a CI timeout or a cancelled job left the repository's
# formula pinning digests no artifact will ever have.
#
# <version> is validated strictly before it is used. It reaches two places
# where a loose value is more than a bad filename: a Python replacement string,
# where a backslash is an escape and `\d` aborts the run with a traceback
# instead of a teaching error; and Ruby source, where a quote ends the string
# literal and everything after it is code that `brew install` will execute.
# The sibling generator (scripts/gen-build-provenance.sh) already refuses
# anything outside a fixed character class before splicing into Lean; this one
# accepted anything starting with a digit.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

PLACEHOLDER='0000000000000000000000000000000000000000000000000000000000000000'

usage() {
  echo "usage: $0 [--template <file>] <version> <sums-file> [<output>] | $0 --selftest" >&2
  exit 2
}

fail() {
  echo "gen-homebrew-formula: $1" >&2
  exit 1
}

generate() {
  template=$1
  version=$2
  sums=$3
  output=${4:-"$repo_root/Formula/tl.rb"}

  [ -f "$template" ] || fail "$template not found — pass --template, or run this from a checkout that has Formula/tl.rb."
  [ -f "$sums" ] || fail "$sums not found. Pass the release's SHA256SUMS, and verify it first with scripts/verify-release-artifacts.sh: every digest written into the formula is copied from that file on trust."

  required=$(rc_targets supported) || fail "could not read the target tiers from release/targets.json."
  optional=$(rc_targets best-effort) || fail "could not read the target tiers from release/targets.json."
  # Two statements. Nested inside rc_lower the digest tool's failure is masked
  # by rc_lower succeeding on empty input, and the generator went on to write
  # `sha256 ""` into the formula and report success — the placeholder guard
  # passes, because the placeholder *was* replaced.
  sums_digest=$(rc_sha256_of "$sums") \
    || fail "could not digest $sums, so the fallback url cannot be pinned."
  sums_digest=$(rc_lower "$sums_digest")
  case $sums_digest in
    *[!0-9a-f]* | '') fail "the digest computed for $sums is not lowercase hex ('$sums_digest')." ;;
  esac
  [ "${#sums_digest}" -eq 64 ] \
    || fail "the digest computed for $sums is ${#sums_digest} characters, not 64."

  # Everything from here is one Python pass over the template. The previous
  # shape ran one interpreter per substitution against a shared temp file,
  # which is what made each step's failure mode ("could not find the
  # placeholder") depend on whether an earlier step had already rewritten it.
  TEMPLATE="$template" VERSION="$version" SUMS="$sums" OUTPUT="$output" \
  REQUIRED="$required" OPTIONAL="$optional" PLACEHOLDER="$PLACEHOLDER" \
  SUMS_DIGEST="$sums_digest" python3 <<'PYEOF'
import os
import re
import sys

template = os.environ["TEMPLATE"]
version = os.environ["VERSION"]
sums_path = os.environ["SUMS"]
output = os.environ["OUTPUT"]
required = os.environ["REQUIRED"].split()
optional = os.environ["OPTIONAL"].split()
placeholder = os.environ["PLACEHOLDER"]
sums_digest = os.environ["SUMS_DIGEST"]


def die(message):
    sys.exit(f"gen-homebrew-formula: {message}")


# The version, before it touches anything. Not "starts with a digit": this
# value is interpolated into Ruby source that `brew install` executes, and into
# a regular-expression replacement where a backslash is an escape.
SEMVER = re.compile(
    r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)"
    r"(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$"
)
if version.startswith("v"):
    die(
        f"'{version}' begins with 'v' — pass the version number without it (for example 0.1.0). "
        "The formula composes its own tag as v#{version}, so a leading v would produce vv0.1.0."
    )
if SEMVER.match(version) is None:
    die(
        f"'{version}' is not a SemVer version. It is written into Ruby source that every "
        "`brew install` from the tap executes, so it is restricted to MAJOR.MINOR.PATCH with an "
        "optional dot-separated alphanumeric prerelease suffix — nothing else. This is the same "
        "shape release/identity.json's certificate expression accepts, so a version this rejects "
        "could not have been signed either."
    )

with open(template, encoding="utf-8") as handle:
    text = handle.read()


def read_digest(target):
    """The digest for tl-<target> from the sums file, or None if absent."""
    asset = "tl-" + target
    with open(sums_path, encoding="utf-8") as handle:
        for line in handle:
            parts = line.split()
            if len(parts) >= 2 and parts[1].lstrip("*") == asset:
                digest = parts[0]
                if re.fullmatch(r"[0-9a-fA-F]{64}", digest) is None:
                    die(
                        f"the digest for {asset} in {sums_path} is not 64 hex characters "
                        f"('{digest}') — the sums file is malformed or truncated."
                    )
                return digest.lower()
    return None


def substitute_once(pattern, replacement, what):
    """Exactly one substitution, with the replacement taken literally.

    `re.sub` processes escapes in the *replacement*, so a version containing a
    backslash would be interpreted rather than inserted. A function
    replacement is passed through untouched.
    """
    global text
    text, count = pattern.subn(lambda _match: replacement, text, count=1)
    if count != 1:
        die(
            f"could not find {what} in the formula template. Either the template was already "
            "filled in (regenerate from the committed copy) or its shape changed and this "
            "generator needs updating alongside it."
        )


# The fallback url's tag. The fallback keeps the stable spec resolvable on a
# platform this release published no binary for; without it Homebrew raises
# `formula requires at least a URL` when the formula is *loaded*, for every
# brew command, not just install.
#
# Whether an explicit `version` line is also needed depends on the version.
# Homebrew scans a version out of this url and `brew audit` rejects an explicit
# one as *redundant* — but its scanner drops a SemVer prerelease suffix:
# `Version.detect(".../v1.2.3-rc.1/SHA256SUMS")` is `1.2.3`. Without a line,
# every `v#{version}` url in a prerelease formula would therefore point at a
# release that does not exist, and the formula would claim the stable version
# number. So the line is emitted exactly when the scanned value would be wrong,
# which is also exactly when `brew audit` does not call it redundant.
scanned = version.split("-", 1)[0]
substitute_once(
    re.compile(
        r'^  url "https://github\.com/DmitryKorolev/tl/releases/download/v[^"/]*/SHA256SUMS"$',
        re.M,
    ),
    f'  url "https://github.com/DmitryKorolev/tl/releases/download/v{version}/SHA256SUMS"',
    "the fallback SHA256SUMS url",
)
# …and that fallback's own digest, which is the digest of the sums file itself.
pattern = re.compile(
    r'(url "https://github\.com/DmitryKorolev/tl/releases/download/v'
    + re.escape(version)
    + r'/SHA256SUMS"\n  sha256 ")' + re.escape(placeholder) + r'(")'
)
text, count = pattern.subn(lambda m: m.group(1) + sums_digest + m.group(2), text, count=1)
if count != 1:
    die(
        "could not find the placeholder digest under the fallback SHA256SUMS url. The template's "
        "header shape changed and this generator needs updating alongside it."
    )

if scanned != version:
    # Between the url and the sha256, which is the order `brew style` wants.
    anchor = f'  url "https://github.com/DmitryKorolev/tl/releases/download/v{version}/SHA256SUMS"\n'
    if anchor not in text:
        die("could not place the version line: the fallback url is not where this generator wrote it.")
    text = text.replace(anchor, anchor + f'  version "{version}"\n', 1)
elif re.search(r'^  version "', text, re.M):
    die(
        "the template already carries an explicit `version` line, and this release does not need "
        "one — Homebrew scans the same value from the url, and `brew audit` rejects the "
        "redundancy. Remove it from the template; the generator adds one only for a prerelease."
    )

pinned = []
for target in required + optional:
    digest = read_digest(target)
    if digest is None:
        if target in required:
            die(
                f"{sums_path} has no entry for tl-{target}, which is a Supported target. A formula "
                "cannot pin a digest for an asset the release did not publish; build the missing "
                "target and re-run."
            )
        # Best-effort and absent: drop its url/sha256 pair. The fallback url
        # above keeps the spec resolvable, and `install` refuses on that
        # platform with a message naming the tier.
        print(
            f"gen-homebrew-formula: no digest for tl-{target} — dropping its block. It is a "
            "Best-effort target (ADR-0006), so brew reports that this release published nothing "
            "for that platform instead of the release failing."
        )
        block = re.compile(
            r"\n[ \t]*on_(?:arm|intel) do\n[^\n]*url \"[^\"]*" + re.escape(target)
            + r"\"\n[^\n]*sha256 \"[^\"]*\"\n[ \t]*end\n"
        )
        text, dropped = block.subn("\n", text, count=1)
        if dropped != 1:
            die(
                f"could not find the block to drop for tl-{target}. The formula's shape changed "
                "and this generator needs updating alongside it."
            )
        continue

    pinned.append(target)
    block = re.compile(
        r'(url "[^"]*' + re.escape(target) + r'"\n(\s*)sha256 ")' + re.escape(placeholder) + r'(")'
    )
    text, count = block.subn(lambda m: m.group(1) + digest + m.group(3), text, count=1)
    if count != 1:
        die(
            f"could not find the placeholder sha256 under the tl-{target} url. Either the formula "
            "was already filled in (regenerate from the committed template) or its shape changed "
            "and this generator needs updating alongside it."
        )

# `install` reads this to refuse before downloading anything it cannot use.
# Without it, a dropped Best-effort block would fall through to the fallback
# url and `bin.install` would fail on an asset that was never fetched.
substitute_once(
    re.compile(r"^  PINNED_TARGETS = %w\[[^\]]*\]\.freeze$", re.M),
    "  PINNED_TARGETS = %w[" + " ".join(sorted(pinned)) + "].freeze",
    "the PINNED_TARGETS list",
)

if placeholder in text:
    die(
        "the generated formula still contains a placeholder digest, so at least one url was not "
        "filled in. Do not publish it."
    )

with open(output, "w", encoding="utf-8") as handle:
    handle.write(text)
# `mktemp` yields 0600 and `mv` carries that mode onto the destination, which
# silently made the tracked formula unreadable to anyone but its owner. Written
# in place with an explicit mode instead.
os.chmod(output, 0o644)
print(f"gen-homebrew-formula: wrote {output} for v{version} pinning {len(pinned)} target(s)")
PYEOF
}

selftest() {
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  rc_selftest_begin "gen-homebrew-formula" "$work"

  # The template is copied into the fixture, and every case runs against the
  # copy. Nothing here can touch the checkout's own Formula/tl.rb — which is
  # the point: the previous shape overwrote it and kept its only backup inside
  # the directory the EXIT trap deletes.
  template="$work/template.rb"
  cp "$repo_root/Formula/tl.rb" "$template"
  # Digested as found, not diffed against HEAD: the property is "this selftest
  # changed nothing", which must hold whether or not the formula happens to
  # have uncommitted edits when it runs.
  tracked_before=$(rc_sha256_of "$repo_root/Formula/tl.rb")

  required=$(rc_targets supported)
  optional=$(rc_targets best-effort)
  all_targets="$required $optional"

  gen() {
    "$0" --template "$template" "$@"
  }

  sums="$work/SHA256SUMS"
  : > "$sums"
  i=1
  for target in $all_targets; do
    printf '%s  tl-%s\n' "$(printf '%063d%d' 0 "$i")" "$target" >> "$sums"
    i=$((i + 1))
  done

  out="$work/tl.rb"
  rc_expect_status 0 "a complete sums file fills the formula in" gen 1.2.3 "$sums" "$out"
  rc_note "$(! grep -q '^  version "' "$out" && echo 0 || echo 1)" \
    "no explicit version line survives, so brew audit's redundancy check stays quiet"
  rc_note "$(! grep -q "$PLACEHOLDER" "$out" && echo 0 || echo 1)" "no placeholder digest survives"
  rc_note "$(grep -q 'download/v1.2.3/SHA256SUMS' "$out" && echo 0 || echo 1)" \
    "the fallback url names this release's tag"
  rc_note "$(grep -q "$(rc_sha256_of "$sums")" "$out" && echo 0 || echo 1)" \
    "the fallback url pins the sums file's own digest"
  # `ruby -c` where ruby exists, an explicit skip row where it does not.
  # Written as `command -v ruby && ruby -c … || echo 1` the row reported FAIL on
  # a machine with no ruby, so the whole release policy failed with a message
  # naming no missing tool — two lines after the policy had correctly *skipped*
  # its sibling "the Homebrew formula parses" gate for exactly that reason. A
  # skip is a visible row, never a silent pass and never a failure.
  parses_as_ruby() {
    if ! command -v ruby >/dev/null 2>&1; then
      echo "  skip $2 (ruby is not on PATH)"
      return 0
    fi
    rc_note "$(ruby -c "$1" >/dev/null 2>&1 && echo 0 || echo 1)" "$2"
  }
  parses_as_ruby "$out" "the generated formula parses as Ruby"
  for target in $all_targets; do
    rc_note "$(grep -A1 "${target}\"" "$out" | grep -q 'sha256 "0*[0-9]' && echo 0 || echo 1)" \
      "tl-$target gets a digest"
  done
  # Each digest must land under its own url, not merely somewhere in the file.
  # The fixture numbers the digests in target order, so each asset's digest
  # ends in its own index; a substitution that drifted to a neighbouring block
  # would put the wrong one there.
  i=1
  for target in $all_targets; do
    rc_note "$(grep -A1 "${target}\"" "$out" | grep -q "sha256 \"0*${i}\"" && echo 0 || echo 1)" \
      "the tl-$target digest lands under the tl-$target url"
    i=$((i + 1))
  done
  rc_note "$(grep -q "PINNED_TARGETS = %w\[$(echo "$all_targets" | tr ' ' '\n' | sort | tr '\n' ' ' | sed 's/ $//')\]" "$out" && echo 0 || echo 1)" \
    "PINNED_TARGETS lists every target this formula pins"
  rc_note "$([ "$(stat -f '%Lp' "$out" 2>/dev/null || stat -c '%a' "$out")" = 644 ] && echo 0 || echo 1)" \
    "the generated formula is world-readable, not 0600"

  # The checked-in template must still be a placeholder formula: an
  # accidentally committed filled-in copy would pin a stale release. Five
  # placeholders now — four platform digests plus the fallback's.
  rc_note "$(grep -c "$PLACEHOLDER" "$repo_root/Formula/tl.rb" | grep -qx 5 && echo 0 || echo 1)" \
    "the committed formula still carries five placeholder digests"
  rc_note "$([ "$(rc_sha256_of "$repo_root/Formula/tl.rb")" = "$tracked_before" ] && echo 0 || echo 1)" \
    "the selftest leaves the checkout's own Formula/tl.rb byte-identical"

  # A prerelease. Homebrew's version scanner drops the SemVer suffix, so
  # without an explicit line every interpolated url points at a tag that does
  # not exist and the formula claims the stable number. Every gate passed that
  # formula, because nothing ever generated one at a prerelease version.
  preout="$work/pre.rb"
  rc_expect_status 0 "a prerelease version generates" gen 1.2.3-rc.1 "$sums" "$preout"
  rc_note "$(grep -q '^  version "1.2.3-rc.1"$' "$preout" && echo 0 || echo 1)" \
    "a prerelease formula carries an explicit version line"
  rc_note "$(grep -q 'download/v1.2.3-rc.1/SHA256SUMS' "$preout" && echo 0 || echo 1)" \
    "the prerelease fallback url names the prerelease tag"
  rc_note "$(! grep -q 'download/v1.2.3/' "$preout" && echo 0 || echo 1)" \
    "no url in the prerelease formula points at the stable tag"
  rc_note "$(! grep -q '^  version "' "$out" && echo 0 || echo 1)" \
    "a stable formula carries no version line, so brew audit stays quiet"
  parses_as_ruby "$preout" "the prerelease formula parses as Ruby"

  # A digest tool that is present but broken must refuse, not write an empty
  # sha256 and report success.
  nodigest="$work/nodigest"
  mkdir -p "$nodigest"
  for tool in sha256sum shasum; do
    printf '#!/bin/sh\nexit 127\n' > "$nodigest/$tool"
    chmod +x "$nodigest/$tool"
  done
  rc_expect_output 1 "cannot be pinned" "a broken digest tool refuses rather than pinning nothing" \
    env PATH="$nodigest:$PATH" "$0" --template "$template" 1.2.3 "$sums" "$work/o-nodigest"
  rc_note "$([ ! -e "$work/o-nodigest" ] && echo 0 || echo 1)" \
    "no formula is written when the fallback digest cannot be computed"

  # The version argument is the injection surface: it reaches a Python
  # replacement string and Ruby source. Every one of these used to pass the
  # `[0-9]*` guard.
  rc_expect_output 1 "not a SemVer version" "a version with a backslash escape is refused" \
    gen '1.0.0\d' "$sums" "$work/o-esc"
  rc_expect_output 1 "not a SemVer version" "a version that closes the Ruby string is refused" \
    gen '1.0.0"; system "id"; a="' "$sums" "$work/o-inject"
  rc_expect_output 1 "not a SemVer version" "a version with an interpolation is refused" \
    gen '1.0.0#{`id`}' "$sums" "$work/o-interp"
  rc_expect_output 1 "not a SemVer version" "a version with a newline is refused" \
    gen '1.0.0
evil' "$sums" "$work/o-nl"
  rc_expect_output 1 "not a SemVer version" "a two-component version is refused" \
    gen '1.2' "$sums" "$work/o-short"
  rc_expect_output 1 "not a SemVer version" "a leading-zero component is refused" \
    gen '01.2.3' "$sums" "$work/o-zero"
  rc_expect_output 1 "without it" "a version with a leading v is refused and says so" \
    gen v1.2.3 "$sums" "$work/o4"
  rc_note "$([ ! -e "$work/o-inject" ] && echo 0 || echo 1)" \
    "a refused version writes no formula at all"

  # Refusals about the sums file.
  short="$work/short"
  a_last_required=$(printf '%s' "$required" | awk '{print $NF}')
  grep -v "tl-$a_last_required" "$sums" > "$short"
  rc_expect_output 1 "no entry for tl-$a_last_required" \
    "a sums file missing a Supported asset is refused and names it" \
    gen 1.2.3 "$short" "$work/o2"

  bad="$work/bad"
  # Composed, not written out: the task-ID lint reads a written-out macOS asset
  # name as a possible tracker reference.
  a_required=$(printf '%s' "$required" | cut -d' ' -f1)
  an_optional=$(printf '%s' "$optional" | cut -d' ' -f1)
  printf 'nothex  tl-%s\n' "$a_required" > "$bad"
  for target in $all_targets; do
    [ "$target" = "$a_required" ] || grep "tl-$target" "$sums" >> "$bad"
  done
  rc_expect_status 1 "a malformed digest is refused" gen 1.2.3 "$bad" "$work/o3"

  shortd="$work/shortdigest"
  printf 'abcdef  tl-%s\n' "$a_required" > "$shortd"
  for target in $all_targets; do
    [ "$target" = "$a_required" ] || grep "tl-$target" "$sums" >> "$shortd"
  done
  rc_expect_output 1 "not 64 hex characters" "a digest of the wrong length is refused" \
    gen 1.2.3 "$shortd" "$work/o6"

  rc_expect_status 1 "a missing sums file is refused" gen 1.2.3 "$work/nope" "$work/o5"
  rc_expect_status 2 "no arguments is a usage error" "$0"
  rc_expect_status 2 "an unknown flag is a usage error" "$0" --bogus
  rc_expect_status 2 "a version with no sums file is a usage error" "$0" 1.2.3
  rc_expect_status 2 "--template with no other arguments is a usage error" "$0" --template "$template"

  # A Best-effort target absent from the sums file drops its url/sha256 pair.
  # The formula must still *load* on that platform — the whole reason for the
  # fallback url — and `install` must refuse there with a message.
  besteffort="$work/besteffort"
  grep -v "tl-$an_optional" "$sums" > "$besteffort"
  out2="$work/formula-besteffort.rb"
  rc_expect_status 0 "a missing Best-effort digest drops its block rather than failing" \
    gen 1.2.3 "$besteffort" "$out2"
  rc_note "$(! grep -q "url .*$an_optional" "$out2" && echo 0 || echo 1)" \
    "the dropped block leaves no url for that target"
  rc_note "$(grep -c 'sha256 "' "$out2" | grep -qx 4 && echo 0 || echo 1)" \
    "the formula with a dropped block pins three targets plus the fallback"
  rc_note "$(! grep -q "$PLACEHOLDER" "$out2" && echo 0 || echo 1)" \
    "the formula with a dropped block has no placeholder left"
  parses_as_ruby "$out2" "the formula with a dropped block still parses as Ruby"
  # The load-time failure this shape exists to prevent: a stable spec with no
  # url for the running platform makes Homebrew raise on *load*, for every brew
  # command. The fallback must survive the drop.
  rc_note "$(grep -q 'download/v1.2.3/SHA256SUMS' "$out2" && echo 0 || echo 1)" \
    "the dropped-block formula keeps a fallback url, so its spec still resolves"
  rc_note "$(! grep -q "PINNED_TARGETS.*$an_optional" "$out2" && echo 0 || echo 1)" \
    "the dropped target is absent from PINNED_TARGETS, so install refuses there"

  required_missing="$work/reqmissing"
  a_second_required=$(printf '%s' "$required" | cut -d' ' -f2)
  grep -v "tl-$a_second_required" "$sums" > "$required_missing"
  rc_expect_output 1 "Supported target" "a missing Supported digest aborts and names the tier" \
    gen 1.2.3 "$required_missing" "$work/o7"

  # The generated formula must still perform the signature verification. A
  # formula that only checks Homebrew's sha256 would install unsigned bytes
  # from anyone who could serve that url.
  rc_note "$(grep -q 'verify-blob' "$out" && grep -q 'CERTIFICATE_IDENTITY' "$out" \
          && grep -q 'OIDC_ISSUER' "$out" && echo 0 || echo 1)" \
    "the generated formula still verifies the signature against the pinned identity"

  # A template whose placeholders were already filled in must be refused rather
  # than silently producing a formula pinning a stale release.
  prefilled="$work/prefilled.rb"
  sed "s/$PLACEHOLDER/1111111111111111111111111111111111111111111111111111111111111111/" \
    "$template" > "$prefilled"
  rc_expect_status 1 "a template with no placeholder left is refused" \
    "$0" --template "$prefilled" 1.2.3 "$sums" "$work/o8"

  rc_selftest_end "Do not publish a formula this generator produced."
}

template=''
case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  --template)
    [ "$#" -ge 3 ] || usage
    template=$2
    shift 2
    [ "$#" -ge 2 ] && [ "$#" -le 3 ] || usage
    generate "$template" "$@"
    ;;
  -*) usage ;;
  *)
    [ "$#" -ge 2 ] && [ "$#" -le 3 ] || usage
    generate "$repo_root/Formula/tl.rb" "$@"
    ;;
esac
