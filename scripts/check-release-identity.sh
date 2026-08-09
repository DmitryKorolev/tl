#!/bin/sh
# Check that the pinned signing identity in release/identity.json actually
# discriminates — that it accepts this repository's release workflow on a
# SemVer tag and rejects everything else.
#
#   scripts/check-release-identity.sh              check the committed pin
#   scripts/check-release-identity.sh --selftest   prove the checker can fail
#
# Why this exists as its own gate: `Tests/ReleaseTests.lean` guards that every
# operative copy of the pin carries the same *text*, which is drift. It cannot
# guard what the text *means*, because the expression is a Go regular
# expression and the test suite has no regex engine. An expression that is
# anchored and well-formed but matches the wrong repository would sail through
# a text-equality check while hollowing out the fail-closed verifier
# (ADR-0014 T3), so the meaning is checked here, against adversarial
# candidates.
#
# The engine is Python's `re`, and cosign's is Go's RE2 — which is a strict
# subset, with no lookaround and no backreferences. This script used to claim
# they were "the same engine class"; they are not, and a pin using either
# construct would pass every candidate here and then make cosign error on every
# call. The constructs RE2 rejects are therefore refused explicitly below,
# which is narrower than compiling with the real engine and is stated as such.
set -eu

config="release/identity.json"
if [ ! -f "$config" ]; then
  echo "check-release-identity: $config not found — run this from the repository root" >&2
  exit 2
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "check-release-identity: python3 not found — it supplies the regular-expression engine this check needs. Install python3, or run this gate in CI only and say so in ADR-0026." >&2
  exit 2
fi

selftest=0
case "${1-}" in
  '') ;;
  --selftest) selftest=1 ;;
  *)
    echo "check-release-identity: unknown argument '$1' — pass --selftest or nothing" >&2
    exit 2
    ;;
esac

# The RE2 refusals, exercised before the permissive-pin case below. Each runs
# this script against a substituted pin in a throwaway directory, because the
# constructs are rejected *before* the candidate evaluation and so cannot be
# reached by the SELFTEST substitution. A refusal nothing exercises is a
# refusal that has already stopped working, for all anyone knows.
if [ "$selftest" -eq 1 ]; then
  self=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)/$(basename -- "$0")
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  re2_failures=0
  re2_case() {
    # re2_case <name> <expression>
    d="$work/$(printf '%s' "$1" | tr ' ' '_')"
    mkdir -p "$d/release"
    python3 - "$config" "$d/release/identity.json" "$2" <<'PY'
import json, sys
pin = json.load(open(sys.argv[1]))
pin["certificateIdentityRegexp"] = sys.argv[3]
json.dump(pin, open(sys.argv[2], "w"), indent=2)
PY
    cp "$self" "$d/"
    got=0
    ( cd "$d" && sh "./$(basename -- "$self")" >"$work/out" 2>"$work/err" ) || got=$?
    if [ "$got" -eq 1 ] && grep -q "RE2 does not support\|multiline flag" "$work/err"; then
      echo "  ok   $1 is refused"
    else
      echo "  FAIL $1 is refused: expected exit 1 naming RE2, got $got" >&2
      sed 's/^/    /' "$work/err" >&2
      re2_failures=$((re2_failures + 1))
    fi
  }
  echo "check-release-identity --selftest:"
  base='^https://github\.com/DmitryKorolev/tl/\.github/workflows/release\.yml@refs/tags/v'
  re2_case "a negative lookahead" "${base}(?!x)(0|[1-9][0-9]*)\\.0\\.0\$"
  re2_case "a lookbehind" "${base}(?<=v)(0|[1-9][0-9]*)\\.0\\.0\$"
  re2_case "a backreference" "${base}([0-9])\\1\\.0\\.0\$"
  re2_case "the multiline flag" "(?m)${base}(0|[1-9][0-9]*)\\.0\\.0\$"
  if [ "$re2_failures" -ne 0 ]; then
    echo "check-release-identity: --selftest found $re2_failures broken RE2 refusal(s). A pin using a construct cosign's engine rejects would pass this gate and then break every verifier." >&2
    exit 1
  fi
fi

SELFTEST="$selftest" python3 - "$config" <<'PY'
import json
import os
import re
import sys

config_path = sys.argv[1]
with open(config_path, encoding="utf-8") as handle:
    config = json.load(handle)

repository = config["repository"]
workflow = config["releaseWorkflow"]
issuer = config["certificateOidcIssuer"]
expression = config["certificateIdentityRegexp"]

# A deliberately wrong expression, used only by --selftest: it is anchored and
# looks plausible, but the repository segment is unescaped and unconstrained,
# which is exactly the failure a text-equality drift guard cannot see.
if os.environ.get("SELFTEST") == "1":
    expression = r"^https://github\.com/.*/\.github/workflows/release\.yml@refs/tags/v.*$"

subject = f"https://github.com/{repository}/{workflow}@refs/tags/"

accept = [
    subject + "v0.1.0",
    subject + "v1.2.3",
    subject + "v10.20.30",
    subject + "v0.1.0-rc.1",
    subject + "v0.1.0-alpha",
    subject + "v0.1.0-0.3.7",
]
reject = [
    # Not a tag at all.
    f"https://github.com/{repository}/{workflow}@refs/heads/main",
    f"https://github.com/{repository}/{workflow}@refs/pull/1/merge",
    # A different repository whose name contains ours, or is contained by it.
    f"https://github.com/{repository}-evil/{workflow}@refs/tags/v0.1.0",
    f"https://github.com/evil-{repository}/{workflow}@refs/tags/v0.1.0",
    f"https://github.com/evil/{repository}/{workflow}@refs/tags/v0.1.0",
    # A different workflow in this repository: signing must not be delegable.
    f"https://github.com/{repository}/.github/workflows/ci.yml@refs/tags/v0.1.0",
    f"https://github.com/{repository}/.github/workflows/release.yml.bak@refs/tags/v0.1.0",
    # The dots are metacharacters if unescaped.
    f"https://github.comX{repository}/{workflow}@refs/tags/v0.1.0",
    f"https://github.com/{repository}/.github/workflows/releaseXyml@refs/tags/v0.1.0",
    # Not SemVer.
    subject + "v01.0.0",
    subject + "v1.2",
    subject + "v1.2.3.4",
    subject + "release-1",
    # Trailing content past the tag.
    subject + "v0.1.0/../../evil",
    subject + "v0.1.0\n" + subject + "v0.1.0",
]

try:
    pattern = re.compile(expression)
except re.error as exc:
    print(f"check-release-identity: certificateIdentityRegexp does not compile: {exc}", file=sys.stderr)
    sys.exit(1)

# Python's `re` is not cosign's engine. cosign is Go, and Go's regexp is RE2,
# which is a strict subset: it has no lookaround and no backreferences, by
# construction, because they cannot be matched in linear time. A pin using
# either compiles here, passes every accept/reject candidate below, and then
# makes cosign error on *every* call — so `install.sh`, this script's sibling
# verifier, the release workflow's own pre-publish check and the Homebrew
# formula all fail on genuine, correctly signed artifacts, and the wrapper
# reports it as "the verifier could not run" rather than as a broken pin.
#
# There is no RE2 in the Python standard library, so the check is lexical over
# exactly the constructs RE2 rejects. That is narrower than compiling with the
# real engine and it is stated as such: it catches the two families a pin would
# plausibly reach for, not every difference between the dialects.
RE2_UNSUPPORTED = [
    (r"\(\?=", "a lookahead `(?=`"),
    (r"\(\?!", "a negative lookahead `(?!`"),
    (r"\(\?<=", "a lookbehind `(?<=`"),
    (r"\(\?<!", "a negative lookbehind `(?<!`"),
    (r"\(\?>", "an atomic group `(?>`"),
    (r"(?<!\\)\\[1-9]", "a backreference"),
    (r"[*+?}]\+", "a possessive quantifier"),
]
for probe, description in RE2_UNSUPPORTED:
    if re.search(probe, expression):
        print(
            f"check-release-identity: certificateIdentityRegexp uses {description}, which Go's "
            "RE2 does not support. cosign — not this script — is what actually matches this "
            "expression, and Go's regexp.Compile rejects it outright, so every verification "
            "would fail on genuine artifacts and be reported as a verifier problem rather than "
            "as a broken pin. Express the constraint without lookaround or backreferences.",
            file=sys.stderr,
        )
        sys.exit(1)

# `$` also differs: in Go's default (non-multiline) mode it matches only at end
# of text, while Python's matches before a trailing newline too. The candidates
# below include an embedded newline case for that reason; this states why.
if "(?m)" in expression:
    print(
        "check-release-identity: certificateIdentityRegexp sets the multiline flag. cosign "
        "matches a single certificate identity, so multiline changes only what `^` and `$` "
        "anchor to — which is exactly the property the pin depends on. Remove it.",
        file=sys.stderr,
    )
    sys.exit(1)

if not issuer.startswith("https://"):
    print(
        "check-release-identity: certificateOidcIssuer must be an https URL — "
        f"got {issuer!r}. Set it to the GitHub Actions OIDC issuer.",
        file=sys.stderr,
    )
    sys.exit(1)

failures = []
for candidate in accept:
    # cosign matches with Go's regexp, which is unanchored unless the pattern
    # says otherwise; `re.search` is the same discipline.
    if pattern.search(candidate) is None:
        failures.append(f"should ACCEPT but rejected: {candidate!r}")
for candidate in reject:
    if pattern.search(candidate) is not None:
        failures.append(f"should REJECT but accepted: {candidate!r}")

if os.environ.get("SELFTEST") == "1":
    # A checker that silently stopped discriminating would pass forever, so it
    # proves it can still catch a permissive pin before its silence is
    # believed. Here, failures are the expected outcome.
    if failures:
        print(
            f"check-release-identity: --selftest caught the deliberately-permissive expression "
            f"({len(failures)} candidate(s) misjudged, e.g. {failures[0]}). The checker discriminates."
        )
        sys.exit(0)
    print(
        "check-release-identity: --selftest fed in a deliberately-permissive expression and the "
        "checker accepted it. This gate no longer detects a hollowed-out identity pin — repair the "
        "candidate lists in this script before trusting any green run of it.",
        file=sys.stderr,
    )
    sys.exit(1)

if failures:
    print(
        "check-release-identity: the pinned certificate identity does not discriminate as intended.",
        file=sys.stderr,
    )
    for failure in failures:
        print(f"  {failure}", file=sys.stderr)
    print(
        "Fix release/identity.json's certificateIdentityRegexp — anchor it with ^ and $, escape every "
        "literal dot, and fix the repository and workflow path exactly — then update the copies in "
        "VERIFYING.md, ADR-0006, ADR-0014 and the installer so Tests/ReleaseTests.lean stays green.",
        file=sys.stderr,
    )
    sys.exit(1)

print(
    f"check-release-identity: pin discriminates ({len(accept)} accepted, {len(reject)} rejected) "
    f"for {repository} via {workflow}"
)
PY
