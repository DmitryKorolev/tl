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
# candidates, with the same engine class cosign uses.
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
