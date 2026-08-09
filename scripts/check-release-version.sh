#!/bin/sh
# One version, checked everywhere it is written down.
#
#   scripts/check-release-version.sh                 the copies agree
#   scripts/check-release-version.sh --tag v0.1.0    …and agree with this tag
#   scripts/check-release-version.sh --print         print the canonical version
#   scripts/check-release-version.sh --selftest      prove the checker can fail
#
# `Tl/Cli/Commands.lean`'s `productVersion` is canonical: it is the version the
# binary reports, so it is the one a user can observe. Every other copy must
# equal it.
#
# Before this gate nothing compared them. `release.yml` read `productVersion`
# and compared it with the tag; `npm-pack.sh` compared the five npm manifests
# with `productVersion`; and both told the operator, in an error message, to
# "bump the lakefile package version" — which neither of them, nor anything
# else, ever read. A release could therefore ship with Lake metadata claiming a
# different version from the binary, and the pinned literal in
# `Tests/ReleaseTests.lean` was a sixth copy that only failed *after* someone
# had already bumped the other five.
#
# The npm package *name* is checked here too, for the same reason: it is pinned
# in `release/identity.json`, which every prose document is guarded against,
# while the manifest that actually decides what gets published was never
# compared with it.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)

command -v python3 >/dev/null 2>&1 || {
  echo "check-release-version: python3 not found — it parses the manifests this gate compares. Install python3, or run this gate in CI only and say so in ADR-0026." >&2
  exit 2
}

mode=check
tag=''
case "${1-}" in
  '') ;;
  --print) mode=print ;;
  --selftest) mode=selftest ;;
  --tag)
    [ "$#" -eq 2 ] || {
      echo "check-release-version: --tag takes exactly one argument, the tag to compare (for example --tag v0.1.0)" >&2
      exit 2
    }
    tag=$2
    ;;
  *)
    echo "check-release-version: unknown argument '$1' — pass --tag <tag>, --print, --selftest, or nothing" >&2
    exit 2
    ;;
esac

MODE="$mode" TAG="$tag" python3 - "$repo_root" <<'PY'
import json
import os
import re
import shutil
import sys
import tempfile

repo_root = sys.argv[1]
mode = os.environ.get("MODE", "check")
tag = os.environ.get("TAG", "")

SEMVER = re.compile(
    r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)"
    r"(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$"
)


class Drift(Exception):
    pass


def read(root, rel):
    path = os.path.join(root, rel)
    try:
        with open(path, encoding="utf-8") as handle:
            return handle.read()
    except FileNotFoundError:
        raise Drift(
            f"{rel} not found. Every copy of the release version is compared here; a missing "
            f"file means either the layout moved (update this gate with it) or the checkout is "
            f"incomplete."
        )


def one_match(pattern, text, rel, what):
    """Exactly one match, or a refusal naming what went wrong.

    Deliberately not `sed -n 's/…/p'`, which the release workflow used: that
    prints *every* match, so two definitions would silently produce a
    two-line version string that then flowed into $GITHUB_OUTPUT and into
    later `run:` blocks.
    """
    found = pattern.findall(text)
    if not found:
        raise Drift(
            f"{rel} has no {what}. Either the definition moved or changed shape; update the "
            f"pattern in scripts/check-release-version.sh to match it, because the release "
            f"workflow reads the same value and would otherwise ship an empty version."
        )
    if len(found) > 1:
        raise Drift(
            f"{rel} has {len(found)} definitions of {what} ({', '.join(found)}). Exactly one is "
            f"expected; a second copy makes which version ships depend on file order."
        )
    return found[0]


def collect(root):
    """(canonical version, [(label, version)…], npm package name)."""
    product = one_match(
        re.compile(r'^def productVersion : String := "([^"]*)"$', re.M),
        read(root, "Tl/Cli/Commands.lean"),
        "Tl/Cli/Commands.lean",
        "`def productVersion`",
    )

    copies = []
    copies.append((
        "lakefile.lean package version",
        one_match(
            re.compile(r'^  version := v!"([^"]*)"$', re.M),
            read(root, "lakefile.lean"),
            "lakefile.lean",
            "the package `version :=` line",
        ),
    ))
    copies.append((
        "Tests/ReleaseTests.lean pinned `tl version` payload",
        one_match(
            re.compile(
                r'checkEq "tl version: product version" \(jStr out\.data "version"\) \(some "([^"]*)"\)'
            ),
            read(root, "Tests/ReleaseTests.lean"),
            "Tests/ReleaseTests.lean",
            "the pinned `tl version` product-version literal",
        ),
    ))

    manifests = ["npm/tl/package.json"]
    targets = json.loads(read(root, "release/targets.json"))["targets"]
    for entry in targets:
        manifests.append(f"npm/platform/{entry['target']}/package.json")
    for rel in manifests:
        data = json.loads(read(root, rel))
        copies.append((rel, data["version"]))

    identity = json.loads(read(root, "release/identity.json"))
    return product, copies, identity["npmPackage"]


def check(root, tag):
    product, copies, pinned_name = collect(root)
    problems = []

    if SEMVER.match(product) is None:
        problems.append(
            f"productVersion '{product}' is not SemVer. The signing identity in "
            f"release/identity.json only accepts a SemVer tag, so nothing built from this "
            f"version could be signed with an identity any verifier accepts."
        )

    for label, value in copies:
        if value != product:
            problems.append(
                f"{label} is {value!r}, but Tl/Cli/Commands.lean reports {product!r}. Bring "
                f"every copy to {product!r} in one change — the binary's self-report is "
                f"canonical because it is the one a user can observe."
            )

    if tag:
        if not tag.startswith("v"):
            problems.append(
                f"tag {tag!r} does not begin with 'v'. Release tags are vMAJOR.MINOR.PATCH; the "
                f"pinned certificate identity accepts no other shape."
            )
        elif tag[1:] != product:
            problems.append(
                f"tag {tag!r} names version {tag[1:]!r} but the binary reports {product!r}. "
                f"Either bump every copy to {tag[1:]!r} and re-tag, or tag v{product} instead."
            )

    launcher = json.loads(read(root, "npm/tl/package.json"))
    if launcher["name"] != pinned_name:
        problems.append(
            f"npm/tl/package.json is named {launcher['name']!r} but release/identity.json pins "
            f"the published package as {pinned_name!r}. The prose documents are guarded against "
            f"that pin; the manifest that actually decides what gets published was not, so the "
            f"two could name different packages with every gate green."
        )

    return product, copies, problems


if mode == "selftest":
    failures = 0

    def note(ok, name):
        global failures
        if ok:
            print(f"  ok   {name}")
        else:
            print(f"  FAIL {name}", file=sys.stderr)
            failures += 1

    def drifts(root, tag=""):
        """True when the fixture is reported as broken, by refusal or problem."""
        try:
            _, _, problems = check(root, tag)
        except (Drift, KeyError, json.JSONDecodeError):
            return True
        return bool(problems)

    print("check-release-version --selftest:")
    work = tempfile.mkdtemp()
    try:
        fixture = os.path.join(work, "repo")
        for rel in (
            "Tl/Cli/Commands.lean",
            "lakefile.lean",
            "Tests/ReleaseTests.lean",
            "release/targets.json",
            "release/identity.json",
            "npm/tl/package.json",
        ):
            os.makedirs(os.path.join(fixture, os.path.dirname(rel)), exist_ok=True)
            shutil.copy(os.path.join(repo_root, rel), os.path.join(fixture, rel))
        for entry in json.loads(read(repo_root, "release/targets.json"))["targets"]:
            rel = f"npm/platform/{entry['target']}/package.json"
            os.makedirs(os.path.join(fixture, os.path.dirname(rel)), exist_ok=True)
            shutil.copy(os.path.join(repo_root, rel), os.path.join(fixture, rel))

        def restore(rel):
            shutil.copy(os.path.join(repo_root, rel), os.path.join(fixture, rel))

        def rewrite(rel, old, new):
            path = os.path.join(fixture, rel)
            with open(path, encoding="utf-8") as handle:
                text = handle.read()
            if old not in text:
                raise AssertionError(f"selftest fixture: {old!r} not in {rel}")
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(text.replace(old, new, 1))

        note(not drifts(fixture), "the committed copies agree (the fixture starts clean)")

        current, _, _ = check(fixture, "")
        note(drifts(fixture, "v9.9.9"), "a tag that does not match productVersion is caught")
        note(not drifts(fixture, f"v{current}"), "the matching tag is accepted")
        note(drifts(fixture, current), "a tag without its leading v is caught")

        # Each copy in turn. A gate that reads five of six files passes while
        # the sixth ships a contradiction, which is exactly what happened to
        # the lakefile.
        for rel, old, new in [
            ("lakefile.lean", f'version := v!"{current}"', 'version := v!"9.9.9"'),
            (
                "Tests/ReleaseTests.lean",
                f'(jStr out.data "version") (some "{current}")',
                '(jStr out.data "version") (some "9.9.9")',
            ),
            ("npm/tl/package.json", f'"version": "{current}"', '"version": "9.9.9"'),
            (
                "npm/platform/linux-x64/package.json",
                f'"version": "{current}"',
                '"version": "9.9.9"',
            ),
        ]:
            rewrite(rel, old, new)
            note(drifts(fixture), f"a stale version in {rel} is caught")
            restore(rel)

        # A second definition must be refused, not silently resolved by order.
        path = os.path.join(fixture, "Tl/Cli/Commands.lean")
        with open(path, "a", encoding="utf-8") as handle:
            handle.write('\ndef productVersion : String := "9.9.9"\n')
        note(drifts(fixture), "a second productVersion definition is refused, not resolved by order")
        restore("Tl/Cli/Commands.lean")

        # A renamed definition must refuse rather than report an empty version.
        rewrite("Tl/Cli/Commands.lean", "def productVersion : String :=", "def productVersionX : String :=")
        note(drifts(fixture), "a renamed productVersion is refused rather than read as empty")
        restore("Tl/Cli/Commands.lean")

        # A non-SemVer version could never be signed.
        rewrite("Tl/Cli/Commands.lean", f'productVersion : String := "{current}"', 'productVersion : String := "0.1"')
        note(drifts(fixture), "a non-SemVer productVersion is caught")
        restore("Tl/Cli/Commands.lean")

        # The published package name.
        rewrite("npm/tl/package.json", '"name": "@taskloop/tl"', '"name": "@taskloop/tl-renamed"')
        note(drifts(fixture), "a launcher package name that contradicts release/identity.json is caught")
        restore("npm/tl/package.json")
    finally:
        shutil.rmtree(work, ignore_errors=True)

    if failures:
        print(
            f"check-release-version: --selftest found {failures} broken case(s). This gate no "
            "longer notices a version that disagrees with itself — repair it before trusting a "
            "green run.",
            file=sys.stderr,
        )
        sys.exit(1)
    print("check-release-version: --selftest passed")
    sys.exit(0)

try:
    product, copies, problems = check(repo_root, tag)
except Drift as exc:
    print(f"check-release-version: {exc}", file=sys.stderr)
    sys.exit(1)

if mode == "print":
    print(product)
    sys.exit(0)

if problems:
    print("check-release-version: the release version does not agree with itself.", file=sys.stderr)
    for problem in problems:
        print(f"  {problem}", file=sys.stderr)
    sys.exit(1)

where = f" and tag {tag}" if tag else ""
print(f"check-release-version: {1 + len(copies)} copies agree at {product}{where}")
PY
