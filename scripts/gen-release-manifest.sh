#!/bin/sh
# The canonical description of one release.
#
#   scripts/gen-release-manifest.sh <dist-dir> <tag> <commit> <output>
#   scripts/gen-release-manifest.sh --verify <dist-dir> <manifest>
#   scripts/gen-release-manifest.sh --selftest
#
# Every job downstream of signing used to reconstruct, independently, what this
# release consists of: the sign job built an asset list with `find`, the
# Homebrew generator re-derived the platform set from SHA256SUMS, the npm job
# re-derived it from which files happened to be present, and each carried its
# own copy of the tier policy. Four derivations of one fact is four chances to
# disagree, and the disagreements are invisible — each job's answer looks
# reasonable on its own.
#
# So the release is described once, here, and the description is signed
# alongside SHA256SUMS. `--verify` is how a later job consumes it: it checks
# that the directory holds exactly what the manifest says, with the digests the
# manifest names, and refuses on anything extra or missing. A job that has
# verified the manifest does not need to re-derive anything.
#
# What it deliberately does *not* do is replace the signature. The manifest is
# evidence about a set of bytes; `scripts/verify-release-artifacts.sh` is what
# establishes that those bytes are the ones this repository signed, and it runs
# first everywhere both are used.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

usage() {
  echo "usage: $0 <dist-dir> <tag> <commit> <output> | $0 --verify <dist-dir> <manifest> | $0 --selftest" >&2
  exit 2
}

generate() {
  dist=$1
  tag=$2
  commit=$3
  output=$4

  [ -d "$dist" ] || { echo "gen-release-manifest: '$dist' is not a directory." >&2; exit 1; }

  DIST="$dist" TAG="$tag" COMMIT="$commit" OUTPUT="$output" ROOT="$repo_root" \
  REQUIRED="$(rc_targets supported)" OPTIONAL="$(rc_targets best-effort)" \
  python3 <<'PYEOF'
import hashlib
import json
import os
import re
import sys

dist = os.environ["DIST"]
tag = os.environ["TAG"]
commit = os.environ["COMMIT"]
output = os.environ["OUTPUT"]
root = os.environ["ROOT"]
required = os.environ["REQUIRED"].split()
optional = os.environ["OPTIONAL"].split()


def die(message):
    sys.exit(f"gen-release-manifest: {message}")


if not re.fullmatch(r"v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?", tag):
    die(f"'{tag}' is not a SemVer release tag; the pinned certificate identity accepts no other shape.")
if not re.fullmatch(r"[0-9a-f]{40}", commit):
    die(f"'{commit}' is not a full 40-character git object id.")


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read(rel):
    with open(os.path.join(root, rel), encoding="utf-8") as handle:
        return handle.read()


version = tag[1:]

# Which platform binaries actually arrived, and which are legitimately absent.
# The tier policy is applied once, here, rather than in each consumer.
targets = []
for target in required + optional:
    asset = f"tl-{target}"
    path = os.path.join(dist, asset)
    tier = "supported" if target in required else "best-effort"
    if not os.path.isfile(path):
        if tier == "supported":
            die(
                f"{asset} is missing from {dist}, and {target} is a Supported target — "
                "release-blocking under ADR-0006. Fix the failing build leg; do not publish a "
                "partial release."
            )
        targets.append({"target": target, "tier": tier, "published": False, "asset": None,
                        "sha256": None, "build": None})
        continue

    # Each leg's own record of what it built, carried out of the build job with
    # the binary. Comparing it here is what makes `sign` sign the bytes that
    # were smoke-tested, rather than whatever the artifact store returned.
    build = None
    metadata_path = os.path.join(dist, f"build-metadata-{target}.json")
    if os.path.isfile(metadata_path):
        with open(metadata_path, encoding="utf-8") as handle:
            build = json.load(handle)
        actual = digest(path)
        if build.get("sha256") != actual:
            die(
                f"{asset} hashes to {actual}, but the {target} build leg recorded "
                f"{build.get('sha256')}. The binary that arrived is not the one that was built "
                "and smoke-tested — the artifact was replaced in transit or the wrong one was "
                "uploaded. Nothing is signed."
            )
        if build.get("commit") != commit:
            die(
                f"the {target} build leg recorded commit {build.get('commit')}, but this release "
                f"is {commit}. The legs did not all build the same source."
            )
    targets.append({
        "target": target,
        "tier": tier,
        "published": True,
        "asset": asset,
        "sha256": digest(path),
        "build": build,
    })

published_targets = [t["target"] for t in targets if t["published"]]

# Every file in the directory, so the manifest describes the release rather
# than a chosen subset of it. Sigstore bundles are excluded: they are produced
# *after* this manifest is written and signed alongside it, so listing them
# would be a promise this file cannot keep.
assets = []
for name in sorted(os.listdir(dist)):
    path = os.path.join(dist, name)
    if not os.path.isfile(path) or name.endswith(".sigstore.json"):
        continue
    if name in ("SHA256SUMS", os.path.basename(output)):
        continue
    if name.startswith("tl-") and name[3:] in [t["target"] for t in targets]:
        kind = "binary"
    elif name.startswith("build-metadata-"):
        kind = "build-metadata"
    elif name.startswith("link-audit-"):
        kind = "link-audit"
    elif name in ("LICENSE", "THIRD-PARTY-LICENSES"):
        kind = "notice"
    elif name.endswith(".spdx.json"):
        kind = "sbom"
    elif name == "REBUILDING.md":
        kind = "documentation"
    else:
        kind = "other"
    assets.append({"name": name, "sha256": digest(path), "kind": kind})

if not assets:
    die(f"{dist} holds no assets to describe. An empty manifest would read as a release with nothing in it rather than as a broken step.")

identity = json.loads(read("release/identity.json"))
scope = identity["npmPackage"].split("/")[0]

manifest = {
    "schemaVersion": 1,
    "product": "tl",
    "version": version,
    "tag": tag,
    "commit": commit,
    "repository": identity["repository"],
    "toolchain": read("lean-toolchain").strip(),
    "lakeManifestSha256": hashlib.sha256(
        open(os.path.join(root, "lake-manifest.json"), "rb").read()
    ).hexdigest(),
    "signing": {
        "certificateOidcIssuer": identity["certificateOidcIssuer"],
        "certificateIdentityRegexp": identity["certificateIdentityRegexp"],
        "workflow": identity["releaseWorkflow"],
    },
    "targets": targets,
    "assets": assets,
    "npm": {
        # A prerelease must not become what `npm install @taskloop/tl` resolves
        # to, and the rule is recorded here rather than recomputed per job.
        "distTag": "next" if "-" in version else "latest",
        "packages": [identity["npmPackage"]]
        + [f"{scope}/tl-bin-{t}" for t in published_targets],
    },
    "homebrew": {
        "tap": f"{identity['repository'].split('/')[0]}/homebrew-tap",
        # A tap carries one formula, so a prerelease is generated and attached
        # but never pushed (ADR-0006).
        "push": "-" not in version,
        "pinnedTargets": published_targets,
    },
}

with open(output, "w", encoding="utf-8") as handle:
    json.dump(manifest, handle, indent=2, sort_keys=True)
    handle.write("\n")
print(
    f"gen-release-manifest: wrote {output} — {len(assets)} assets, "
    f"{len(published_targets)} of {len(targets)} targets published"
)
PYEOF
}

verify() {
  dist=$1
  manifest=$2
  [ -d "$dist" ] || { echo "gen-release-manifest: '$dist' is not a directory." >&2; exit 1; }
  [ -f "$manifest" ] || { echo "gen-release-manifest: '$manifest' not found — it is the signed description every job downstream of signing reads instead of re-deriving the release." >&2; exit 1; }

  DIST="$dist" MANIFEST="$manifest" python3 <<'PYEOF'
import hashlib
import json
import os
import sys

dist = os.environ["DIST"]
manifest_path = os.environ["MANIFEST"]

with open(manifest_path, encoding="utf-8") as handle:
    manifest = json.load(handle)


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


problems = []
described = set()
for asset in manifest["assets"]:
    described.add(asset["name"])
    path = os.path.join(dist, asset["name"])
    if not os.path.isfile(path):
        problems.append(f"{asset['name']} is described by the manifest but is not in {dist}")
        continue
    actual = digest(path)
    if actual != asset["sha256"]:
        problems.append(
            f"{asset['name']} hashes to {actual}, but the manifest says {asset['sha256']}"
        )

# Anything present but undescribed. An extra asset in a signed release is not a
# harmless surplus: it is published under the same release, and a user has no
# way to tell it apart from one this pipeline produced.
allowed_extra = {"SHA256SUMS", os.path.basename(manifest_path)}
for name in sorted(os.listdir(dist)):
    if not os.path.isfile(os.path.join(dist, name)):
        continue
    if name in described or name in allowed_extra or name.endswith(".sigstore.json"):
        continue
    problems.append(
        f"{name} is in {dist} but the manifest does not describe it — a release must not "
        "publish an asset nothing accounts for"
    )

if problems:
    print("gen-release-manifest: the directory does not match the manifest.", file=sys.stderr)
    for problem in problems:
        print(f"  {problem}", file=sys.stderr)
    print(
        "The manifest is signed alongside SHA256SUMS, so a mismatch means either the wrong "
        "directory or a modified one. Do not publish it.",
        file=sys.stderr,
    )
    sys.exit(1)

print(
    f"gen-release-manifest: {dist} matches the manifest for {manifest['tag']} "
    f"({len(manifest['assets'])} assets)"
)
PYEOF
}

selftest() {
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  rc_selftest_begin "gen-release-manifest"
  RC_OUT="$work/out"
  RC_ERR="$work/err"

  commit=1111111111111111111111111111111111111111
  build_dist() {
    d=$1
    shift
    rm -rf "$d"
    mkdir -p "$d"
    for target in "$@"; do
      printf 'binary for %s\n' "$target" > "$d/tl-$target"
      python3 -c '
import hashlib, json, sys
path, target, commit, out = sys.argv[1:5]
with open(path, "rb") as handle:
    digest = hashlib.sha256(handle.read()).hexdigest()
json.dump({"target": target, "sha256": digest, "commit": commit,
           "runner": "ubuntu-latest", "toolchain": "leanprover/lean4:v4.32.2"},
          open(out, "w"), indent=2, sort_keys=True)
' "$d/tl-$target" "$target" "$commit" "$d/build-metadata-$target.json"
      printf 'link audit for %s\n' "$target" > "$d/link-audit-$target.txt"
    done
    printf 'notice\n' > "$d/THIRD-PARTY-LICENSES"
    printf 'license\n' > "$d/LICENSE"
    printf '{}\n' > "$d/tl.spdx.json"
  }

  all_targets=$(rc_targets)
  # shellcheck disable=SC2086
  build_dist "$work/dist" $all_targets
  out="$work/release-manifest.json"
  rc_expect_status 0 "a complete candidate set produces a manifest" \
    "$0" "$work/dist" v1.2.3 "$commit" "$out"
  rc_note "$(python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$out" 2>/dev/null && echo 0 || echo 1)" \
    "the manifest is valid JSON"
  for needle in '"version": "1.2.3"' '"tag": "v1.2.3"' '"distTag": "latest"' '"kind": "sbom"' '"kind": "notice"' '"kind": "link-audit"'; do
    rc_note "$(grep -qF -- "$needle" "$out" && echo 0 || echo 1)" "it records ${needle}"
  done
  rc_expect_status 0 "the manifest verifies against the directory it describes" \
    "$0" --verify "$work/dist" "$out"

  # A prerelease reaches npm under `next`, and the tap is not pushed.
  pre="$work/pre.json"
  "$0" "$work/dist" v1.2.3-rc.1 "$commit" "$pre" >/dev/null 2>&1
  rc_note "$(grep -qF '"distTag": "next"' "$pre" && echo 0 || echo 1)" \
    "a prerelease records the next dist-tag"
  rc_note "$(grep -qF '"push": false' "$pre" && echo 0 || echo 1)" \
    "a prerelease records that the tap is not pushed"

  # The build-boundary check: a binary that does not match what its leg
  # recorded must stop the release. This is the artifact hand-off that
  # previously had no re-verification at all.
  tampered="$work/tampered"
  # shellcheck disable=SC2086
  build_dist "$tampered" $all_targets
  a_target=$(printf '%s' "$all_targets" | cut -d' ' -f1)
  printf 'replaced\n' > "$tampered/tl-$a_target"
  rc_expect_output 1 "not the one that was built" \
    "a binary that differs from what its build leg recorded is refused" \
    "$0" "$tampered" v1.2.3 "$commit" "$work/o1"

  mixed="$work/mixed"
  # shellcheck disable=SC2086
  build_dist "$mixed" $all_targets
  python3 -c '
import json, sys
path = sys.argv[1]
data = json.load(open(path))
data["commit"] = "2222222222222222222222222222222222222222"
json.dump(data, open(path, "w"), indent=2, sort_keys=True)
' "$mixed/build-metadata-$a_target.json"
  rc_expect_output 1 "did not all build the same source" \
    "a leg that built a different commit is refused" \
    "$0" "$mixed" v1.2.3 "$commit" "$work/o2"

  # Tiers: a missing Best-effort target is recorded as unpublished; a missing
  # Supported one stops the release.
  an_optional=$(rc_targets best-effort | cut -d' ' -f1)
  partial="$work/partial"
  # shellcheck disable=SC2086
  build_dist "$partial" $(rc_targets supported)
  ppart="$work/partial.json"
  rc_expect_status 0 "a missing Best-effort target still produces a manifest" \
    "$0" "$partial" v1.2.3 "$commit" "$ppart"
  rc_note "$(python3 -c '
import json, sys
doc = json.load(open(sys.argv[1]))
entry = [t for t in doc["targets"] if t["target"] == sys.argv[2]][0]
sys.exit(0 if entry["published"] is False and entry["tier"] == "best-effort" else 1)' "$ppart" "$an_optional" && echo 0 || echo 1)" \
    "the absent Best-effort target is recorded as unpublished, not omitted"
  rc_note "$(! grep -q "tl-bin-$an_optional" "$ppart" && echo 0 || echo 1)" \
    "the absent target is not listed among the npm packages to publish"

  missing_req="$work/missing-required"
  # shellcheck disable=SC2086
  build_dist "$missing_req" $all_targets
  a_required=$(rc_targets supported | cut -d' ' -f1)
  rm "$missing_req/tl-$a_required" "$missing_req/build-metadata-$a_required.json"
  rc_expect_output 1 "release-blocking" "a missing Supported target is refused" \
    "$0" "$missing_req" v1.2.3 "$commit" "$work/o3"

  # --verify is the consumer side, and it must catch all three ways a directory
  # can stop matching.
  drifted="$work/drifted"
  cp -R "$work/dist" "$drifted"
  cp "$out" "$drifted/release-manifest.json"
  printf 'changed\n' > "$drifted/THIRD-PARTY-LICENSES"
  rc_expect_output 1 "hashes to" "--verify catches a modified asset" \
    "$0" --verify "$drifted" "$out"
  cp -R "$work/dist" "$work/short"
  rm "$work/short/LICENSE"
  rc_expect_output 1 "is not in" "--verify catches a missing asset" \
    "$0" --verify "$work/short" "$out"
  cp -R "$work/dist" "$work/extra"
  printf 'surprise\n' > "$work/extra/unexpected-asset"
  rc_expect_output 1 "does not describe it" "--verify catches an undescribed asset" \
    "$0" --verify "$work/extra" "$out"

  # Argument handling.
  rc_expect_output 1 "not a SemVer release tag" "a non-SemVer tag is refused" \
    "$0" "$work/dist" 1.2.3 "$commit" "$work/o4"
  rc_expect_output 1 "40-character git object id" "a short commit is refused" \
    "$0" "$work/dist" v1.2.3 abc123 "$work/o5"
  rc_expect_status 1 "a missing dist directory is refused" \
    "$0" "$work/nope" v1.2.3 "$commit" "$work/o6"
  rc_expect_status 2 "no arguments is a usage error" "$0"
  rc_expect_status 2 "too few arguments is a usage error" "$0" "$work/dist" v1.2.3
  rc_expect_status 2 "an unknown flag is a usage error" "$0" --bogus

  rc_selftest_end "The manifest is what every job downstream of signing trusts instead of re-deriving the release."
}

case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  --verify)
    [ "$#" -eq 3 ] || usage
    verify "$2" "$3"
    ;;
  -*) usage ;;
  *)
    [ "$#" -eq 4 ] || usage
    generate "$1" "$2" "$3" "$4"
    ;;
esac
