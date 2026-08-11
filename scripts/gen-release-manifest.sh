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

  # Resolved into variables first, with their statuses checked. As assignment
  # prefixes on the `python3` command the substitutions' failures are discarded
  # — the command's own status is what survives — so an unreadable
  # release/targets.json produced empty tier lists, and the manifest below then
  # described a release with no targets and skipped every per-leg
  # build-metadata check. The manifest is signed, so that is a signed document
  # asserting a release whose contents nothing looked at.
  required=$(rc_targets supported) || {
    echo "gen-release-manifest: could not read the release-blocking targets, so the manifest cannot say which artifacts this release requires. A manifest with an empty required list is not a smaller claim, it is a signed claim that nothing was checked." >&2
    exit 1
  }
  optional=$(rc_targets best-effort) || {
    echo "gen-release-manifest: could not read the best-effort targets, so the manifest cannot distinguish an artifact whose absence is acceptable from one whose absence blocks the release." >&2
    exit 1
  }

  DIST="$dist" TAG="$tag" COMMIT="$commit" OUTPUT="$output" ROOT="$repo_root" \
  REQUIRED="$required" OPTIONAL="$optional" \
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
manifest_digest = hashlib.sha256(
    open(os.path.join(root, "lake-manifest.json"), "rb").read()
).hexdigest()
# GITHUB_WORKFLOW_REF is absent outside Actions (the selftest), so an empty
# value means "cannot compare" rather than "compare against nothing".
workflow_ref = os.environ.get("GITHUB_WORKFLOW_REF", "")
run_id = None

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
    #
    # Mandatory, not "checked when present". Written the other way this was
    # fail-open in the worst direction: delete the metadata and every binary
    # publishes with `"build": null` and no comparison at all, so the check
    # that exists to prove the signed bytes were smoke-tested was satisfied by
    # removing the evidence. Absence is now a refusal.
    metadata_path = os.path.join(dist, f"build-metadata-{target}.json")
    if not os.path.isfile(metadata_path):
        die(
            f"{asset} is present but build-metadata-{target}.json is not. Every published target "
            "must carry the record its own build leg wrote — that record is the only thing tying "
            "the signed bytes to the leg that smoke-tested them, so its absence is a refusal "
            "rather than a check that gets skipped. Fix the upload in the build job."
        )
    audit_path = os.path.join(dist, f"link-audit-{target}.txt")
    if not os.path.isfile(audit_path):
        die(
            f"{asset} is present but link-audit-{target}.txt is not. ADR-0006 requires the "
            "link-time audit for every binary release, and it is produced per target by the leg "
            "that built it. Fix the upload in the build job."
        )
    try:
        with open(metadata_path, encoding="utf-8") as handle:
            build = json.load(handle)
    except json.JSONDecodeError as exc:
        die(f"build-metadata-{target}.json is not valid JSON ({exc}).")
    if not isinstance(build, dict):
        die(f"build-metadata-{target}.json is not a JSON object.")

    # Every field the leg is supposed to have recorded, checked against what
    # this job independently knows. A record that merely exists proves nothing;
    # one whose fields are absent would compare `None` against `None` and pass.
    for field in ("target", "sha256", "commit", "tier", "runner", "toolchain",
                  "lakeManifestSha256", "workflowRef", "runId"):
        if not build.get(field):
            die(
                f"build-metadata-{target}.json has no {field!r}. The record is incomplete, so it "
                "cannot establish what it is here to establish; fix the recording step in the "
                "build job rather than relaxing this check."
            )
    actual = digest(path)
    if build["sha256"] != actual:
        die(
            f"{asset} hashes to {actual}, but the {target} build leg recorded "
            f"{build['sha256']}. The binary that arrived is not the one that was built "
            "and smoke-tested — the artifact was replaced in transit or the wrong one was "
            "uploaded. Nothing is signed."
        )
    if build["commit"] != commit:
        die(
            f"the {target} build leg recorded commit {build['commit']}, but this release "
            f"is {commit}. The legs did not all build the same source."
        )
    if build["target"] != target:
        die(
            f"build-metadata-{target}.json records target {build['target']!r}. The records were "
            "crossed between legs, so none of them can be trusted to describe its own binary."
        )
    if build["tier"] != tier:
        die(
            f"the {target} leg recorded tier {build['tier']!r}, but release/targets.json says "
            f"{tier!r}. The tier decides whether a missing binary blocks the release, so the two "
            "must agree."
        )
    if build["toolchain"] != read("lean-toolchain").strip():
        die(
            f"the {target} leg built with toolchain {build['toolchain']!r}, but this checkout "
            f"pins {read('lean-toolchain').strip()!r}. The artifacts do not all come from the "
            "pinned toolchain."
        )
    if build["lakeManifestSha256"] != manifest_digest:
        die(
            f"the {target} leg recorded a lake-manifest digest of "
            f"{build['lakeManifestSha256']}, but this checkout's is {manifest_digest}. The legs "
            "did not all build against the same dependency set."
        )
    # All legs belong to one workflow run; a record from another run means an
    # artifact was carried in from somewhere else.
    if run_id is None:
        run_id = build["runId"]
    elif build["runId"] != run_id:
        die(
            f"the {target} leg records run {build['runId']}, but another leg records {run_id}. "
            "These binaries were not produced by one run of this workflow."
        )
    if workflow_ref and build["workflowRef"] != workflow_ref:
        die(
            f"the {target} leg records workflow {build['workflowRef']!r}, but this job is "
            f"{workflow_ref!r}. The record did not come from this workflow."
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
    "lakeManifestSha256": manifest_digest,
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
  # This selftest is not a workflow run, so the ambient GITHUB_WORKFLOW_REF is
  # not the ref its fixtures were "built" by. `generate` compares each leg's
  # recorded workflowRef against that variable whenever it is non-empty, and
  # inside GitHub Actions it is *always* non-empty — so the fixture's fixed
  # workflowRef could never match, and this selftest passed on every developer
  # machine while failing in CI. Both workflows run it through the release
  # policy, so the first push would have failed the gates job for a reason
  # nothing local could reproduce.
  #
  # Scrubbed rather than adopted: making the fixture copy the ambient value
  # would make the comparison compare a thing with itself, which is the check
  # not running. Its real exercise belongs with the port, where the run
  # identity is an injected value rather than an environment variable.
  unset GITHUB_WORKFLOW_REF

  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  rc_selftest_begin "gen-release-manifest" "$work"

  commit=1111111111111111111111111111111111111111
  build_dist() {
    d=$1
    shift
    rm -rf "$d"
    mkdir -p "$d"
    for target in "$@"; do
      printf 'binary for %s\n' "$target" > "$d/tl-$target"
      # The same shape the build leg writes. Kept complete on purpose: a
      # fixture that omits fields the generator requires would make every
      # refusal row pass for the wrong reason.
      python3 -c '
import hashlib, json, sys
path, target, commit, tier, toolchain, manifest_digest, out = sys.argv[1:8]
with open(path, "rb") as handle:
    digest = hashlib.sha256(handle.read()).hexdigest()
json.dump({"target": target, "sha256": digest, "commit": commit, "tier": tier,
           "runner": "ubuntu-latest", "runnerOs": "Linux", "runnerArch": "X64",
           "containerImage": "", "toolchain": toolchain,
           "lakeManifestSha256": manifest_digest,
           "workflowRef": "DmitryKorolev/tl/.github/workflows/release.yml@refs/tags/v1.2.3",
           "runId": "42", "runAttempt": "1"},
          open(out, "w"), indent=2, sort_keys=True)
' "$d/tl-$target" "$target" "$commit" "$(rc_target_tier "$target")" \
  "$(tr -d ' \t\r\n' < "$repo_root/lean-toolchain")" \
  "$(rc_sha256_of "$repo_root/lake-manifest.json")" \
  "$d/build-metadata-$target.json"
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
  #
  # Through the harness, not bare. Unwrapped and with its output discarded, a
  # failure here aborted the entire selftest under `set -eu` — no failing row,
  # no count, no remedy line, and the diagnostic sent to /dev/null. A selftest
  # that cannot report its own failure is the same defect as a gate that cannot
  # fail, one level up.
  pre="$work/pre.json"
  rc_expect_status 0 "a prerelease manifest is written at all" \
    "$0" "$work/dist" v1.2.3-rc.1 "$commit" "$pre"
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
  an_optional=$(rc_targets best-effort | cut -d' ' -f1)
  printf 'replaced\n' > "$tampered/tl-$a_target"
  rc_expect_output 1 "not the one that was built" \
    "a binary that differs from what its build leg recorded is refused" \
    "$0" "$tampered" v1.2.3 "$commit" "$work/o1"

  # An unreadable targets file must stop the generator, not describe a release
  # with no targets. The manifest is signed, so an empty required list is not a
  # smaller claim — it is a signed claim that nothing was checked, and every
  # per-leg build-metadata comparison below is skipped along with it.
  rc_expect_output 1 "could not read the release-blocking targets" \
    "an unreadable targets file refuses rather than describing an empty release" \
    env RC_TARGETS_FILE="$work/no-such-targets.json" "$0" "$tampered" v1.2.3 "$commit" "$work/o-notargets"
  rc_note "$([ ! -e "$work/o-notargets" ] && echo 0 || echo 1)" \
    "the refused run wrote no manifest at all"

  # The evidence must be *mandatory*. Written as "check it when the file
  # happens to exist", deleting the metadata published every binary with
  # "build": null and no comparison at all — the check was satisfied by
  # removing what it checks.
  nometa="$work/nometa"
  # shellcheck disable=SC2086
  build_dist "$nometa" $all_targets
  rm "$nometa"/build-metadata-*.json
  rc_expect_output 1 "is not. Every published target" \
    "a published binary with no build metadata is refused, not published with a null record" \
    "$0" "$nometa" v1.2.3 "$commit" "$work/o-nometa"
  rc_note "$([ ! -e "$work/o-nometa" ] && echo 0 || echo 1)" \
    "no manifest is written when the evidence is missing"

  noaudit="$work/noaudit"
  # shellcheck disable=SC2086
  build_dist "$noaudit" $all_targets
  rm "$noaudit"/link-audit-*.txt
  rc_expect_output 1 "link-audit" "a published binary with no link audit is refused" \
    "$0" "$noaudit" v1.2.3 "$commit" "$work/o-noaudit"

  # A record that exists but is hollow must not pass by comparing None to None.
  for field in target sha256 commit tier runner toolchain lakeManifestSha256 workflowRef runId; do
    hollow="$work/hollow-$field"
    # shellcheck disable=SC2086
    build_dist "$hollow" $all_targets
    python3 -c '
import json, sys
path, field = sys.argv[1], sys.argv[2]
data = json.load(open(path))
del data[field]
json.dump(data, open(path, "w"), indent=2, sort_keys=True)
' "$hollow/build-metadata-$a_target.json" "$field"
    rc_expect_output 1 "has no '$field'" "a record missing $field is refused" \
      "$0" "$hollow" v1.2.3 "$commit" "$work/o-hollow-$field"
  done

  # Crossed, mismatched and foreign records.
  crossed="$work/crossed"
  # shellcheck disable=SC2086
  build_dist "$crossed" $all_targets
  python3 -c '
import json, sys
path = sys.argv[1]
data = json.load(open(path))
data["target"] = sys.argv[2]
json.dump(data, open(path, "w"), indent=2, sort_keys=True)
' "$crossed/build-metadata-$a_target.json" "$an_optional"
  rc_expect_output 1 "crossed between legs" "a record naming another target is refused" \
    "$0" "$crossed" v1.2.3 "$commit" "$work/o-crossed"

  drifted_tc="$work/drifted-toolchain"
  # shellcheck disable=SC2086
  build_dist "$drifted_tc" $all_targets
  python3 -c '
import json, sys
path = sys.argv[1]
data = json.load(open(path))
data["toolchain"] = "leanprover/lean4:v0.0.0"
json.dump(data, open(path, "w"), indent=2, sort_keys=True)
' "$drifted_tc/build-metadata-$a_target.json"
  rc_expect_output 1 "pinned toolchain" "a leg that built with another toolchain is refused" \
    "$0" "$drifted_tc" v1.2.3 "$commit" "$work/o-tc"

  tworuns="$work/tworuns"
  # shellcheck disable=SC2086
  build_dist "$tworuns" $all_targets
  python3 -c '
import json, sys
path = sys.argv[1]
data = json.load(open(path))
data["runId"] = "99"
json.dump(data, open(path, "w"), indent=2, sort_keys=True)
' "$tworuns/build-metadata-$an_optional.json"
  rc_expect_output 1 "not produced by one run" \
    "records from two different workflow runs are refused" \
    "$0" "$tworuns" v1.2.3 "$commit" "$work/o-tworuns"

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
  partial="$work/partial"
  # shellcheck disable=SC2086
  # Word splitting is the point: rc_targets prints a space-separated list and
  # build_dist takes one target per argument.
  # shellcheck disable=SC2046
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
