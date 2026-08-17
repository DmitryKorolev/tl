# shellcheck shell=sh
# Deferred-channel helpers: the npm and Homebrew machinery, and nothing the
# v0.1 release path reaches. Sourced, never executed.
#
#   . "$(dirname -- "$0")/lib/channel-common.sh"
#
# Split out of release-common.sh, which install.sh, the artifact verifier and
# the release workflow all source. Everything here reads a JSON document with
# `python3`, and ADR-0026's v0.1 dependency boundary forbids python, ruby, node,
# npm and brew anywhere the GitHub-only release path can reach. Keeping these
# three helpers in the shared library would have put an interpreter one
# `.`-include away from the installer forever, and the boundary gate would have
# had to reason about which *functions* a script calls rather than which files
# it reads.
#
# So the split is the enforcement: this file is named in the boundary gate's
# deferred set, the three npm scripts that source it are named there too, and
# none of them is reachable from install.sh, scripts/verify-release-artifacts.sh, the
# release profile of the policy, or the release workflow's enabled jobs. When a
# channel is enabled its scripts return to the release path — and these helpers
# with them, which is the point at which `tlrelease` has to own these reads.
#
# It is sourced after release-common.sh but needs nothing from it: the root
# computation below came here with the two paths that were its only readers, so
# neither library defines a variable the other one reads — which is a shape no
# static analysis can see through, at either end.

# The repository root, derived from the library directory rather than from the
# caller's working directory: the scripts that source it are run from CI, from a
# checkout, and from inside their own throwaway fixtures. `$0` is the sourcing
# script, not this file, which is why the caller passes its library path in
# `RC_LIB_SELF`; both libraries live in the same directory, so either one's path
# answers the same question.
RC_LIB_DIR=$(CDPATH='' cd -- "$(dirname -- "${RC_LIB_SELF:-$0}")" && pwd -P)
case $RC_LIB_DIR in
  */scripts/lib) RC_ROOT=$(CDPATH='' cd -- "$RC_LIB_DIR/../.." && pwd -P) ;;
  */scripts) RC_ROOT=$(CDPATH='' cd -- "$RC_LIB_DIR/.." && pwd -P) ;;
  *) RC_ROOT=$RC_LIB_DIR ;;
esac

# ---------------------------------------------------------------------------
# Targets and ADR-0006 support tiers, from release/targets.json
#
# The tier split decides whether a missing binary is a warning or a refusal, and
# it was decided independently in npm-pack.sh, the Homebrew generator and the
# release workflow. One source now, so "Supported" cannot mean three things —
# and the Homebrew half no longer reads this file at all: `tlrelease` takes the
# tier from the signed manifest's own target rows.
# ---------------------------------------------------------------------------

RC_TARGETS_FILE=${RC_TARGETS_FILE:-"$RC_ROOT/release/targets.json"}

# rc_targets [tier] — space-separated target names, in file order. With no
# argument, every target; with `supported` or `best-effort`, that tier only.
rc_targets() {
  rc__tier=${1-}
  [ -f "$RC_TARGETS_FILE" ] || {
    echo "$RC_TARGETS_FILE not found — it is the one place the distributed targets and their ADR-0006 tiers are recorded, and every consumer reads it rather than repeating the list." >&2
    return 1
  }
  command -v python3 >/dev/null 2>&1 || {
    echo "python3 not found — it reads release/targets.json. A text scrape would silently return an empty target list, which reads as 'nothing to publish' rather than as a broken tool." >&2
    return 1
  }
  python3 -c '
import json, sys
path, tier = sys.argv[1], sys.argv[2]
with open(path, encoding="utf-8") as handle:
    data = json.load(handle)
names = [t["target"] for t in data["targets"] if not tier or t["tier"] == tier]
if not names:
    sys.exit(f"release/targets.json lists no targets for tier {tier!r}")
print(" ".join(names))
' "$RC_TARGETS_FILE" "$rc__tier"
}

RC_PLAN_FILE=${RC_PLAN_FILE:-"$RC_ROOT/release/plan.json"}

# rc_channel_state <channel> — print `enabled`, or `deferred <version>`.
# Returns non-zero, having explained itself on stderr, when the plan cannot be
# read; the caller must not treat that as "off". A channel this release defers
# needs none of its prerequisites, and a channel nobody could ask about is a
# different answer from one deliberately switched off.
rc_channel_state() {
  [ -f "$RC_PLAN_FILE" ] || {
    echo "$RC_PLAN_FILE not found — it is the one place the channels a release publishes through are recorded, and every consumer reads it rather than assuming." >&2
    return 1
  }
  command -v python3 >/dev/null 2>&1 || {
    echo "python3 not found — it reads release/plan.json. A text scrape would silently report a channel as off, which reads as 'deliberately deferred' rather than as a broken tool." >&2
    return 1
  }
  python3 -c '
import json, sys
path, channel = sys.argv[1], sys.argv[2]
try:
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    rows = [row for row in data["channels"] if row.get("channel") == channel]
except (OSError, ValueError, KeyError, TypeError) as error:
    sys.exit(f"{path} could not be read as a release plan ({error}).")
if len(rows) != 1:
    sys.exit(f"{path} has {len(rows)} rows for the {channel!r} channel; it must have exactly one.")
row = rows[0]
if not isinstance(row.get("enabled"), bool):
    sys.exit(f"{path} does not say whether the {channel!r} channel is enabled.")
if row["enabled"]:
    print("enabled")
else:
    planned = row.get("plannedFor")
    if not isinstance(planned, str) or not planned:
        sys.exit(f"{path} defers the {channel!r} channel without naming the release it is planned for.")
    print(f"deferred {planned}")
' "$RC_PLAN_FILE" "$1"
}

# rc_target_tier <target> — `supported`, `best-effort`, or a refusal.
rc_target_tier() {
  python3 -c '
import json, sys
path, want = sys.argv[1], sys.argv[2]
with open(path, encoding="utf-8") as handle:
    data = json.load(handle)
for entry in data["targets"]:
    if entry["target"] == want:
        print(entry["tier"])
        break
else:
    sys.exit(f"{want!r} is not a target in release/targets.json; add it there rather than special-casing it here")
' "$RC_TARGETS_FILE" "$1"
}

# rc_target_is_required <target> — true for the release-blocking tier.
rc_target_is_required() {
  [ "$(rc_target_tier "$1")" = supported ]
}
