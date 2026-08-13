#!/bin/sh
# The gates for the distribution channels this release defers.
#
#   scripts/check-channel-policy.sh            everything runnable here
#   scripts/check-channel-policy.sh --strict   …and no gate may be skipped
#   scripts/check-channel-policy.sh --list     name the gates and exit
#
# These run on every commit — `scripts/check-release-policy.sh` calls this file
# under its default profile — whether or not release/plan.json publishes through
# npm or Homebrew. A deferred channel whose generators stopped being exercised
# would rot until the release that enabled it, and that release is the worst
# moment to discover it (ADR-0006).
#
# They are a separate file because they are the gates the v0.1 release path may
# not run. Each one invokes npm, python3 or ruby — the npm scripts stage and
# install real packages, the formula generator reads release/targets.json with
# python3, and nothing but ruby can tell whether Formula/tl.rb parses — and
# ADR-0026's dependency boundary forbids all three anywhere the GitHub-only
# release path reaches. `--profile release` therefore does not skip these gates,
# it does not have them: this file is not among those it names, and
# `tlrelease dependency-boundary` never traverses into it.
#
# Enabling a channel moves its scripts back onto the release path. At that point
# these gates belong in the release profile too, and the interpreter reads
# behind them have to move into `tlrelease` first.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
cd "$repo_root"

RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

RC_POLICY_STRICT=0
list=0
while [ "$#" -gt 0 ]; do
  case $1 in
    --strict) RC_POLICY_STRICT=1; shift ;;
    --list) list=1; shift ;;
    *)
      echo "check-channel-policy: unknown argument '$1' — pass --strict, --list, or nothing" >&2
      exit 2
      ;;
  esac
done

if [ "$list" -eq 1 ]; then
  cat <<'GATES'
deferred-channel gates, in order:
  npm package selftest                scripts/npm-pack.sh --selftest    (needs npm)
  npm publisher selftest              scripts/npm-publish.sh --selftest (needs npm)
  npm bootstrap selftest              scripts/npm-bootstrap.sh --selftest (needs npm)
  Homebrew formula generator selftest scripts/gen-homebrew-formula.sh --selftest
  the Homebrew formula parses         ruby -c Formula/tl.rb             (needs ruby)
GATES
  exit 0
fi

rc_policy_begin "channel policy: npm, Homebrew$(if [ "$RC_POLICY_STRICT" -eq 1 ]; then echo ", strict"; fi)"

if command -v npm >/dev/null 2>&1; then
  rc_gate "npm package selftest" ./scripts/npm-pack.sh --selftest
  # The publisher's refusals are the ones that matter most: an npm version
  # cannot be reissued, so a mistake here is not correctable after the fact.
  rc_gate "npm publisher selftest" ./scripts/npm-publish.sh --selftest
  # The one-time bootstrap is the only manual step before the first release,
  # and the only one that publishes an immutable version by hand.
  rc_gate "npm bootstrap selftest" ./scripts/npm-bootstrap.sh --selftest
else
  rc_skip_gate "npm package selftest" "npm is not on PATH"
  rc_skip_gate "npm publisher selftest" "npm is not on PATH"
  rc_skip_gate "npm bootstrap selftest" "npm is not on PATH"
fi

rc_gate "Homebrew formula generator selftest" ./scripts/gen-homebrew-formula.sh --selftest

if command -v ruby >/dev/null 2>&1; then
  # Nothing else evaluates the formula: a syntax error would pass every other
  # gate here and surface only when the tap tried to use it.
  rc_gate "the Homebrew formula parses" ruby -c Formula/tl.rb
else
  rc_skip_gate "the Homebrew formula parses" "ruby is not on PATH"
fi

rc_policy_end "channel policy"
