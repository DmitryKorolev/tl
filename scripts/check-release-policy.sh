#!/bin/sh
# The whole release policy, as one command.
#
#   scripts/check-release-policy.sh                     everything runnable here
#   scripts/check-release-policy.sh --strict            …and no gate may be skipped
#   scripts/check-release-policy.sh --tag v0.1.0        …and this is a tag run
#   scripts/check-release-policy.sh --profile release   the v0.1 release path only
#   scripts/check-release-policy.sh --list              name the gates and exit
#
# `--tag` states that this is a release run rather than a working-tree check.
# It no longer gates tag agreement: that moved to `tlrelease version-consistency
# --tag`, which the release workflow's gates job runs on the tagged commit
# before the build matrix, because it needs a Lean toolchain this job does not
# have. What `--tag` still decides here is the development-stamp gate, which a
# tag run is expected to fail: a tag stamps on purpose.
#
# There were two definitions of "the release policy". `ci.yml` ran nine gates
# on every commit; `release.yml`'s `gates` job ran four and described itself as
# re-running the correctness gates against the tagged commit. The installer,
# the artifact verifier, the npm packages and the Homebrew formula were
# therefore never exercised on the commit actually being released — which is
# the one commit where it matters, because that is where a stale gate becomes a
# published artifact.
#
# One list, called identically from both workflows. A gate added here is a gate
# both of them get; there is no second place to remember.
#
# `--profile` is the one thing they do not share, and it is not a narrowing of
# convenience. `ci` (the default) additionally runs scripts/check-channel-policy.sh,
# whose five gates invoke npm, python3 and ruby to keep the deferred npm and
# Homebrew machinery from rotting while it waits. `release` is the profile the
# release workflow runs, and ADR-0026's v0.1 dependency boundary forbids those
# three interpreters anywhere the GitHub-only release path can reach. So a
# deferred channel's gates are *absent* from the release profile rather than
# skipped: a skip is a report about this run, and absence is a statement about
# the release.
#
# `--strict` refuses to skip a gate whose tool is missing. Locally, `ruby` or
# `actionlint` may legitimately be absent and the run says so; in CI their
# absence is a broken job, not a smaller policy. A skipped gate never counts as
# a passing one either way — the summary separates them and `--strict` turns
# the distinction into an exit code.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
cd "$repo_root"

RC_POLICY_STRICT=0
tag=''
list=0
profile=ci
while [ "$#" -gt 0 ]; do
  case $1 in
    --strict) RC_POLICY_STRICT=1; shift ;;
    --list) list=1; shift ;;
    --profile)
      [ "$#" -ge 2 ] || {
        echo "check-release-policy: --profile takes ci or release" >&2
        exit 2
      }
      case $2 in
        ci|release) profile=$2 ;;
        *)
          echo "check-release-policy: unknown profile '$2' — pass ci (every gate) or release (the v0.1 release path, without the deferred channels')" >&2
          exit 2
          ;;
      esac
      shift 2
      ;;
    --tag)
      [ "$#" -ge 2 ] || {
        echo "check-release-policy: --tag takes the tag to check, for example --tag v0.1.0" >&2
        exit 2
      }
      tag=$2
      shift 2
      ;;
    *)
      echo "check-release-policy: unknown argument '$1' — pass --strict, --tag <tag>, --profile <ci|release>, --list, or nothing" >&2
      exit 2
      ;;
  esac
done

RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

# The development-stamp check regenerates Tl/Build/Stamp.lean and diffs it.
# Three places state as fact that the checked-in copy is the *development*
# stamp; nothing but this enforces it, and a stamped copy swept in by
# `git commit -a` would make every build from that tree report an
# exact-correspondence claim that is false while passing the whole suite.
development_stamp_is_checked_in() {
  ./scripts/gen-build-provenance.sh >/dev/null
  if ! git diff --exit-code -- Tl/Build/Stamp.lean; then
    echo "::error::Tl/Build/Stamp.lean differs from what scripts/gen-build-provenance.sh produces. Either a stamped copy was committed (run the generator with no arguments and commit the result), or lean-toolchain / lake-manifest.json changed without regenerating it." >&2
    return 1
  fi
}

# -S warning is the floor: the info level is advisory style over
# script-controlled temp paths, and admitting it would mean a wave of
# suppressions rather than better code. Anything genuinely wrong there is fixed
# at the site. The configuration lives in .shellcheckrc so an editor and a
# developer's own `shellcheck` see the same rules this gate does.
shellcheck_all() {
  # Every tracked file that is a shell script by shebang or by extension, found
  # rather than listed — a list would silently stop covering a new script, and
  # a gate that quietly narrows is the failure mode this whole file exists to
  # prevent.
  files=$(git ls-files -- '*.sh' 'install.sh' 'npm/tl/bin/tl' 2>/dev/null)
  if [ -z "$files" ]; then
    echo "::error::found no shell files to analyse — the discovery pattern in shellcheck_all matches nothing, so this gate would pass over everything." >&2
    return 1
  fi
  # shellcheck disable=SC2086
  shellcheck -S warning $files
}

if [ "$list" -eq 1 ]; then
  cat <<'GATES'
release-policy gates, in order:
  task-id lint selftest               scripts/check-task-ids.sh --selftest
  task-id leakage                     scripts/check-task-ids.sh
  shell static analysis               shellcheck over every tracked shell file
  build-provenance generator selftest scripts/gen-build-provenance.sh --selftest
  artifact verifier selftest          scripts/verify-release-artifacts.sh --selftest
  release runtime boundary selftest   scripts/check-release-runtimes.sh --selftest
  installer selftest                  sh install.sh --selftest
  workflow lint                       actionlint .github/workflows/*.yml (needs actionlint)
  the checked-in build stamp is       git diff after regenerating it
    the development stamp             (skipped with --tag: a tag run stamps on purpose)
GATES
  if [ "$profile" = ci ]; then
    printf '  deferred-channel gates              scripts/check-channel-policy.sh\n\n'
    ./scripts/check-channel-policy.sh --list
    printf '\n'
  else
    cat <<'ABSENT'

not in the release profile, and absent rather than skipped:
  the deferred-channel gates          scripts/check-channel-policy.sh --list
                                      — each invokes npm, python3 or ruby, and
                                      ADR-0026's v0.1 dependency boundary
                                      forbids those on the release path
ABSENT
  fi
  cat <<'ELSEWHERE'
covered by a different required gate, and deliberately not run here:
  the SBOM generator                  `lake exe tltest`, over Tests/ReleaseToolTests.lean
                                      — it is `tlrelease sbom`, and this script
                                      answers in seconds without a toolchain
  the v0.1 dependency boundary        `tlrelease dependency-boundary`, in the
                                      job that has a Lean toolchain; this script
                                      is itself one of the entry points it reads
  the same boundary at runtime        `scripts/check-release-runtimes.sh`, which
                                      runs this script's release profile with
                                      the six runtimes shimmed to fail — so it
                                      wraps this one rather than running inside
                                      it
ELSEWHERE
  exit 0
fi

rc_policy_begin "release policy: $(if [ -n "$tag" ]; then echo "tag $tag"; else echo "working tree"; fi), $profile profile$(if [ "$RC_POLICY_STRICT" -eq 1 ]; then echo ", strict"; fi)"

# The task-id lint. ci.yml runs it as its own job so a lint failure and a build
# failure are separately visible, but it belongs in "the whole release policy"
# too — without it this script can be green on a commit CI will reject, which
# is exactly what happened to the commit that introduced this file.
rc_gate "task-id lint selftest" ./scripts/check-task-ids.sh --selftest
rc_gate "task-id leakage" ./scripts/check-task-ids.sh

# Each gate proves it can still fail before its silence is believed, then runs.
# The selftest/real pairing is the discipline the identity gate established;
# applying it uniformly is most of why this file exists.
# Every shell file in the repository, not only the snippets embedded in
# workflows. actionlint runs ShellCheck over `run:` blocks and nothing else, so
# install.sh — the file users pipe into a shell — and the release scripts had
# no static analysis at all. It found two real defects on the commit that added
# this gate: a `[ -e "$dir/.tl.install."* ]` test that misbehaves on more than
# one match, and a comment beginning with the tool's own name, which ShellCheck
# reads as a malformed directive and treats as an error.
rc_tool_gate "shell static analysis" --tool shellcheck -- shellcheck_all

rc_gate "build-provenance generator selftest" ./scripts/gen-build-provenance.sh --selftest
# Version consistency and embedded-copy drift are `tlrelease
# version-consistency` and `tlrelease embedded-copies`, and the release
# workflow's gates job runs both against the tagged commit before the build
# matrix. They are not gates here for the same reason as the rest: this script
# runs in a job with no Lean toolchain by design.
#
# The SBOM generator, the release manifest, each build leg's record, the
# signing-identity policy and the external-prerequisite audit are `tlrelease
# sbom`, `manifest`/`manifest-verify`, `build-metadata`, `identity-check` and
# `prereqs`, and their refusals are covered by
# Tests/ReleaseToolTests.lean under `lake exe tltest` — a required gate on the
# same commit in ci.yml and in the release workflow's own gates job. They are
# not invoked here because this script runs in a job with no Lean toolchain, by
# design: it answers in seconds rather than after the build matrix. Named in
# --list under what a different gate covers, so a reader asking what the policy
# covers is not told those are uncovered.

# The code path behind VERIFYING.md, the installer, and the release workflow's
# own pre-publish check. Its refusal paths are the whole point of it.
rc_gate "artifact verifier selftest" ./scripts/verify-release-artifacts.sh --selftest

# The PATH-shim arm of the v0.1 dependency boundary proves it can fire here,
# and only that. The arm itself runs the whole release profile under the shims,
# so running it as a gate *inside* that profile would run the profile twice;
# what belongs here is the evidence that its shims still refuse, since a shim
# that silently stopped shadowing would make a clean release path mean nothing.
rc_gate "release runtime boundary selftest" ./scripts/check-release-runtimes.sh --selftest

# The installer is piped into a shell by people who cannot inspect it first, so
# a check that silently stopped running would be invisible to exactly the users
# who most depend on it.
rc_gate "installer selftest" sh install.sh --selftest

# A workflow cannot validate itself: if GitHub refuses to load release.yml,
# nothing runs to say so, and the failure surfaces only when someone pushes a
# tag. actionlint parses both workflows — expressions, unknown keys, runner
# labels, and the embedded shell through shellcheck.
#
# Two tools, and the second one's absence is not the first one's. actionlint
# shells out to ShellCheck for every `run:` block and silently does without it
# when it is absent — so on a machine with actionlint and no ShellCheck this
# gate passes having checked only the YAML. That is how three real shell defects
# in these two workflows survived: the runner has ShellCheck preinstalled, so the
# gate would have failed in CI while passing everywhere it was tried. Naming the
# shortfall is the difference between a gate that is not running and a gate that
# is running clean.
#
# (Capitalised deliberately. A comment whose first word after `#` is the
# lowercase tool name is parsed as a ShellCheck *directive*, and an unparseable
# directive is an error that fails the file — which is what this very comment
# used to do.)
rc_tool_gate "workflow lint" \
  --tool actionlint \
  --tool shellcheck \
  --why "actionlint is present but shellcheck is not, and without it actionlint checks the YAML only" \
  -- actionlint -color .github/workflows/ci.yml .github/workflows/release.yml

if [ -n "$tag" ]; then
  echo "── the checked-in build stamp is the development stamp: not applicable on a tag run (the release workflow stamps the tagged commit on purpose)"
else
  rc_gate "the checked-in build stamp is the development stamp" development_stamp_is_checked_in
fi

# Last, and only under the ci profile. One gate rather than five, because the
# channel policy counts and reports its own; what this file decides is whether
# the deferred channels are in scope at all.
if [ "$profile" = ci ]; then
  if [ "$RC_POLICY_STRICT" -eq 1 ]; then
    rc_gate "deferred-channel gates" ./scripts/check-channel-policy.sh --strict
  else
    rc_gate "deferred-channel gates" ./scripts/check-channel-policy.sh
  fi
fi

rc_policy_end "release policy"
