#!/bin/sh
# The whole release policy, as one command.
#
#   scripts/check-release-policy.sh                     everything runnable here
#   scripts/check-release-policy.sh --strict            …and no gate may be skipped
#   scripts/check-release-policy.sh --tag v0.1.0        …and this is a tag run
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
# `--tag` additionally checks that the tag agrees with every copy of the
# version, and drops the development-stamp check: the release workflow stamps
# `Tl/Build/Stamp.lean` on purpose before building, so on a tag run a modified
# stamp is the pipeline working rather than a mistake.
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

strict=0
tag=''
list=0
while [ "$#" -gt 0 ]; do
  case $1 in
    --strict) strict=1; shift ;;
    --list) list=1; shift ;;
    --tag)
      [ "$#" -ge 2 ] || {
        echo "check-release-policy: --tag takes the tag to check, for example --tag v0.1.0" >&2
        exit 2
      }
      tag=$2
      shift 2
      ;;
    *)
      echo "check-release-policy: unknown argument '$1' — pass --strict, --tag <tag>, --list, or nothing" >&2
      exit 2
      ;;
  esac
done

passed=0
failed=0
skipped=0
failed_names=''
skipped_names=''

# gate <name> <command>… — run one gate, remember the outcome, keep going.
# Deliberately not `set -e` on the first failure: a release-policy run that
# stops at the first problem makes the operator fix and re-run once per gate,
# and the gates are independent. The exit code at the end is what matters.
gate() {
  name=$1
  shift
  echo "── $name"
  if "$@"; then
    passed=$((passed + 1))
  else
    echo "::error::release-policy gate failed: $name" >&2
    failed=$((failed + 1))
    failed_names="$failed_names
  - $name"
  fi
}

# skip_gate <name> <reason> — a gate that could not run. Never silent, and
# never counted as a pass; fatal under --strict.
skip_gate() {
  if [ "$strict" -eq 1 ]; then
    echo "::error::release-policy gate cannot be skipped under --strict: $1 ($2)" >&2
    failed=$((failed + 1))
    failed_names="$failed_names
  - $1 (tool missing: $2)"
    return 0
  fi
  echo "── $1: SKIPPED — $2"
  skipped=$((skipped + 1))
  skipped_names="$skipped_names
  - $1 ($2)"
}

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
  npm package selftest                scripts/npm-pack.sh --selftest
  npm publisher selftest              scripts/npm-publish.sh --selftest
  npm bootstrap selftest              scripts/npm-bootstrap.sh --selftest
  installer selftest                  sh install.sh --selftest
  Homebrew formula generator selftest scripts/gen-homebrew-formula.sh --selftest
  the Homebrew formula parses         ruby -c Formula/tl.rb            (needs ruby)
  workflow lint                       actionlint .github/workflows/*.yml (needs actionlint)
  the checked-in build stamp is       git diff after regenerating it
    the development stamp             (skipped with --tag: a tag run stamps on purpose)

covered by a different required gate, and deliberately not run here:
  the SBOM generator                  `lake exe tltest`, over Tests/ReleaseToolTests.lean
                                      — it is `tlrelease sbom`, and this script
                                      answers in seconds without a toolchain
GATES
  exit 0
fi

echo "release policy: $(if [ -n "$tag" ]; then echo "tag $tag"; else echo "working tree"; fi)$(if [ "$strict" -eq 1 ]; then echo ", strict"; fi)"

# The task-id lint. ci.yml runs it as its own job so a lint failure and a build
# failure are separately visible, but it belongs in "the whole release policy"
# too — without it this script can be green on a commit CI will reject, which
# is exactly what happened to the commit that introduced this file.
gate "task-id lint selftest" ./scripts/check-task-ids.sh --selftest
gate "task-id leakage" ./scripts/check-task-ids.sh

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
if command -v shellcheck >/dev/null 2>&1; then
  gate "shell static analysis" shellcheck_all
else
  skip_gate "shell static analysis" "shellcheck is not on PATH"
fi

gate "build-provenance generator selftest" ./scripts/gen-build-provenance.sh --selftest
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
gate "artifact verifier selftest" ./scripts/verify-release-artifacts.sh --selftest

if command -v npm >/dev/null 2>&1; then
  gate "npm package selftest" ./scripts/npm-pack.sh --selftest
  # The publisher's refusals are the ones that matter most: an npm version
  # cannot be reissued, so a mistake here is not correctable after the fact.
  gate "npm publisher selftest" ./scripts/npm-publish.sh --selftest
  # The one-time bootstrap is the only manual step before the first release,
  # and the only one that publishes an immutable version by hand.
  gate "npm bootstrap selftest" ./scripts/npm-bootstrap.sh --selftest
else
  skip_gate "npm package selftest" "npm is not on PATH"
  skip_gate "npm publisher selftest" "npm is not on PATH"
  skip_gate "npm bootstrap selftest" "npm is not on PATH"
fi

# The installer is piped into a shell by people who cannot inspect it first, so
# a check that silently stopped running would be invisible to exactly the users
# who most depend on it.
gate "installer selftest" sh install.sh --selftest

gate "Homebrew formula generator selftest" ./scripts/gen-homebrew-formula.sh --selftest

if command -v ruby >/dev/null 2>&1; then
  # Nothing else evaluates the formula: a syntax error would pass every other
  # gate here and surface only when the tap tried to use it.
  gate "the Homebrew formula parses" ruby -c Formula/tl.rb
else
  skip_gate "the Homebrew formula parses" "ruby is not on PATH"
fi

if ! command -v actionlint >/dev/null 2>&1; then
  skip_gate "workflow lint" "actionlint is not on PATH"
elif ! command -v shellcheck >/dev/null 2>&1; then
  # actionlint shells out to ShellCheck for every `run:` block and silently
  # does without it when it is absent — so on a machine with actionlint and no
  # ShellCheck the gate passes having checked only the YAML. That is how three
  # real shell defects in these two workflows survived: the runner has it
  # preinstalled, so the gate would have failed in CI while passing everywhere
  # it was tried. Naming the shortfall is the difference between a gate that is
  # not running and a gate that is running clean.
  #
  # (Capitalised deliberately. A comment whose first word after `#` is the
  # lowercase tool name is parsed as a ShellCheck *directive*, and an
  # unparseable directive is an error that fails the file — which is what this
  # very comment used to do.)
  skip_gate "workflow lint" "actionlint is present but shellcheck is not, and without it actionlint checks the YAML only"
else
  # A workflow cannot validate itself: if GitHub refuses to load release.yml,
  # nothing runs to say so, and the failure surfaces only when someone pushes a
  # tag. actionlint parses both workflows — expressions, unknown keys, runner
  # labels, and the embedded shell through shellcheck.
  gate "workflow lint" actionlint -color .github/workflows/ci.yml .github/workflows/release.yml
fi

if [ -n "$tag" ]; then
  echo "── the checked-in build stamp is the development stamp: not applicable on a tag run (the release workflow stamps the tagged commit on purpose)"
else
  gate "the checked-in build stamp is the development stamp" development_stamp_is_checked_in
fi

echo
if [ "$failed" -ne 0 ]; then
  echo "release policy: $failed gate(s) failed, $passed passed, $skipped skipped.$failed_names" >&2
  echo "Nothing above is advisory: each of these gates stands between a defect and a published artifact." >&2
  exit 1
fi
if [ "$skipped" -ne 0 ]; then
  echo "release policy: $passed gate(s) passed, $skipped skipped.$skipped_names"
  echo "A skipped gate is not a passing one. CI and the release workflow run this with --strict, where a missing tool is a failure."
  exit 0
fi
echo "release policy: all $passed gates passed"
