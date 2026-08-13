#!/bin/sh
# The v0.1 release path, run with the runtimes it may not use shimmed to fail.
#
#   scripts/check-release-runtimes.sh              run the release profile under shims
#   scripts/check-release-runtimes.sh --tag v0.1.0 …and tell it this is a tag run
#   scripts/check-release-runtimes.sh --selftest   prove the shims can fire
#
# The second of ADR-0026's two enforcement arms. The first,
# `tlrelease dependency-boundary`, reads the reachable scripts and refuses on an
# invocation it can see. What it cannot see is a command name held in a
# variable, one inside the string `sh -c` runs, or a tool something further down
# shells out to on its own. This arm sees anything that actually executes,
# whatever it is spelled like — and, symmetrically, sees nothing about a branch
# this run did not take. Neither arm covers what the other does.
#
# What runs under the shims is `check-release-policy.sh --profile release`,
# which is the whole v0.1 policy: the installer selftest and the artifact
# verifier selftest are gates inside it, so both are exercised here without a
# second list of what to run. The deferred channels' gates are not in that
# profile — they invoke npm, python3 and ruby by design — and they keep running
# on every commit under the ci profile, where these shims are not on PATH.
#
# The shims are proved to fire before the run is believed. A shim directory that
# was not on PATH, or a shim that was not executable, would make every release
# path look clean for the same reason a genuinely clean one does; that is the
# silently-green failure this project treats as the worst kind, so each of the
# six is invoked and required to fail first.
set -eu

self=$0
script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
cd "$repo_root"

RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

selftest=0
tag=''
while [ "$#" -gt 0 ]; do
  case $1 in
    --selftest) selftest=1; shift ;;
    --tag)
      [ "$#" -ge 2 ] || {
        echo "check-release-runtimes: --tag takes the tag, for example --tag v0.1.0" >&2
        exit 2
      }
      tag=$2
      shift 2
      ;;
    *)
      echo "check-release-runtimes: unknown argument '$1' — pass --tag <tag>, --selftest, or nothing" >&2
      exit 2
      ;;
  esac
done

# The same six ADR-0026 names `tlrelease dependency-boundary` refuses, and the
# duplication is deliberate: one list is the lexical scan's and this one is the
# runtime's, and a release must not be able to lose a name from both at once by
# editing one file. `tlrelease dependency-boundary --root .` is what compares
# them — its own findings are stated in these terms — and the boundary tests
# name all six on the Lean side.
FORBIDDEN='python python3 ruby brew node npm'

# write_shims <dir> — a failing stand-in for each forbidden command, first on
# PATH. Each says which command was invoked and where the rule is, because the
# reader of this failure is looking at a release log and needs to know it is a
# policy refusal rather than a broken runner.
write_shims() {
  mkdir -p "$1"
  for command in $FORBIDDEN; do
    cat > "$1/$command" <<SHIM
#!/bin/sh
echo "check-release-runtimes: the v0.1 release path invoked \\\`$command\\\`, which ADR-0026's dependency boundary forbids: an operator's machine is not a GitHub runner, and a release must not stop for a runtime it does not publish through. Move the decision into tlrelease, or put the step behind the channel that owns that runtime." >&2
exit 97
SHIM
    chmod +x "$1/$command"
  done
}

# prove_shims_fire <dir> — every shim, invoked. Reported as rows so a partial
# failure names the command rather than the directory.
prove_shims_fire() {
  for command in $FORBIDDEN; do
    rc_expect_output 97 "dependency boundary forbids" \
      "the $command shim fires when it is invoked" \
      env PATH="$1:$PATH" "$command" --version
  done
}

scratch=$(mktemp -d "${TMPDIR:-/tmp}/tl-release-runtimes.XXXXXX")
cleanup() { rm -rf "$scratch"; }
trap cleanup EXIT INT HUP TERM

shims="$scratch/shims"
write_shims "$shims"

if [ "$selftest" -eq 1 ]; then
  rc_selftest_begin "check-release-runtimes" "$scratch"
  prove_shims_fire "$shims"
  # A script that reaches for one of them, the way a release step would: once
  # per command, and once for a command the shims do not shadow. The last row
  # is what stops the others from holding because the harness fails everything
  # it runs — and it is also the row that would catch shims that shadowed the
  # whole PATH instead of six names.
  #
  # The probe takes the command as an argument rather than naming one. That is
  # the shape the boundary gate can read, and it has to be: this file is on the
  # release path it guards, and a literal invocation here would be a finding
  # `tlrelease dependency-boundary` is right to report. Nothing in this script
  # invokes any of the six except through `$FORBIDDEN`, and never off the shims.
  probe="$scratch/probe.sh"
  cat > "$probe" <<'PROBE'
#!/bin/sh
"$1" --version >/dev/null 2>&1 || exit 3
exit 0
PROBE
  chmod +x "$probe"
  for command in $FORBIDDEN; do
    rc_expect_status 3 "a script reaching for $command fails under the shims" \
      env PATH="$shims:$PATH" "$probe" "$command"
  done
  rc_expect_status 0 "a script reaching for a command outside the list is unaffected" \
    env PATH="$shims:$PATH" "$probe" git
  # The argument surface of the three policy entry points. None of it decides a
  # release, but all of it decides whether the caller ran what they meant to:
  # a profile name that silently fell back, or an option consumed as a value,
  # produces a green run of something other than the gate that was asked for.
  # Status 2 throughout, kept distinct from a gate failure's 1.
  rc_expect_output 2 "unknown profile" \
    "an unknown policy profile is refused, not silently narrowed" \
    ./scripts/check-release-policy.sh --profile nonesuch
  rc_expect_output 2 "takes ci or release" \
    "a profile with no value is refused rather than binding the next argument" \
    ./scripts/check-release-policy.sh --profile
  rc_expect_output 2 "unknown argument" \
    "an unknown policy argument is refused" \
    ./scripts/check-release-policy.sh --evrything
  rc_expect_output 2 "takes the tag" \
    "a tag with no value is refused" \
    ./scripts/check-release-policy.sh --tag
  rc_expect_output 2 "unknown argument" \
    "an unknown channel-policy argument is refused" \
    ./scripts/check-channel-policy.sh --stirct
  rc_expect_output 2 "unknown argument" \
    "an unknown runtime-boundary argument is refused" \
    "$self" --selftets
  rc_expect_output 2 "takes the tag" \
    "a runtime-boundary tag with no value is refused" \
    "$self" --tag
  # Naming the gates is what makes the profiles reviewable, so it is a listed
  # behaviour rather than a debugging aid: the release profile must not name a
  # gate that invokes one of the six.
  rc_expect_output 0 "deferred-channel gates" \
    "the ci profile lists the deferred channels' gates" \
    ./scripts/check-release-policy.sh --list
  rc_expect_output 0 "absent rather than skipped" \
    "the release profile says those gates are absent, not skipped" \
    ./scripts/check-release-policy.sh --profile release --list
  rc_selftest_end "The shim mechanism is what makes a clean run of the release path mean anything; fix it before trusting one."
fi

echo "release runtimes: the v0.1 release path, with $FORBIDDEN shimmed to fail"
rc_capture_into "$scratch"
RC_FAILURES=0
prove_shims_fire "$shims"
if [ "$RC_FAILURES" -ne 0 ]; then
  echo "::error::check-release-runtimes: a shim did not fire, so a clean run below would prove nothing. Fix the shim directory before reading this gate's result." >&2
  exit 1
fi

echo "── the release profile of the policy, under the shims"
if [ -n "$tag" ]; then
  env PATH="$shims:$PATH" ./scripts/check-release-policy.sh --profile release --strict --tag "$tag"
else
  env PATH="$shims:$PATH" ./scripts/check-release-policy.sh --profile release --strict
fi

echo
echo "release runtimes: the v0.1 release path ran with none of $FORBIDDEN available"
