#!/bin/sh
# The gates for the distribution channels this release defers.
#
#   scripts/check-channel-policy.sh            everything runnable here
#   scripts/check-channel-policy.sh --strict   …and no gate may be skipped
#   scripts/check-channel-policy.sh --list     name the gates and exit
#   scripts/check-channel-policy.sh --list-names  one gate name per line
#   scripts/check-channel-policy.sh --ruby-only   just that gate's body
#
# These run on every commit — `scripts/check-release-policy.sh` calls this file
# under its default profile — whether or not release/plan.json publishes through
# npm or Homebrew. A deferred channel whose generators stopped being exercised
# would rot until the release that enabled it, and that release is the worst
# moment to discover it (ADR-0006).
#
# They are a separate file because they are the gates the v0.1 release path may
# not run. Each one invokes npm or ruby — the npm scripts stage and install real
# packages, and nothing but ruby can tell whether a rendered formula parses —
# and ADR-0026's dependency boundary forbids both anywhere the GitHub-only
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
list_names=0
only=''
while [ "$#" -gt 0 ]; do
  case $1 in
    --strict) RC_POLICY_STRICT=1; shift ;;
    --list) list=1; shift ;;
    --list-names) list_names=1; shift ;;
    --ruby-only) only=ruby; shift ;;
    *)
      echo "check-channel-policy: unknown argument '$1' — pass --strict, --list, --list-names, --ruby-only, or nothing" >&2
      exit 2
      ;;
  esac
done

# The gate names, in the order the run below performs them; the run compares its
# own count against this, so the two cannot drift apart silently.
gate_names() {
  cat <<'NAMES'
npm packaging over the real client
the rendered formulae parse
NAMES
}

if [ "$list_names" -eq 1 ]; then
  gate_names
  exit 0
fi

if [ "$list" -eq 1 ]; then
  cat <<'GATES'
deferred-channel gates, in order:
  npm packaging over the real client  tlrelease npm-selftest --root .   (needs npm)
  the rendered formulae parse         ruby -c over Formula/tl.rb and the
                                      Tests/fixtures/homebrew rows      (needs ruby)
GATES
  exit 0
fi

# Nothing else on a non-macOS machine evaluates the formulae. Real Homebrew is
# the acceptance authority and the `homebrew-formula` job is where it runs, so
# this is an early signal rather than the verdict: a syntax error would
# otherwise pass every gate a developer can run and surface on the macOS job.
#
# All four rendered formulae, not only the tracked one. They come out of one
# renderer, so a break in the placeholder is a break in the rest — but the three
# fixtures are the shapes with a dropped block, a prerelease version line and a
# full pin set, and checking only the file that happens to be tracked would be
# checking the least varied of them.
formulae_parse() {
  # Found rather than listed, and refused when it finds nothing: a glob that
  # matched no files would leave this gate reporting that it had checked the
  # fixtures when it had run `ruby -c` on one file.
  fixtures=$(git ls-files -- 'Tests/fixtures/homebrew/*.rb')
  if [ -z "$fixtures" ]; then
    echo "::error::found no rendered formula fixtures under Tests/fixtures/homebrew — this gate would report checking them while checking nothing." >&2
    return 1
  fi
  ruby -c Formula/tl.rb >/dev/null || return 1
  for fixture in $fixtures; do
    ruby -c "$fixture" >/dev/null || return 1
  done
  echo "Formula/tl.rb and $(printf '%s\n' "$fixtures" | wc -l | tr -d ' ') rendered fixtures parse as Ruby"
}

# The npm gate, run against an ambient configuration that would break it.
#
# `tlrelease npm-selftest` pins npm's cache and all three of its config layers
# to a scratch directory, because a gate whose verdict moves with the
# developer's `~/.npm` reports on the machine rather than on the code. That
# pinning was once appended by each call site, and one of them did not append
# it: every `npm pack --dry-run --json` — the rows that read which files a
# package would actually publish — ran against the caller's real cache and
# npmrc. Nothing showed it, because an ambient cache normally works.
#
# So the run is handed a HOME whose `.npmrc` names a cache that cannot exist:
# its parent is a regular file, so creating it is ENOTDIR on every platform
# rather than a fact about how one of them treats /proc. An invocation that
# stays inside the pinned configuration never reads this file. One that escapes
# fails, here, on the gate — which is what makes the isolation a checked
# property rather than a claim in a comment.
npm_packaging() {
  npm_home=$(mktemp -d "${TMPDIR:-/tmp}/tl-npm-ambient.XXXXXX") || return 1
  : > "$npm_home/not-a-directory"
  cat > "$npm_home/.npmrc" <<NPMRC
cache=$npm_home/not-a-directory/cache
registry=http://127.0.0.1:9/tl-must-not-reach-a-registry/
NPMRC
  npm_status=0
  HOME=$npm_home ./.lake/build/bin/tlrelease npm-selftest --root . || npm_status=$?
  rm -rf "$npm_home"
  return "$npm_status"
}

if [ -n "$only" ]; then
  case $only in
    ruby) formulae_parse ;;
    *)
      # The arm that must exist even while every flag has one. `case` with no
      # match runs nothing and leaves `$?` at the last command's status, so
      # `exit $?` here would report a pass for a run that performed no gate —
      # and the caller asking for a single gate is the typed registry, which
      # would then be naming an invocation that checks nothing. A flag added to
      # the parser and not to this dispatch fails loudly instead.
      echo "check-channel-policy: '$only' names no gate in this dispatch, so this run would report a pass having run nothing. Add the arm beside the flag that sets it." >&2
      exit 2
      ;;
  esac
  exit $?
fi

rc_policy_begin "channel policy: npm, Homebrew$(if [ "$RC_POLICY_STRICT" -eq 1 ]; then echo ", strict"; fi)"

# Each gate states the tool it needs and `rc_tool_gate` decides the rest —
# present or absent, strict or not, passed or failed. Stating it per gate rather
# than wrapping three in one `command -v` also stops a fourth npm gate from
# landing inside a branch written for the three above it.
# What only the real client can answer: which files a package actually
# contains, the modes they are published with, where an optional dependency
# lands, and whether the bin symlink npm creates execs the platform binary.
# The channel's own decisions — staging, comparison, ordering, publication —
# are decided by `tlrelease` and covered against a stub in the ordinary suite,
# which is what lets them run where npm may not be reached at all.
rc_tool_gate "npm packaging over the real client" --tool npm -- npm_packaging

rc_tool_gate "the rendered formulae parse" --tool ruby -- formulae_parse

listed=$(gate_names | wc -l | tr -d ' ')
ran=$((RC_POLICY_PASSED + RC_POLICY_FAILED + RC_POLICY_SKIPPED))
if [ "$listed" -ne "$ran" ]; then
  echo "::error::this run performed $ran gate(s) and --list-names names $listed. One of them was edited without the other." >&2
  exit 1
fi

rc_policy_end "channel policy"
