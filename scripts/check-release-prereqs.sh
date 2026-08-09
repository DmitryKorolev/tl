#!/bin/sh
# Audit the external state the release pipeline depends on.
#
#   scripts/check-release-prereqs.sh              audit what can be audited
#   scripts/check-release-prereqs.sh --selftest   prove the checker can fail
#
# Everything here lives somewhere other than this repository: npm's per-package
# trusted-publisher configuration, the GitHub `release` environment and its
# protection rules, the `v*` tag ruleset, the Homebrew tap and its credential.
# Writing `environment: release` in a workflow does not create any of that.
#
# Deliberately *not* wired into scripts/check-release-policy.sh. The policy
# gate runs on every commit and must be hermetic; this one talks to npm and to
# the GitHub API, so it is run by a human before tagging, and by the release
# workflow once, before anything is signed. A network check inside the
# per-commit gate would make CI flaky and teach people to ignore it.
#
# Rows it cannot check are reported as UNCHECKED with the reason, never
# silently omitted, and they are carried in docs/overview.md as assumptions.
# The exit code covers only what was actually verified; the summary says how
# much that was.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

usage() {
  echo "usage: $0 [--selftest]" >&2
  exit 2
}

ok=0
bad=0
unchecked=0

pass() { echo "  ok        $1"; ok=$((ok + 1)); }
fail_row() { echo "  MISSING   $1" >&2; echo "            $2" >&2; bad=$((bad + 1)); }
unchecked_row() { echo "  unchecked $1"; echo "            $2"; unchecked=$((unchecked + 1)); }

identity_field() {
  python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' \
    "$repo_root/release/identity.json" "$1"
}

audit() {
  repository=$(identity_field repository)
  npm_package=$(identity_field npmPackage)
  scope=${npm_package%%/*}

  echo "release prerequisites for ${repository}:"

  # --- npm ---------------------------------------------------------------
  if ! command -v npm >/dev/null 2>&1; then
    unchecked_row "the five npm packages exist" \
      "npm is not on PATH, so the registry could not be asked."
  else
    packages="$npm_package"
    for target in $(rc_targets); do
      packages="$packages ${scope}/tl-bin-${target}"
    done
    for pkg in $packages; do
      if npm view "$pkg" name >/dev/null 2>&1; then
        pass "$pkg exists on the registry"
      else
        fail_row "$pkg does not exist on the registry" \
          "npm configures trusted publishing per package and only for a package that already exists, so the first release cannot authenticate for this one. Bootstrap it by hand per docs/release-prerequisites.md, then configure its trusted publisher."
      fi
    done
    unchecked_row "each package's trusted publisher names this workflow" \
      "npm exposes no public API for a package's trusted-publisher configuration; confirm it on npmjs.com per docs/release-prerequisites.md."
    unchecked_row "no classic automation token can publish these packages" \
      "Same: token scopes are not readable from here."
  fi

  # --- GitHub ------------------------------------------------------------
  if ! command -v gh >/dev/null 2>&1; then
    unchecked_row "the release environment, the tag ruleset and the tap" \
      "gh is not on PATH, so the GitHub API could not be asked."
    return 0
  fi
  if ! gh auth status >/dev/null 2>&1; then
    unchecked_row "the release environment, the tag ruleset and the tap" \
      "gh is not authenticated ('gh auth login'), so the GitHub API could not be asked."
    return 0
  fi

  if gh api "repos/${repository}/environments/release" >/dev/null 2>&1; then
    pass "the 'release' environment exists"
    # Protection rules need admin scope to read. Report the shortfall rather
    # than reading an empty list as "no rules configured", which would be the
    # same output as a genuinely unprotected environment.
    if rules=$(gh api "repos/${repository}/environments/release" \
                 --jq '.protection_rules | length' 2>/dev/null); then
      if [ "${rules:-0}" -gt 0 ]; then
        pass "the 'release' environment carries $rules protection rule(s)"
      else
        fail_row "the 'release' environment has no protection rules" \
          "Without required reviewers and a v* deployment-tag rule, anyone who can create a tag can make this workflow sign whatever that tag points at. Configure them per docs/release-prerequisites.md."
      fi
    else
      unchecked_row "the 'release' environment's protection rules" \
        "Reading them needs a token with admin scope, which this check deliberately does not require."
    fi
  else
    fail_row "the 'release' environment does not exist" \
      "The sign job declares 'environment: release', and that declaration is inert until the environment exists with protection rules. Create it per docs/release-prerequisites.md."
  fi

  if rulesets=$(gh api "repos/${repository}/rulesets" --jq 'length' 2>/dev/null); then
    if [ "${rulesets:-0}" -gt 0 ]; then
      pass "the repository has $rulesets ruleset(s) configured"
      unchecked_row "a ruleset restricts who may create v* tags" \
        "Whether a ruleset *targets tags matching v\\** and restricts creation needs the per-ruleset detail, which needs admin scope; confirm it in repository settings."
    else
      fail_row "the repository has no rulesets" \
        "A v* tag ruleset is what stops a tag being created outside review. The sign job's ancestry check is a backstop: it sees what the tag points at, never who pushed it."
    fi
  else
    unchecked_row "the v* tag ruleset" \
      "Reading rulesets needs a token with admin scope."
  fi

  tap="${repository%%/*}/homebrew-tap"
  if gh api "repos/${tap}" >/dev/null 2>&1; then
    pass "the Homebrew tap ${tap} exists"
  else
    fail_row "the Homebrew tap ${tap} does not exist or is not visible" \
      "A stable release pushes the generated formula there and now fails if it cannot. Create it, or remove Homebrew from ADR-0006's channels deliberately."
  fi
  unchecked_row "HOMEBREW_TAP_TOKEN grants write access to the tap" \
    "A secret's scope is not readable from a workflow; confirm by running the release once, or by testing the token by hand."
}

selftest() {
  # The checker's own reporting, not the external world. Each row class must be
  # distinguishable in the output and must land in the right counter — an
  # 'unchecked' row silently counted as 'ok' is exactly the failure this script
  # exists to prevent, one level up.
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  rc_selftest_begin "check-release-prereqs"
  RC_OUT="$work/out"
  RC_ERR="$work/err"

  ok=0; bad=0; unchecked=0
  pass "a verified row" >/dev/null
  rc_note "$([ "$ok" -eq 1 ] && [ "$bad" -eq 0 ] && [ "$unchecked" -eq 0 ] && echo 0 || echo 1)" \
    "a verified row counts as verified and nothing else"

  ok=0; bad=0; unchecked=0
  fail_row "a missing prerequisite" "the remedy" 2>/dev/null
  rc_note "$([ "$bad" -eq 1 ] && [ "$ok" -eq 0 ] && echo 0 || echo 1)" \
    "a missing prerequisite counts as missing"

  ok=0; bad=0; unchecked=0
  unchecked_row "something unreadable" "the reason" >/dev/null
  rc_note "$([ "$unchecked" -eq 1 ] && [ "$ok" -eq 0 ] && [ "$bad" -eq 0 ] && echo 0 || echo 1)" \
    "an unchecked row is neither a pass nor a failure"

  # The exit code must follow the MISSING rows, and unchecked rows must not
  # make a clean audit fail.
  ok=1; bad=0; unchecked=3
  st=0; summary_status >/dev/null 2>&1 || st=$?
  rc_note "$([ "$st" -eq 0 ] && echo 0 || echo 1)" \
    "unchecked rows alone do not fail the audit"
  ok=1; bad=1; unchecked=0
  st=0; summary_status >/dev/null 2>&1 || st=$?
  rc_note "$([ "$st" -eq 1 ] && echo 0 || echo 1)" \
    "a single missing prerequisite fails the audit"

  # Every row the document promises has a counterpart here, so the two cannot
  # drift into describing different sets of prerequisites.
  doc="$repo_root/docs/release-prerequisites.md"
  rc_note "$([ -f "$doc" ] && echo 0 || echo 1)" "docs/release-prerequisites.md exists"
  for needle in "trusted publisher" "release" "ruleset" "HOMEBREW_TAP_TOKEN"; do
    rc_note "$(grep -qi -- "$needle" "$doc" && echo 0 || echo 1)" \
      "the document covers '$needle'"
  done
  # The npm package list this checker audits is the one release/identity.json
  # and release/targets.json define, not a written-out copy.
  rc_note "$(grep -q 'rc_targets' "$script_dir/$(basename -- "$0")" && echo 0 || echo 1)" \
    "the package list is derived from release/targets.json, not written out here"

  rc_selftest_end "The prerequisite audit no longer reports what it claims to report."
}

summary_status() {
  echo
  if [ "$bad" -ne 0 ]; then
    echo "release prerequisites: $bad missing, $ok verified, $unchecked unchecked." >&2
    echo "A missing prerequisite is not a warning: the pipeline's authorization and its npm channel both rest on state configured outside this repository." >&2
    return 1
  fi
  echo "release prerequisites: $ok verified, $unchecked unchecked."
  if [ "$unchecked" -ne 0 ]; then
    echo "The unchecked rows are carried as assumptions in docs/overview.md; confirm them by hand per docs/release-prerequisites.md before the first release and after any permission change."
  fi
  return 0
}

case "${1-}" in
  '')
    audit
    summary_status
    ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  *) usage ;;
esac
