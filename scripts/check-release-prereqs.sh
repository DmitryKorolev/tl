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
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  repository=$(identity_field repository)
  npm_package=$(identity_field npmPackage)
  scope=${npm_package%%/*}

  echo "release prerequisites for ${repository}:"

  # --- the repository must be public -------------------------------------
  #
  # First, because everything else assumes it. GitHub Releases are the source
  # of truth for artifacts, and a private repository serves its assets only to
  # authenticated clients: install.sh, the Homebrew formula and every step in
  # VERIFYING.md get a 404. The document said so; nothing checked it, so the
  # audit reported seven missing prerequisites while the eighth — the one that
  # makes the other seven pointless — went unmentioned.
  if ! command -v gh >/dev/null 2>&1 || ! gh auth status >/dev/null 2>&1; then
    unchecked_row "the repository is public" \
      "gh is not on PATH or not authenticated, so the repository's visibility could not be read."
  elif visibility=$(gh api "repos/${repository}" --jq '.visibility' 2>/dev/null); then
    if [ "$visibility" = public ]; then
      pass "the repository is public, so release assets are downloadable"
    else
      fail_row "the repository is ${visibility}, not public" \
        "A private repository serves release assets only to authenticated clients — an anonymous fetch of /releases/latest is a 404 — so install.sh, 'brew install tl' and the whole of VERIFYING.md cannot work. Deployment protection rules are also a paid feature on private repositories. Make it public, or record an npm-only release in ADR-0006 deliberately: that retires the installer, the tap and the published verification procedure."
    fi
  else
    unchecked_row "the repository is public" \
      "the repository metadata could not be read; check 'gh api repos/${repository}'."
  fi

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

  # The *properties* the security model needs, not proxies for them. A count
  # of protection rules is satisfied by a wait timer, and a count of rulesets
  # by an unrelated branch rule — both would have passed while required
  # reviewers and protected tag creation were absent, which is the whole thing
  # this row exists to establish.
  #
  # A 404 is a missing environment; anything else is an unreadable one, and the
  # two must not collapse into the same verdict.
  env_json="$work/environment.json"
  # `status=$(cmd; echo $?)` does not work here: `set -e` applies inside the
  # command-substitution subshell, so a failing `gh` ends it before `echo`
  # runs and the status comes back empty. An `if` suppresses errexit for its
  # condition, which is the whole point of writing it this way.
  if gh api "repos/${repository}/environments/release" --cache 0s \
       > "$env_json" 2>"$work/env.err"; then
    env_status=0
  else
    env_status=$?
  fi
  if [ "$env_status" -eq 0 ]; then
    pass "the 'release' environment exists"
    reviewers=$(python3 -c '
import json, sys
data = json.load(open(sys.argv[1]))
rules = data.get("protection_rules") or []
for rule in rules:
    if rule.get("type") == "required_reviewers":
        print(len(rule.get("reviewers") or []))
        break
else:
    print(-1)
' "$env_json")
    if [ "$reviewers" -gt 0 ] 2>/dev/null; then
      pass "the 'release' environment requires $reviewers reviewer(s)"
    elif [ "$reviewers" = 0 ]; then
      fail_row "the 'release' environment has a required-reviewers rule with nobody in it" \
        "An empty reviewer list approves itself. Add at least one reviewer per docs/release-prerequisites.md."
    else
      fail_row "the 'release' environment has no required-reviewers rule" \
        "Its other rules — a wait timer, a branch policy — do not gate approval. Without required reviewers, anyone who can create a tag can make this workflow sign whatever that tag points at."
    fi
    if python3 -c '
import json, sys
data = json.load(open(sys.argv[1]))
sys.exit(0 if data.get("deployment_branch_policy") else 1)
' "$env_json"; then
      # A custom policy exists; check that its patterns are tag patterns and
      # that they are the v* shape this pipeline releases under.
      policy=$(gh api "repos/${repository}/environments/release/deployment-branch-policies" \
                 --jq '[.branch_policies[] | select(.type == "tag") | .name] | join(",")' 2>/dev/null || echo '')
      case ",$policy," in
        *,v\**,*) pass "the 'release' environment restricts deployments to v* tags ($policy)" ;;
        ,,) fail_row "the 'release' environment has a deployment policy with no tag patterns" \
              "Only a tag policy matching v* keeps a branch push out of the environment that can sign." ;;
        *) fail_row "the 'release' environment's tag patterns are '$policy', not v*" \
             "The pattern must cover exactly the tags this pipeline releases under." ;;
      esac
    else
      fail_row "the 'release' environment allows deployments from any ref" \
        "Set a deployment-tag policy of v*, so a branch push cannot enter the environment that can sign."
    fi
  elif grep -q '404\|Not Found' "$work/env.err" 2>/dev/null; then
    fail_row "the 'release' environment does not exist" \
      "The sign and publish-npm jobs declare 'environment: release', and that declaration is inert until the environment exists with protection rules. Create it per docs/release-prerequisites.md."
  else
    unchecked_row "the 'release' environment" \
      "the API call failed for a reason other than 'not found' ($(tr -d '\n' < "$work/env.err" | cut -c1-120)); this is not evidence that it is missing."
  fi

  rules_json="$work/rulesets.json"
  if gh api "repos/${repository}/rulesets" --cache 0s \
       > "$rules_json" 2>"$work/rules.err"; then
    rules_status=0
  else
    rules_status=$?
  fi
  if [ "$rules_status" -ne 0 ]; then
    unchecked_row "a ruleset restricts who may create v* tags" \
      "the rulesets API call failed ($(tr -d '\n' < "$work/rules.err" | cut -c1-120))."
  else
    # Each ruleset's detail, not just the count: the target must be `tag`, it
    # must be actively enforced, its conditions must cover v*, and it must
    # actually restrict creation.
    tag_ruleset=''
    for id in $(python3 -c '
import json, sys
for entry in json.load(open(sys.argv[1])):
    if entry.get("target") == "tag":
        print(entry["id"])
' "$rules_json"); do
      detail="$work/ruleset-$id.json"
      gh api "repos/${repository}/rulesets/$id" --cache 0s > "$detail" 2>/dev/null || continue
      if python3 -c '
import json, sys
data = json.load(open(sys.argv[1]))
if data.get("enforcement") != "active":
    sys.exit(1)
patterns = (((data.get("conditions") or {}).get("ref_name") or {}).get("include")) or []
if not any(p in ("~ALL", "refs/tags/v*") or p.startswith("refs/tags/v") for p in patterns):
    sys.exit(1)
kinds = {r.get("type") for r in (data.get("rules") or [])}
sys.exit(0 if "creation" in kinds else 1)
' "$detail"; then
        tag_ruleset=$id
        break
      fi
    done
    if [ -n "$tag_ruleset" ]; then
      pass "an active tag ruleset (#$tag_ruleset) restricts creation of v* tags"
    else
      fail_row "no active ruleset restricts creation of v* tags" \
        "A ruleset that exists but targets branches, is in evaluate mode, does not cover v*, or carries no creation restriction leaves tag creation open. The sign job's ancestry check is a backstop: it sees what the tag points at, never who pushed it."
    fi
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
  rc_selftest_begin "check-release-prereqs" "$work"

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
