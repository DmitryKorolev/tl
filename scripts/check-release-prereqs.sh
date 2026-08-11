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
deferred=0

pass() { echo "  ok        $1"; ok=$((ok + 1)); }
fail_row() { echo "  MISSING   $1" >&2; echo "            $2" >&2; bad=$((bad + 1)); }
unchecked_row() { echo "  unchecked $1"; echo "            $2"; unchecked=$((unchecked + 1)); }
# A prerequisite this release does not have, because release/plan.json defers
# the channel that needs it. Its own class, not a pass and not a skip: reported
# so the reader can see the plan was consulted, and counted separately so a
# deferred channel never contributes to the verdict. Collapsing it into MISSING
# is what made the first release impossible — the audit demanded five npm
# packages and a Homebrew tap for channels v0.1.0 deliberately does not
# publish, and the sign job runs this with no way to disregard a row.
deferred_row() { echo "  deferred  $1"; echo "            $2"; deferred=$((deferred + 1)); }

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
        "A private repository serves release assets only to authenticated clients — an anonymous fetch of /releases/latest is a 404 — so install.sh, 'brew install tl' and the whole of VERIFYING.md cannot work. Deployment protection rules are also a paid feature on private repositories. Make it public, or defer the installer and Homebrew channels in release/plan.json deliberately — that file is where which channels a release publishes is decided, and deferring them retires the tap and the published verification procedure for this release."
    fi
  else
    unchecked_row "the repository is public" \
      "the repository metadata could not be read; check 'gh api repos/${repository}'."
  fi

  # --- npm ---------------------------------------------------------------
  #
  # Only when release/plan.json enables the channel. The plan is where "which
  # channels does this release publish through" is decided, and the publish
  # jobs are already derived from it; an audit that demanded npm's
  # prerequisites regardless would stop the release it was auditing for a
  # channel that release does not use.
  npm_state=$(rc_channel_state npm 2>"$work/plan.err") || npm_state=''
  case $npm_state in
    '')
      unchecked_row "the npm channel's prerequisites" \
        "release/plan.json could not be read ($(tr -d '\n' < "$work/plan.err" | cut -c1-160)), so whether this release publishes to npm is unknown and none of its rows were run."
      ;;
    deferred*)
      deferred_row "the npm packages and their trusted publishers" \
        "release/plan.json defers the npm channel to ${npm_state#deferred }, so this release publishes nothing to npm and needs none of it. Enable the channel there when it is time — and bootstrap the package names first, per docs/release-prerequisites.md, because npm configures trusted publishing only for a package that already exists."
      ;;
    *)
      if ! command -v npm >/dev/null 2>&1; then
        unchecked_row "the five npm packages exist" \
          "npm is not on PATH, so the registry could not be asked."
      else
        packages="$npm_package"
        # Resolved with its status checked: written as `for target in
        # $(rc_targets)` an unreadable targets file audited the launcher alone
        # and reported a clean sweep over one package instead of five.
        targets=$(rc_targets 2>"$work/targets.err") || targets=''
        if [ -z "$targets" ]; then
          unchecked_row "the npm packages exist" \
            "the distributed targets could not be read ($(tr -d '\n' < "$work/targets.err" | cut -c1-160)), so the package names to audit are unknown. Auditing whichever subset resolved would report a clean sweep over the wrong list."
        else
          for target in $targets; do
            packages="$packages ${scope}/tl-bin-${target}"
          done
          for pkg in $packages; do
            # "The registry says no" and "the registry did not answer" are
            # different findings with different remedies, and only the first is
            # about this repository's configuration. Collapsing them aborted a
            # correct release on a transient 5xx, telling the operator to
            # bootstrap a package that already existed.
            if npm view "$pkg" name >"$work/npm.out" 2>"$work/npm.err"; then
              pass "$pkg exists on the registry"
            elif grep -q 'E404\|404 Not Found\|is not in this registry\|No match found' "$work/npm.err"; then
              fail_row "$pkg does not exist on the registry" \
                "npm configures trusted publishing per package and only for a package that already exists, so the first release cannot authenticate for this one. Bootstrap it by hand per docs/release-prerequisites.md, then configure its trusted publisher."
            else
              unchecked_row "$pkg exists on the registry" \
                "the registry did not answer ($(tr -d '\n' < "$work/npm.err" | cut -c1-160)); that is not evidence the package is absent. Re-run when the registry is reachable."
            fi
          done
        fi
        unchecked_row "each package's trusted publisher names this workflow" \
          "npm exposes no public API for a package's trusted-publisher configuration; confirm it on npmjs.com per docs/release-prerequisites.md."
        unchecked_row "no classic automation token can publish these packages" \
          "Same: token scopes are not readable from here."
      fi
      ;;
  esac

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
      # Every policy entry, tagged with its own type. Filtering the branch
      # entries out before looking made an environment that admits `main`
      # *and* `v*` report as one restricted to v* tags — the branch half, which
      # is the half that lets a push reach the signing job, was invisible.
      if policy=$(gh api "repos/${repository}/environments/release/deployment-branch-policies" \
                    --jq '[.branch_policies[] | .type + ":" + .name] | join(",")' \
                    2>"$work/policy.err"); then
        branch_patterns=$(printf '%s' "$policy" | tr ',' '\n' | sed -n 's/^branch://p')
        tag_patterns=$(printf '%s' "$policy" | tr ',' '\n' | sed -n 's/^tag://p')
        if [ -n "$branch_patterns" ]; then
          fail_row "the 'release' environment also admits branch deployments ($(printf '%s' "$branch_patterns" | tr '\n' ' '))" \
            "A branch policy lets a push reach the environment that can sign, whatever the tag policy beside it says. Remove the branch entries and keep only a v* tag policy."
        elif [ -z "$tag_patterns" ]; then
          fail_row "the 'release' environment has a deployment policy with no tag patterns" \
            "Only a tag policy matching v* keeps a branch push out of the environment that can sign."
        elif printf '%s\n' "$tag_patterns" | grep -qx '\*'; then
          fail_row "the 'release' environment's tag policy includes '*', which admits every tag" \
            "A pattern of '*' is not a restriction. Use v*, so only the tags this pipeline releases under can enter the environment that can sign."
        elif printf '%s\n' "$tag_patterns" | grep -qx 'v\*'; then
          pass "the 'release' environment restricts deployments to v* tags ($(printf '%s' "$tag_patterns" | tr '\n' ' '))"
        else
          fail_row "the 'release' environment's tag patterns are '$(printf '%s' "$tag_patterns" | tr '\n' ' ')', not v*" \
            "The pattern must cover exactly the tags this pipeline releases under."
        fi
      else
        unchecked_row "the 'release' environment's deployment policy" \
          "the policy could not be read ($(tr -d '\n' < "$work/policy.err" | cut -c1-160)); this is not evidence that it is correct."
      fi
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
    unreadable_rulesets=0
    # Resolved with its status checked. As `for id in $(python3 …)` the parse's
    # failure was discarded, so a listing this could not read produced an empty
    # loop and, below, a MISSING row — an unreadable API reported as an absent
    # ruleset, which is the collapse the rest of this file exists to remove.
    if ! ids=$(python3 -c '
import json, sys
try:
    entries = json.load(open(sys.argv[1]))
except (OSError, ValueError) as error:
    sys.exit(f"the rulesets listing is not readable JSON ({error})")
for entry in entries:
    if entry.get("target") == "tag":
        print(entry["id"])
' "$rules_json" 2>"$work/rules-parse.err"); then
      unchecked_row "a ruleset restricts who may create v* tags" \
        "the rulesets listing could not be read ($(tr -d '\n' < "$work/rules-parse.err" | cut -c1-160)); that is not evidence that no ruleset exists."
      ids=''
      unreadable_rulesets=1
    fi
    for id in $ids; do
      detail="$work/ruleset-$id.json"
      # A ruleset this cannot read is not a ruleset that fails to qualify.
      # Skipping it silently turned one 5xx on a detail call into "no active
      # ruleset restricts creation of v* tags" — a MISSING row that aborts a
      # correctly configured release and sends the operator to create a
      # ruleset that already exists.
      if ! gh api "repos/${repository}/rulesets/$id" --cache 0s > "$detail" 2>"$work/detail.err"; then
        unreadable_rulesets=$((unreadable_rulesets + 1))
        continue
      fi
      if python3 -c '
import json, sys
data = json.load(open(sys.argv[1]))
if data.get("enforcement") != "active":
    sys.exit(1)
ref_name = ((data.get("conditions") or {}).get("ref_name")) or {}
patterns = ref_name.get("include") or []
# The question is whether the include set covers *every* v* tag, not whether
# one pattern looks v-ish. `p.startswith("refs/tags/v")` answered the second:
# a ruleset naming the single tag `refs/tags/v1.0.0` — or the one release line
# `refs/tags/v1.*` — passed as one restricting creation of v* tags, leaving
# every other v* tag creatable by anyone. So the accepted patterns are an
# explicit closed set, and a pattern outside it is not assumed to cover
# anything.
COVERS_EVERY_V_TAG = {"~ALL", "refs/tags/*", "refs/tags/**", "refs/tags/v*", "refs/tags/v**"}
if not any(p in COVERS_EVERY_V_TAG for p in patterns):
    sys.exit(1)
# An exclude list can hole any of those, and reasoning about which holes matter
# is exactly the kind of interpretation a gate should refuse: an excluded
# `refs/tags/v0.*` would leave the whole 0.x line unrestricted while the
# include set still reads as complete.
if ref_name.get("exclude"):
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
    elif [ "$unreadable_rulesets" -ne 0 ]; then
      unchecked_row "a ruleset restricts who may create v* tags" \
        "$unreadable_rulesets ruleset(s) could not be read, and none of the ones that could read as covering every v* tag. An unreadable ruleset is not an absent one — re-run when the API is reachable rather than creating a ruleset that may already exist."
    else
      fail_row "no active ruleset restricts creation of v* tags" \
        "A ruleset that exists but targets branches, is in evaluate mode, carries no creation restriction, or whose ref conditions do not cover *every* v* tag leaves tag creation open. Coverage means an include pattern of ~ALL, refs/tags/*, refs/tags/** or refs/tags/v*, and no exclude list: naming one tag or one release line restricts that tag or that line and nothing else. The sign job's ancestry check is a backstop — it sees what the tag points at, never who pushed it."
    fi
  fi

  # The Homebrew tap, on the same terms as npm: only when release/plan.json
  # enables the channel, and with "not found" kept apart from "could not ask".
  brew_state=$(rc_channel_state homebrew 2>"$work/plan.err") || brew_state=''
  case $brew_state in
    '')
      unchecked_row "the Homebrew channel's prerequisites" \
        "release/plan.json could not be read ($(tr -d '\n' < "$work/plan.err" | cut -c1-160)), so whether this release publishes a formula is unknown and none of its rows were run."
      ;;
    deferred*)
      deferred_row "the Homebrew tap and its credential" \
        "release/plan.json defers the Homebrew channel to ${brew_state#deferred }, so this release pushes no formula and needs neither the tap nor HOMEBREW_TAP_TOKEN. Enable the channel there when it is time, and create the tap first per docs/release-prerequisites.md."
      ;;
    *)
      tap="${repository%%/*}/homebrew-tap"
      if gh api "repos/${tap}" >"$work/tap.out" 2>"$work/tap.err"; then
        pass "the Homebrew tap ${tap} exists"
      elif grep -q '404\|Not Found' "$work/tap.err"; then
        fail_row "the Homebrew tap ${tap} does not exist or is not visible" \
          "A release with this channel enabled pushes the generated formula there and fails if it cannot. Create the tap per docs/release-prerequisites.md, or defer the Homebrew channel in release/plan.json — that file is where the decision lives."
      else
        unchecked_row "the Homebrew tap ${tap} exists" \
          "the API call failed for a reason other than 'not found' ($(tr -d '\n' < "$work/tap.err" | cut -c1-160)); this is not evidence that the tap is absent."
      fi
      unchecked_row "HOMEBREW_TAP_TOKEN grants write access to the tap" \
        "A secret's scope is not readable from a workflow; confirm by running the release once, or by testing the token by hand. Store it where publish-homebrew reads it — a repository secret, since that job declares no environment."
      ;;
  esac
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

  # --- the audit itself, over stubbed external state ------------------------
  #
  # Everything above tests the reporting helpers; none of it entered `audit`,
  # so every branch that decides a release could change without a row moving.
  # `gh` and `npm` are stubbed and answer from environment variables, so each
  # row drives one branch instead of whatever a real account happens to hold.
  bin="$work/bin"
  mkdir -p "$bin"
  cat > "$bin/gh" <<'GHSTUB'
#!/bin/sh
# Specific paths first: a case glob must match the whole word, but `repos/*`
# would otherwise swallow every one of them.
case "$1" in
  auth) exit "${GH_STUB_AUTH:-0}" ;;
esac
case "$2" in
  repos/*/environments/release/deployment-branch-policies)
    if [ -n "${GH_STUB_POLICY_FAILS:-}" ]; then
      echo "gh: could not reach the API (HTTP 502)" >&2
      exit 1
    fi
    # Unset-only default: an *empty* policy is one of the cases under test.
    printf '%s\n' "${GH_STUB_POLICY-tag:v*}"
    ;;
  repos/*/environments/release)
    case "${GH_STUB_ENV:-ok}" in
      missing) echo "gh: Not Found (HTTP 404)" >&2; exit 1 ;;
      error) echo "gh: could not reach the API (HTTP 502)" >&2; exit 1 ;;
      *) cat "$GH_STUB_ENV_JSON" ;;
    esac
    ;;
  repos/*/rulesets) printf '%s\n' "${GH_STUB_RULESETS:-[]}" ;;
  repos/*/rulesets/*)
    if [ -n "${GH_STUB_RULESET_FAILS:-}" ]; then
      echo "gh: could not reach the API (HTTP 502)" >&2
      exit 1
    fi
    printf '%s\n' "${GH_STUB_RULESET:-{\}}"
    ;;
  repos/*/homebrew-tap)
    case "${GH_STUB_TAP:-ok}" in
      missing) echo "gh: Not Found (HTTP 404)" >&2; exit 1 ;;
      error) echo "gh: could not reach the API (HTTP 502)" >&2; exit 1 ;;
      *) echo '{}' ;;
    esac
    ;;
  repos/*) printf '%s\n' "${GH_STUB_VISIBILITY:-public}" ;;
esac
exit 0
GHSTUB
  cat > "$bin/npm" <<'NPMSTUB'
#!/bin/sh
case "${NPM_STUB:-ok}" in
  absent)
    echo "npm error code E404" >&2
    echo "npm error 404 Not Found - GET https://registry.npmjs.org/x" >&2
    exit 1
    ;;
  unreachable)
    echo "npm error network request to https://registry.npmjs.org failed" >&2
    exit 1
    ;;
  *) echo "@taskloop/tl" ;;
esac
NPMSTUB
  chmod +x "$bin/gh" "$bin/npm"

  # An environment that satisfies every property the audit asks about, so a row
  # varying one thing varies only that thing.
  cat > "$work/env-ok.json" <<'ENVJSON'
{
  "protection_rules": [
    {"type": "required_reviewers", "reviewers": [{"type": "User"}]}
  ],
  "deployment_branch_policy": {"protected_branches": false, "custom_branch_policies": true}
}
ENVJSON
  cat > "$work/env-no-reviewers.json" <<'ENVJSON'
{
  "protection_rules": [{"type": "wait_timer", "wait_timer": 5}],
  "deployment_branch_policy": {"protected_branches": false, "custom_branch_policies": true}
}
ENVJSON
  cp "$repo_root/release/plan.json" "$work/plan-deferred.json"
  cat > "$work/plan-enabled.json" <<'PLANJSON'
{"channels": [
  {"channel": "github-release", "enabled": true},
  {"channel": "installer", "enabled": true},
  {"channel": "npm", "enabled": true},
  {"channel": "homebrew", "enabled": true}
]}
PLANJSON
  printf '%s\n' '{"channels": 3}' > "$work/plan-broken.json"

  # A ruleset that satisfies the tag row, so the environment and channel rows
  # below are the only thing varying.
  ruleset_list='[{"target": "tag", "id": 7}]'
  ruleset_detail='{"enforcement": "active", "conditions": {"ref_name": {"include": ["refs/tags/v*"]}}, "rules": [{"type": "creation"}]}'

  audit_with() {
    # audit_with <want-status> <needle> <name> <VAR=VALUE>...
    aw__want=$1; aw__needle=$2; aw__name=$3; shift 3
    rc_expect_output "$aw__want" "$aw__needle" "$aw__name" \
      env PATH="$bin:$PATH" \
          GH_STUB_ENV_JSON="$work/env-ok.json" \
          GH_STUB_RULESETS="$ruleset_list" \
          GH_STUB_RULESET="$ruleset_detail" \
          "$@" "$0"
  }

  # The whole reason this became plan-aware: with npm and Homebrew deferred,
  # their prerequisites are not this release's, and demanding them made the
  # first release impossible — the sign job runs this and has no way to
  # disregard a row a human was told to disregard.
  audit_with 0 "defers the npm channel" \
    "a deferred npm channel is reported as deferred, not missing" \
    RC_PLAN_FILE="$work/plan-deferred.json"
  audit_with 0 "defers the Homebrew channel" \
    "a deferred Homebrew channel is reported as deferred, not missing" \
    RC_PLAN_FILE="$work/plan-deferred.json"
  # The strongest form of it: with both channels deferred, an absent package
  # and an absent tap are not prerequisites at all. Asserted as the *absence*
  # of a MISSING row, which is the thing that used to stop the release.
  rc_run env PATH="$bin:$PATH" \
    GH_STUB_ENV_JSON="$work/env-ok.json" \
    GH_STUB_RULESETS="$ruleset_list" GH_STUB_RULESET="$ruleset_detail" \
    RC_PLAN_FILE="$work/plan-deferred.json" NPM_STUB=absent GH_STUB_TAP=missing \
    "$0"
  rc_note "$([ "$RC_STATUS" -eq 0 ] && ! grep -q 'MISSING' "$RC_ERR" "$RC_OUT" && echo 0 || echo 1)" \
    "with both channels deferred, an absent package and an absent tap are not prerequisites"
  # And with them enabled the same state is missing, so the rows above are not
  # passing because nothing is checked.
  audit_with 1 "does not exist on the registry" \
    "an enabled npm channel audits the packages" \
    RC_PLAN_FILE="$work/plan-enabled.json" NPM_STUB=absent
  audit_with 1 "the Homebrew tap" \
    "an enabled Homebrew channel audits the tap" \
    RC_PLAN_FILE="$work/plan-enabled.json" GH_STUB_TAP=missing
  # A plan nobody can read is not a plan that says "off".
  audit_with 0 "could not be read" \
    "an unreadable plan leaves the channel rows unchecked rather than off" \
    RC_PLAN_FILE="$work/plan-broken.json"

  # "The registry says no" and "the registry did not answer" have different
  # remedies, and only the first is about this repository. Collapsed, a
  # transient 5xx aborted a correct release telling the operator to bootstrap a
  # package that already existed.
  audit_with 0 "the registry did not answer" \
    "an unreachable registry is unchecked, not a missing package" \
    RC_PLAN_FILE="$work/plan-enabled.json" NPM_STUB=unreachable
  audit_with 0 "other than 'not found'" \
    "an API failure on the tap is unchecked, not a missing tap" \
    RC_PLAN_FILE="$work/plan-enabled.json" GH_STUB_TAP=error

  # The deployment policy. Filtering the branch entries away made an
  # environment that admits `main` report as one restricted to v* tags.
  audit_with 1 "also admits branch deployments" \
    "a branch deployment policy is refused even beside a v* tag policy" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_POLICY="branch:main,tag:v*"
  audit_with 1 "admits every tag" \
    "a '*' tag policy is refused rather than read as a restriction" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_POLICY="tag:*"
  audit_with 1 "not v\*" \
    "a tag policy for some other shape is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_POLICY="tag:release-*"
  audit_with 1 "no tag patterns" \
    "a deployment policy with no tag patterns is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_POLICY=""
  audit_with 0 "restricts deployments to v\* tags" \
    "a v* tag policy alone passes" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_POLICY="tag:v*"
  audit_with 0 "deployment policy" \
    "a policy that could not be read is unchecked, not correct" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_POLICY_FAILS=1

  # The environment and the ruleset: missing, unreadable, and unprotected.
  audit_with 1 "does not exist" "a missing release environment is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_ENV=missing
  audit_with 0 "other than 'not found'" \
    "an unreadable release environment is unchecked, not missing" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_ENV=error
  audit_with 1 "no required-reviewers rule" \
    "an environment with no required reviewers is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_ENV_JSON="$work/env-no-reviewers.json"
  audit_with 1 "no active ruleset restricts creation" \
    "an absent tag ruleset is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_RULESETS="[]"
  audit_with 1 "no active ruleset restricts creation" \
    "a tag ruleset in evaluate mode is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "evaluate", "conditions": {"ref_name": {"include": ["refs/tags/v*"]}}, "rules": [{"type": "creation"}]}'
  audit_with 1 "no active ruleset restricts creation" \
    "a tag ruleset carrying no creation restriction is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "active", "conditions": {"ref_name": {"include": ["refs/tags/v*"]}}, "rules": [{"type": "deletion"}]}'
  # The include set has to cover *every* v* tag. Accepting any pattern that
  # merely starts with refs/tags/v let a ruleset naming one tag, or one release
  # line, pass as one restricting the whole v* namespace — leaving every other
  # v* tag creatable by anyone, which is the capability the environment
  # protections exist to gate.
  audit_with 1 "no active ruleset restricts creation" \
    "a ruleset naming a single tag does not count as covering v*" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "active", "conditions": {"ref_name": {"include": ["refs/tags/v1.0.0"]}}, "rules": [{"type": "creation"}]}'
  audit_with 1 "no active ruleset restricts creation" \
    "a ruleset covering one release line does not count as covering v*" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "active", "conditions": {"ref_name": {"include": ["refs/tags/v1.*"]}}, "rules": [{"type": "creation"}]}'
  audit_with 1 "no active ruleset restricts creation" \
    "an exclude list holes the coverage and is refused rather than interpreted" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "active", "conditions": {"ref_name": {"include": ["refs/tags/v*"], "exclude": ["refs/tags/v0.*"]}}, "rules": [{"type": "creation"}]}'
  # …and the patterns that genuinely do cover it.
  audit_with 0 "restricts creation of v\* tags" \
    "a ruleset over every tag covers v*" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "active", "conditions": {"ref_name": {"include": ["refs/tags/*"]}}, "rules": [{"type": "creation"}]}'
  audit_with 0 "restricts creation of v\* tags" \
    "a ruleset over every ref covers v*" \
    RC_PLAN_FILE="$work/plan-deferred.json" \
    GH_STUB_RULESET='{"enforcement": "active", "conditions": {"ref_name": {"include": ["~ALL"]}}, "rules": [{"type": "creation"}]}'
  # An unreadable ruleset is not an absent one. A 5xx on the detail call used to
  # be skipped silently, which turned a correctly configured repository into
  # "no active ruleset restricts creation of v* tags" and aborted the release
  # with a remedy telling the operator to create what already existed.
  audit_with 0 "could not be read" \
    "a ruleset whose detail cannot be read is unchecked, not missing" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_RULESET_FAILS=1
  audit_with 0 "not an absent one" \
    "the unreadable-ruleset row says why it is not a refusal" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_RULESET_FAILS=1
  # Same for a listing that does not parse: an empty loop used to read as
  # "there are no tag rulesets".
  audit_with 0 "rulesets listing could not be read" \
    "an unparseable rulesets listing is unchecked, not missing" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_RULESETS='not json'

  # The repository's own visibility, which everything else assumes.
  audit_with 1 "not public" "a private repository is refused" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_VISIBILITY=private
  # And a gh that cannot answer at all leaves the GitHub half unchecked.
  audit_with 0 "not authenticated" "an unauthenticated gh leaves the GitHub rows unchecked" \
    RC_PLAN_FILE="$work/plan-deferred.json" GH_STUB_AUTH=1

  rc_selftest_end "The prerequisite audit no longer reports what it claims to report."
}

summary_status() {
  echo
  if [ "$bad" -ne 0 ]; then
    echo "release prerequisites: $bad missing, $ok verified, $unchecked unchecked, $deferred deferred." >&2
    echo "A missing prerequisite is not a warning: the pipeline's authorization rests on state configured outside this repository." >&2
    return 1
  fi
  echo "release prerequisites: $ok verified, $unchecked unchecked, $deferred deferred."
  if [ "$deferred" -ne 0 ]; then
    echo "The deferred rows belong to channels release/plan.json switches off for this release; they become prerequisites the moment that file enables them."
  fi
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
