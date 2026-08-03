#!/usr/bin/env bash
# No-task-ID-leakage gate (AGENTS.md, "Artifacts must be human-readable";
# ADR-0026). Scope: every tracked file except the prose docs that render
# sample CLI output. Any display-affixed id token in scope must be registered
# in scripts/task-id-placeholders.txt as a non-tracker placeholder.
#
# This file is in its own scope, so its probe strings are assembled from
# $affix rather than written out literally.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

registry=scripts/task-id-placeholders.txt
affix='tl-'

# The display affix (ADR-0007) followed by at least shortIdFloor = 4 Crockford
# base32 digits (`0-9 a-z` minus `i l o u`). The leading class is a token
# boundary, so a hyphenated compound cannot hide a match.
if [ ! -s "$registry" ]; then
  echo "::error::$registry is missing or empty — the placeholder registry is part of this gate's pinned contract (ADR-0026); restore it rather than deleting the gate's exclusion set."
  exit 1
fi

pattern="(^|[^0-9A-Za-z_])${affix}[0-9a-hjkmnp-tv-z]{4,}"
token="${affix}[0-9a-hjkmnp-tv-z]{4,}"

scan() {
  git grep -InE "$pattern" -- \
    ':(exclude)docs/' ':(exclude)README.md' ":(exclude)$registry" || true
}

# Every token on a hit line is checked, not just the first: a leak sharing a
# line with a registered placeholder must still be reported.
classify() {
  local leaks=0 line tok
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    for tok in $(printf '%s\n' "$line" | grep -oE "$token"); do
      if ! grep -qxF "$tok" "$registry"; then
        printf '%s\n' "$line"
        leaks=$((leaks + 1))
        break
      fi
    done
  done
  # A count would wrap at 256 as an exit status; report presence, not tally.
  [ "$leaks" -eq 0 ]
}

if [ "${1:-}" = "--selftest" ]; then
  probe() { printf '%s\n' "$1" | grep -qE "$pattern" && echo match || echo miss; }
  fail=0
  for leak in "see ${affix}8wmb for context" "fixed in ${affix}pyvg." \
              "-- ${affix}f01vn6s6n79wmqa8 is the epic" "(${affix}d1zh)" \
              "url/${affix}8wmb" "x-${affix}8wmb"; do
    [ "$(probe "$leak")" = match ] || { echo "selftest: missed '$leak'"; fail=1; }
  done
  for clean in "nothing ${affix}related needs ignoring" "actor is ${affix}dev" \
               "the ${affix} prefix is reserved" "TL-8WMB"; do
    [ "$(probe "$clean")" = miss ] || { echo "selftest: false hit '$clean'"; fail=1; }
  done
  files=$(git ls-files -- ':(exclude)docs/' ':(exclude)README.md' | wc -l | tr -d ' ')
  [ "$files" -gt 0 ] || { echo "selftest: the scan pathspec selected no files"; fail=1; }
  [ -s "$registry" ] || { echo "selftest: $registry is missing or empty"; fail=1; }
  if [ "$fail" -ne 0 ]; then
    echo "::error::the task-id lint no longer detects what it claims to — repair the pattern in scripts/check-task-ids.sh before trusting this gate."
    exit 1
  fi
  echo "task-id lint selftest ok ($files files in scope)"
  exit 0
fi

if ! hits=$(scan | classify); then
  printf '%s\n' "$hits"
  echo "::error::task-tracker id in a tracked artifact. Code and comments must stand on their own — describe the substance instead (AGENTS.md, 'Artifacts must be human-readable'). If this token is a test or example placeholder rather than a tracker reference, register it in $registry in this same change."
  exit 1
fi
echo "task-id lint clean"
