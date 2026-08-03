#!/usr/bin/env bash
# No-task-ID-leakage gate (AGENTS.md, "Artifacts must be human-readable";
# ADR-0026). Scope: every tracked file except the prose docs that render
# sample CLI output. Any display-affixed id token in scope must be registered
# in scripts/task-id-placeholders.txt as a non-tracker placeholder.
#
# This file is in its own scope, so its probe strings are assembled from
# $affix rather than written out literally.
set -euo pipefail
# Byte-oriented matching. Everything this gate compares is ASCII — the pattern,
# the registry lookup, the case fold — and without it the blob-as-text scan
# below is incomplete on exactly the files it newly reaches.
export LC_ALL=C

root=$(git rev-parse --show-toplevel)
cd "$root"

registry=scripts/task-id-placeholders.txt
affix='tl-'

# One pathspec, shared by the scan, the selftest and the file count, so the
# three cannot drift apart when an exclusion is added.
pathspec=(':(exclude)docs/' ':(exclude)README.md' ":(exclude)$registry")

# The display affix (ADR-0007) followed by at least shortIdFloor = 4 Crockford
# base32 digits (`0-9 a-z` minus `i l o u`). The leading class is a token
# boundary, so a hyphenated compound cannot hide a match.
#
# Matched case-insensitively, because the id surface is: `Tl/Cli/Resolve`
# lowercases a token before testing the affix and applies the Crockford aliases,
# so `TL-…`, `Tl-…` and `tl-…` all resolve to the same issue and all three are
# equally a leak. Registry lookups fold case for the same reason.
pattern="(^|[^0-9A-Za-z_])${affix}[0-9a-hjkmnp-tv-z]{4,}"
token="${affix}[0-9a-hjkmnp-tv-z]{4,}"

if [ ! -s "$registry" ]; then
  echo "::error::$registry is missing or empty — the placeholder registry is part of this gate's pinned contract (ADR-0026); restore it rather than deleting the gate's exclusion set."
  exit 1
fi

# Every token on a hit line is checked, not just the first: a leak sharing a
# line with a registered placeholder must still be reported.
classify() {
  local leaks=0 line tok
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    for tok in $(printf '%s\n' "$line" | grep -oEi "$token"); do
      if ! grep -qxF "$(printf '%s' "$tok" | tr '[:upper:]' '[:lower:]')" "$registry"; then
        printf '%s\n' "$line"
        leaks=$((leaks + 1))
        break
      fi
    done
  done
  # A count would wrap at 256 as an exit status; report presence, not tally.
  [ "$leaks" -eq 0 ]
}

# `git grep` exits 1 for "no matches" and 128 for a fatal error — a bad regex, a
# mistyped pathspec magic word, an unreadable object. Collapsing both to "clean"
# would make a scan that *cannot run* indistinguishable from one that found
# nothing, which is the failure mode AGENTS.md names for the trust verifier: an
# arm that is silent when broken must not read as success.
# `-a` reads every blob as text. Without it `git grep` skips anything it sniffs
# as binary — and `.gitattributes` could mark a file binary and narrow this
# gate's scope silently. A file git classifies as binary is still a tracked
# artifact. Note `-I` (the opposite) is what we must NOT use, and plain removal
# is not enough either: git then prints "Binary file X matches", which carries
# no token for `classify` to inspect.
scan() {
  local dir=$1; shift
  git -C "$dir" grep -anEi "$pattern" -- "$@"
}

run_scan() {
  local out rc
  set +e
  out=$(scan "$root" "${pathspec[@]}")
  rc=$?
  set -e
  if [ "$rc" -gt 1 ]; then
    echo "::error::the task-id scan could not run (git grep exit $rc) — repair the pattern or the pathspec in scripts/check-task-ids.sh. A scan that cannot run must not report clean." >&2
    return 2
  fi
  printf '%s' "$out"
}

# Same fail-closed rule as the scan: if the pathspec cannot even be listed, say
# so in the gate's own words rather than dying on git's fatal alone.
scope_size() {
  local out rc
  set +e
  out=$(git ls-files -- "${pathspec[@]}")
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    echo "::error::the task-id scope could not be listed (git ls-files exit $rc) — repair the pathspec in scripts/check-task-ids.sh. A scope that cannot be read must not report clean." >&2
    return 2
  fi
  printf '%s' "$out" | grep -c '' || true
}

if [ "${1:-}" = "--selftest" ]; then
  probe() { printf '%s\n' "$1" | grep -qEi "$pattern" && echo match || echo miss; }
  fail=0
  # The pattern still detects the shapes a leak actually takes, including the
  # uppercase rendering the CLI resolves just as readily …
  for leak in "see ${affix}8wmb for context" "fixed in ${affix}pyvg." \
              "-- ${affix}f01vn6s6n79wmqa8 is the epic" "(${affix}d1zh)" \
              "url/${affix}8wmb" "x-${affix}8wmb" \
              "$(printf '%s' "${affix}8wmb" | tr '[:lower:]' '[:upper:]')"; do
    [ "$(probe "$leak")" = match ] || { echo "selftest: missed '$leak'"; fail=1; }
  done
  # … and still rejects what is not an id.
  # The last entry is the RECORDED LIMIT, not a non-id: the Crockford symbol
  # aliases (o->0, i/l->1) resolve in the CLI but stay out of the canonical
  # class (ADR-0026 residuals). Pinning it here means a future widening has to
  # move this line deliberately rather than change the contract silently.
  for clean in "the ${affix} prefix is reserved" "a ${affix}x short form" \
               "${affix}o231q9wgofse7km2"; do
    [ "$(probe "$clean")" = miss ] || { echo "selftest: false hit '$clean'"; fail=1; }
  done
  # The registry arm and the reporting arm, end to end: an unregistered token is
  # reported, a registered one is not. Without this the selftest would certify
  # the regex alone while `classify` went blind.
  registered=$(head -n 1 "$registry")
  if printf 'a.lean:1:%s\n' "${affix}f01vn6s6n79wmqa8" | classify >/dev/null; then
    echo "selftest: classify passed an unregistered token"; fail=1
  fi
  if ! printf 'a.lean:1:%s\n' "$registered" | classify >/dev/null; then
    echo "selftest: classify rejected the registered token '$registered'"; fail=1
  fi
  # A leak sharing a line with a registered placeholder must still be reported.
  if printf 'a.lean:1:%s and %s\n' "$registered" "${affix}f01vn6s6n79wmqa8" | classify >/dev/null; then
    echo "selftest: classify stopped at the registered token on a mixed line"; fail=1
  fi
  # The scan itself, against a tracked blob git would classify as binary: the
  # arm that `-I` used to skip silently. Built through the same `scan` function
  # the real run uses, so the two cannot drift.
  probe_repo=$(mktemp -d)
  trap 'rm -rf "$probe_repo"' EXIT
  git -C "$probe_repo" init -q
  printf 'lead\000 %sf01vn6s6n79wmqa8 trail\n' "$affix" > "$probe_repo/blob.bin"
  git -C "$probe_repo" add -A
  if ! scan "$probe_repo" . >/dev/null 2>&1; then
    echo "selftest: the scan missed a token in a binary-classified tracked file"; fail=1
  fi
  files=$(scope_size)
  [ "$files" -gt 0 ] || { echo "selftest: the scan pathspec selected no files"; fail=1; }
  if [ "$fail" -ne 0 ]; then
    echo "::error::the task-id lint no longer detects what it claims to — repair scripts/check-task-ids.sh before trusting this gate."
    exit 1
  fi
  echo "task-id lint selftest ok ($files files in scope)"
  exit 0
fi

files=$(scope_size)
if [ "$files" -eq 0 ]; then
  echo "::error::the task-id scan selected no files — an empty scope must not report clean; repair the pathspec in scripts/check-task-ids.sh."
  exit 1
fi

# `printf '%s\n'`, not `%s`: command substitution already stripped the trailing
# newline, and `read` drops a final line that has none — which would silently
# lose the last hit.
hits=$(run_scan)
if ! printf '%s\n' "$hits" | classify; then
  echo "::error::task-tracker id in a tracked artifact. Code and comments must stand on their own — describe the substance instead (AGENTS.md, 'Artifacts must be human-readable'). If this token is a test or example placeholder rather than a tracker reference, register it in $registry in this same change."
  exit 1
fi
echo "task-id lint clean ($files files in scope)"
