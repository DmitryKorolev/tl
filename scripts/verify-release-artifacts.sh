#!/bin/sh
# Verify downloaded tl release artifacts exactly as VERIFYING.md tells a user
# to, against the identity pinned in release/identity.json.
#
#   scripts/verify-release-artifacts.sh <dir> <asset>...
#   scripts/verify-release-artifacts.sh --selftest
#
# <dir> must contain, for each <asset>: the asset itself, `SHA256SUMS`,
# `SHA256SUMS.sigstore.json`, and `<asset>.sigstore.json`.
#
# Two callers: the release workflow runs it over the candidate artifacts before
# publishing them, so nothing is released that the published procedure would
# reject; and `--selftest` runs it against fabricated failures on every commit.
# A procedure documented but never executed is a procedure nobody has tested.
#
# `install.sh` performs the same checks but does not call this script — it is
# piped into a shell with no checkout to read, so it carries its own copy of
# the pinned issuer and expression. `Tests/ReleaseTests.lean` fails if that
# copy drifts from `release/identity.json`.
#
# Order matters and is not an accident. The signature on `SHA256SUMS` is
# checked *first*, because every digest comparison afterwards trusts that file;
# checking a digest against an unverified sums file proves only that the
# attacker was consistent.
#
# TL_INSTALL_SKIP_SIGNATURE=1 skips the Sigstore checks and keeps the SHA-256
# checks mandatory. It exists for an environment where cosign cannot run. It is
# not a weaker default and there is no flag for it: an environment variable
# someone had to set on purpose leaves a trace in shell history and CI logs.
set -eu

usage() {
  echo "usage: $0 <dir> <asset>... | $0 --selftest" >&2
  exit 2
}

# Locate release/identity.json relative to this script, so the installer can
# run from anywhere.
script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
identity_file="$script_dir/../release/identity.json"

fail() {
  echo "verify-release-artifacts: $1" >&2
  exit 1
}

# Read a string field from release/identity.json.
#
# Through a JSON parser, not sed. The certificate expression contains escaped
# dots, which JSON stores as `\\.` — a text scrape hands cosign a pattern
# meaning "a literal backslash followed by any character", which matches no
# real certificate at all. That failure is silent in the worst direction: it
# rejects every genuine signature, and it looks exactly like a verification
# failure rather than like a broken verifier.
identity_field() {
  python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' \
    "$identity_file" "$1" 2>/dev/null
}

# Run cosign and distinguish two very different outcomes. A verification
# failure means these bytes are not what this repository signed. Anything else
# — cosign missing a dependency, a broken pin file, no network for a trust-root
# refresh — is a problem with the checking apparatus, and reporting that as
# tampering sends the reader hunting for an attacker that is not there.
cosign_verify() {
  target=$1
  bundle_path=$2
  label=$3
  out=$(cosign verify-blob "$target" \
          --bundle "$bundle_path" \
          --certificate-oidc-issuer "$issuer" \
          --certificate-identity-regexp "$identity" 2>&1) && return 0
  case $out in
    *"no matching signatures"* | *"none of the expected identities matched"* | \
    *"certificate identity"* | *"invalid signature"* | *"inclusion proof"* | \
    *"transparency log"* | *"tlog"*)
      printf '%s\n' "$out" >&2
      fail "the signature on '$label' did not verify against the pinned identity. Do not use it. Re-download from the official release; if it still fails, these are not the artifacts this repository signed — report it rather than working around it."
      ;;
    *)
      printf '%s\n' "$out" >&2
      fail "cosign could not complete the check on '$label', so whether it is authentic is unknown — this is not evidence of tampering. The usual causes are a cosign version mismatch, no network for the trust-root refresh, or a damaged bundle file. Re-run once; if it persists, verify by hand with the commands in VERIFYING.md."
      ;;
  esac
}

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    fail "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)."
  fi
}

verify_dir() {
  dir=$1
  shift
  [ -d "$dir" ] || fail "'$dir' is not a directory"
  [ "$#" -gt 0 ] || usage

  [ -f "$identity_file" ] || fail "release/identity.json not found next to this script (looked at $identity_file) — without the pinned issuer and certificate identity a signature check would accept any valid Sigstore certificate, which is no check at all."
  command -v python3 >/dev/null 2>&1 \
    || fail "python3 not found — it reads the pinned identity out of release/identity.json. A text scrape would mangle the escapes in the certificate expression and silently reject every genuine signature, so there is no fallback. Install python3, or verify by hand with the commands in VERIFYING.md."

  issuer=$(identity_field certificateOidcIssuer) \
    || fail "release/identity.json has no certificateOidcIssuer, or is not valid JSON — repair the pin before verifying anything against it."
  identity=$(identity_field certificateIdentityRegexp) \
    || fail "release/identity.json has no certificateIdentityRegexp, or is not valid JSON — repair the pin before verifying anything against it."
  [ -n "$issuer" ] || fail "release/identity.json has an empty certificateOidcIssuer — an empty issuer would not constrain the certificate at all."
  [ -n "$identity" ] || fail "release/identity.json has an empty certificateIdentityRegexp — an empty expression matches every certificate, which is no check at all."
  case $identity in
    '^'*) ;;
    *) fail "the pinned certificateIdentityRegexp is not anchored at ^ ('${identity}'). cosign matches unanchored, so an unanchored expression would accept a certificate whose identity merely *contains* this repository's — repair release/identity.json." ;;
  esac

  sums="$dir/SHA256SUMS"
  [ -f "$sums" ] || fail "$sums not found — download SHA256SUMS from the same GitHub Release as the assets."

  skip_signature=0
  if [ "${TL_INSTALL_SKIP_SIGNATURE-}" = "1" ]; then
    skip_signature=1
    echo "verify-release-artifacts: TL_INSTALL_SKIP_SIGNATURE=1 — skipping Sigstore checks. SHA-256 verification still applies; you are trusting that SHA256SUMS is authentic by some other means."
  elif ! command -v cosign >/dev/null 2>&1; then
    fail "cosign not found on PATH — install it from https://github.com/sigstore/cosign/releases to verify the signatures. If cosign genuinely cannot run here, re-run with TL_INSTALL_SKIP_SIGNATURE=1, which keeps the SHA-256 checks and drops only the signature checks."
  fi

  # The sums file first: everything below trusts it.
  if [ "$skip_signature" -eq 0 ]; then
    bundle="$sums.sigstore.json"
    [ -f "$bundle" ] || fail "$bundle not found — download SHA256SUMS.sigstore.json from the same GitHub Release. Without it the sums file is unauthenticated, and every digest below would only prove internal consistency."
    cosign_verify "$sums" "$bundle" SHA256SUMS
    echo "verify-release-artifacts: SHA256SUMS signature ok"
  fi

  for asset in "$@"; do
    path="$dir/$asset"
    [ -f "$path" ] || fail "$path not found — the asset name must match the one in SHA256SUMS exactly."

    # Pull this asset's line out of the sums file by exact name. Not `sha256sum
    # -c`, which would check every line and fail on assets for other platforms
    # that were never downloaded.
    expected=$(awk -v want="$asset" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' "$sums") \
      || fail "SHA256SUMS has no entry named '$asset'. Either the asset was renamed after signing, or you are checking it against a different release's sums file."
    case "$expected" in
      *[!0-9a-fA-F]* | '')
        fail "the SHA256SUMS entry for '$asset' is not a hex digest ('$expected') — the file is malformed or truncated; re-download it."
        ;;
    esac
    if [ "${#expected}" -ne 64 ]; then
      fail "the SHA256SUMS entry for '$asset' is ${#expected} characters, not the 64 of a SHA-256 digest — the file is malformed or truncated; re-download it."
    fi

    actual=$(sha256_of "$path")
    if [ "$actual" != "$expected" ]; then
      fail "digest mismatch for '$asset': the file hashes to $actual but SHA256SUMS says $expected. Delete the download and fetch it again; if it still differs, do not run it."
    fi
    echo "verify-release-artifacts: $asset digest ok"

    if [ "$skip_signature" -eq 0 ]; then
      asset_bundle="$path.sigstore.json"
      [ -f "$asset_bundle" ] || fail "$asset_bundle not found — download the per-asset Sigstore bundle from the same GitHub Release. The bundle must carry the artifact signature, the certificate, and the Rekor inclusion proof; a missing bundle is a verification failure, not a reason to continue."
      cosign_verify "$path" "$asset_bundle" "$asset"
      echo "verify-release-artifacts: $asset signature ok"
    fi
  done

  echo "verify-release-artifacts: verified $# asset(s) in $dir"
}

# ---------------------------------------------------------------------------
# Selftest. Every refusal path above, in throwaway directories.
#
# The Sigstore arms are exercised against a stub `cosign` placed first on PATH.
# That is deliberate: the stub covers *this script's* branching on a verifier
# verdict, which is what could regress here. Whether real cosign checks a Rekor
# inclusion proof correctly is cosign's own business, and the release workflow
# runs the real thing over real artifacts before publishing.
# ---------------------------------------------------------------------------
selftest() {
  command -v git >/dev/null 2>&1 || true
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  failures=0
  self=$script_dir/$(basename -- "$0")

  # A stub cosign. It does two jobs: report a verdict from
  # COSIGN_STUB_VERDICT, and — more importantly — assert that it was handed
  # the pinned issuer and the pinned expression *exactly*, byte for byte
  # against release/identity.json read through a JSON parser.
  #
  # A stub that ignored its arguments would pass while this script fed cosign
  # a mangled expression, which is precisely the failure that reaches users as
  # "every genuine release is rejected". Argument checking is the part of the
  # stub that earns its keep.
  mkdir -p "$work/bin"
  cat > "$work/bin/cosign" <<STUB
#!/bin/sh
printf '%s\n' "\$*" >> "$work/cosign-argv"
want_issuer=\$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["certificateOidcIssuer"])' "$identity_file")
want_identity=\$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["certificateIdentityRegexp"])' "$identity_file")
got_issuer=''
got_identity=''
got_bundle=''
while [ \$# -gt 0 ]; do
  case \$1 in
    --certificate-oidc-issuer) got_issuer=\$2; shift 2 ;;
    --certificate-identity-regexp) got_identity=\$2; shift 2 ;;
    --bundle) got_bundle=\$2; shift 2 ;;
    --insecure-ignore-tlog*)
      echo "stub cosign: called with \$1 — the transparency-log check must never be bypassed" >&2
      exit 90
      ;;
    *) shift ;;
  esac
done
[ "\$got_issuer" = "\$want_issuer" ] || {
  echo "stub cosign: issuer '\$got_issuer' is not the pinned '\$want_issuer'" >&2
  exit 91
}
[ "\$got_identity" = "\$want_identity" ] || {
  echo "stub cosign: identity expression '\$got_identity' is not the pinned '\$want_identity'" >&2
  exit 92
}
[ -n "\$got_bundle" ] || { echo "stub cosign: no --bundle was passed" >&2; exit 93; }
[ -f "\$got_bundle" ] || { echo "stub cosign: bundle '\$got_bundle' does not exist" >&2; exit 94; }
case "\${COSIGN_STUB_VERDICT:-ok}" in
  ok) ;;
  bad)
    # The shape cosign really prints when the certificate does not match.
    echo "error: no matching signatures: none of the expected identities matched what was in the certificate" >&2
    exit 1
    ;;
  broken)
    # Anything that is not a verdict: a verifier problem, not tampering.
    echo "error: fetching trust root: Get \"https://tuf-repo-cdn.sigstore.dev/\": dial tcp: lookup failed" >&2
    exit 1
    ;;
esac
echo "Verified OK"
exit 0
STUB
  chmod +x "$work/bin/cosign"

  # A release directory that verifies cleanly.
  fixture() {
    d="$work/$1"
    mkdir -p "$d"
    printf 'binary contents\n' > "$d/tl-linux-x64"
    digest=$(sha256_of "$d/tl-linux-x64")
    printf '%s  tl-linux-x64\n' "$digest" > "$d/SHA256SUMS"
    printf '{}\n' > "$d/SHA256SUMS.sigstore.json"
    printf '{}\n' > "$d/tl-linux-x64.sigstore.json"
    echo "$d"
  }

  note_ok() { echo "  ok   $1"; }
  note_fail() {
    echo "  FAIL $1" >&2
    [ "$2" = /dev/null ] || sed 's/^/    /' "$2" >&2
    failures=$((failures + 1))
  }
  expect_status() {
    dir=$1; want=$2; name=$3
    got=0
    ( PATH="$work/bin:$PATH" "$self" "$dir" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
    if [ "$got" -ne "$want" ]; then
      echo "  FAIL $name: expected exit $want, got $got" >&2
      sed 's/^/    /' "$work/err" >&2
      failures=$((failures + 1))
      return 0
    fi
    echo "  ok   $name (exit $got)"
  }

  echo "verify-release-artifacts --selftest:"

  d=$(fixture happy); expect_status "$d" 0 "a complete, consistent release verifies"

  d=$(fixture no-sums); rm "$d/SHA256SUMS"
  expect_status "$d" 1 "a missing SHA256SUMS is refused"
  d=$(fixture no-sums-bundle); rm "$d/SHA256SUMS.sigstore.json"
  expect_status "$d" 1 "a missing SHA256SUMS bundle is refused"
  d=$(fixture no-asset-bundle); rm "$d/tl-linux-x64.sigstore.json"
  expect_status "$d" 1 "a missing per-asset bundle is refused"
  d=$(fixture no-asset); rm "$d/tl-linux-x64"
  expect_status "$d" 1 "a missing asset is refused"

  d=$(fixture unlisted); printf 'deadbeef  some-other-asset\n' > "$d/SHA256SUMS"
  expect_status "$d" 1 "an asset absent from SHA256SUMS is refused"
  d=$(fixture malformed); printf 'not-a-digest  tl-linux-x64\n' > "$d/SHA256SUMS"
  expect_status "$d" 1 "a non-hex digest line is refused"
  d=$(fixture truncated); printf 'abcdef  tl-linux-x64\n' > "$d/SHA256SUMS"
  expect_status "$d" 1 "a short digest line is refused"
  d=$(fixture mismatch); printf 'tampered\n' >> "$d/tl-linux-x64"
  expect_status "$d" 1 "a digest mismatch is refused"

  # Signature verdicts, via the stub.
  d=$(fixture bad-signature)
  got=0
  ( PATH="$work/bin:$PATH" COSIGN_STUB_VERDICT=bad "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ]; then
    echo "  ok   a rejected signature is refused (exit 1)"
  else
    echo "  FAIL a rejected signature is refused: expected exit 1, got $got" >&2
    failures=$((failures + 1))
  fi

  # The escape hatch drops signatures and keeps digests.
  d=$(fixture skip-ok); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  got=0
  ( PATH="/usr/bin:/bin" TL_INSTALL_SKIP_SIGNATURE=1 "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 0 ]; then
    echo "  ok   TL_INSTALL_SKIP_SIGNATURE=1 verifies without bundles (exit 0)"
  else
    echo "  FAIL TL_INSTALL_SKIP_SIGNATURE=1 verifies without bundles: expected exit 0, got $got" >&2
    sed 's/^/    /' "$work/err" >&2
    failures=$((failures + 1))
  fi
  d=$(fixture skip-mismatch); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  printf 'tampered\n' >> "$d/tl-linux-x64"
  got=0
  ( PATH="/usr/bin:/bin" TL_INSTALL_SKIP_SIGNATURE=1 "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ]; then
    echo "  ok   TL_INSTALL_SKIP_SIGNATURE=1 still refuses a digest mismatch (exit 1)"
  else
    echo "  FAIL TL_INSTALL_SKIP_SIGNATURE=1 still refuses a digest mismatch: expected exit 1, got $got" >&2
    failures=$((failures + 1))
  fi

  # Without cosign and without the explicit opt-out, refuse rather than
  # silently degrade to a digest-only check.
  d=$(fixture no-cosign)
  got=0
  ( PATH="/usr/bin:/bin" "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ] && grep -q "cosign not found" "$work/err"; then
    echo "  ok   a missing cosign is refused rather than skipped (exit 1)"
  else
    echo "  FAIL a missing cosign is refused rather than skipped: expected exit 1 naming cosign, got $got" >&2
    sed 's/^/    /' "$work/err" >&2
    failures=$((failures + 1))
  fi

  # The pin itself. These run the script against a substituted identity file,
  # so they check what happens when the *pin* is broken rather than when an
  # artifact is.
  pin_case() {
    # pin_case <name> <expected-status> <identity-json-content>
    name=$1; want=$2; content=$3
    d=$(fixture "pin-$(echo "$name" | tr ' /' '__')")
    alt_root="$work/alt-$(echo "$name" | tr ' /' '__')"
    mkdir -p "$alt_root/scripts" "$alt_root/release"
    cp "$self" "$alt_root/scripts/"
    printf '%s\n' "$content" > "$alt_root/release/identity.json"
    got=0
    ( PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64 \
        >"$work/out" 2>"$work/err" ) || got=$?
    if [ "$got" -eq "$want" ]; then
      echo "  ok   $name (exit $got)"
    else
      echo "  FAIL $name: expected exit $want, got $got" >&2
      sed 's/^/    /' "$work/err" >&2
      failures=$((failures + 1))
    fi
  }
  pin_case "a malformed identity.json is refused" 1 '{ not json'
  pin_case "an identity.json without the issuer is refused" 1 \
    '{"certificateIdentityRegexp": "^x$"}'
  pin_case "an identity.json without the expression is refused" 1 \
    '{"certificateOidcIssuer": "https://example.invalid"}'
  pin_case "an empty certificate expression is refused" 1 \
    '{"certificateOidcIssuer": "https://example.invalid", "certificateIdentityRegexp": ""}'
  # An unanchored expression is the failure a text-equality drift guard cannot
  # see: it is well-formed, it verifies real artifacts, and it also accepts a
  # certificate whose identity merely contains this repository's.
  pin_case "an unanchored certificate expression is refused" 1 \
    '{"certificateOidcIssuer": "https://example.invalid", "certificateIdentityRegexp": "https://github.com/x"}'

  # A verifier that cannot run must not be reported as tampering: the two
  # outcomes send a reader to entirely different places.
  d=$(fixture broken-verifier)
  got=0
  ( PATH="$work/bin:$PATH" COSIGN_STUB_VERDICT=broken "$self" "$d" tl-linux-x64 \
      >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ] && grep -q 'not evidence of tampering' "$work/err"; then
    note_ok "a verifier that cannot run is not reported as tampering"
  else
    note_fail "a verifier that cannot run is not reported as tampering" "$work/err"
  fi
  d=$(fixture rejected-cert)
  got=0
  ( PATH="$work/bin:$PATH" COSIGN_STUB_VERDICT=bad "$self" "$d" tl-linux-x64 \
      >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ] && grep -q 'did not verify against the pinned identity' "$work/err"; then
    note_ok "a rejected certificate is reported as a verification failure"
  else
    note_fail "a rejected certificate is reported as a verification failure" "$work/err"
  fi

  # Usage and argument handling: exit 2, distinct from a verification refusal.
  d=$(fixture usage)
  for args in "" "--bogus" "--selftest extra" "$d"; do
    got=0
    # shellcheck disable=SC2086
    ( PATH="$work/bin:$PATH" "$self" $args >/dev/null 2>&1 ) || got=$?
    if [ "$got" -eq 2 ]; then
      note_ok "'$args' is a usage error (exit 2)"
    else
      note_fail "'$args' is a usage error (got exit $got)" /dev/null
    fi
  done
  got=0
  ( PATH="$work/bin:$PATH" "$self" "$work/no-such-dir" tl-linux-x64 >/dev/null 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ] && grep -q 'is not a directory' "$work/err"; then
    note_ok "a nonexistent directory refuses with a naming message"
  else
    note_fail "a nonexistent directory refuses with a naming message" "$work/err"
  fi

  # What was actually passed to cosign, from the stub's own log of the happy
  # path. The transparency-log check is not ours to skip, and the bundle the
  # proof lives in has to be named on every call.
  if [ -s "$work/cosign-argv" ]; then
    if grep -q 'insecure-ignore-tlog' "$work/cosign-argv"; then
      echo "  FAIL cosign is never invoked with a transparency-log bypass" >&2
      failures=$((failures + 1))
    else
      echo "  ok   cosign is never invoked with a transparency-log bypass"
    fi
    calls=$(grep -c 'verify-blob' "$work/cosign-argv" || true)
    bundles=$(grep -c -- '--bundle' "$work/cosign-argv" || true)
    if [ "$calls" -ge 2 ] && [ "$calls" = "$bundles" ]; then
      echo "  ok   every cosign call names a bundle ($calls calls)"
    else
      echo "  FAIL every cosign call names a bundle ($calls verify-blob calls, $bundles with --bundle)" >&2
      failures=$((failures + 1))
    fi
  else
    echo "  FAIL cosign was never invoked, so the signature checks did not run" >&2
    failures=$((failures + 1))
  fi

  if [ "$failures" -ne 0 ]; then
    echo "verify-release-artifacts: --selftest found $failures broken case(s). This verifier no longer refuses what it claims to refuse — repair it before trusting anything it accepts." >&2
    exit 1
  fi
  echo "verify-release-artifacts: --selftest passed"
  exit 0
}

case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  -*) usage ;;
  *) verify_dir "$@" ;;
esac
