#!/bin/sh
# Verify downloaded tl release artifacts exactly as VERIFYING.md tells a user
# to, against the identity pinned in release/identity.json.
#
#   scripts/verify-release-artifacts.sh [--require-signature] <dir> <asset>...
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
# copy drifts from `release/identity.json`, and
# `scripts/check-embedded-copies.sh` fails if its copies of the shared helpers
# drift from `scripts/lib/release-common.sh`.
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
#
# `--require-signature` refuses that escape outright. The release workflow
# passes it, because there the escape would be a silent downgrade of the one
# gate standing between a candidate and the public: without it, a
# `TL_INSTALL_SKIP_SIGNATURE=1` inherited from anywhere in the job environment
# turns "nothing is published that this procedure would reject" into comparing
# SHA256SUMS against itself. A user's escape hatch and a release gate's are not
# the same thing, and the difference has to be expressible.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
RC_LIB_SELF="$script_dir/lib/release-common.sh"
if [ ! -f "$RC_LIB_SELF" ]; then
  echo "verify-release-artifacts: scripts/lib/release-common.sh not found next to this script (looked at $RC_LIB_SELF) — it holds the digest and reporting helpers this verifier shares with the rest of the release machinery. Run it from a checkout." >&2
  exit 2
fi
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

usage() {
  echo "usage: $0 [--require-signature] <dir> <asset>... | $0 --selftest" >&2
  exit 2
}

# Locate release/identity.json relative to this script, so the installer can
# run from anywhere.
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

verify_dir() {
  require_signature=$1
  dir=$2
  shift 2
  [ -d "$dir" ] || fail "'$dir' is not a directory. Pass the directory the release assets were downloaded into, then the asset names within it — for example 'scripts/verify-release-artifacts.sh ~/Downloads tl-linux-x64'."
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
  # Both anchors, not just the head. cosign matches unanchored, so a missing
  # `^` accepts a certificate whose identity merely *contains* the pinned one —
  # and a missing `$` accepts one that merely *begins* with it, which is not
  # hypothetical: a git tag name may contain `/`, so
  # `…/release.yml@refs/tags/v1.0.0/anything` would satisfy a head-only pin.
  # Tests/ReleaseTests.lean already required both of release/identity.json;
  # this verifier checked only the first half.
  case $identity in
    '^'*) ;;
    *) fail "the pinned certificateIdentityRegexp is not anchored at ^ ('${identity}'). cosign matches unanchored, so an unanchored expression would accept a certificate whose identity merely *contains* this repository's — repair release/identity.json." ;;
  esac
  case $identity in
    *'$') ;;
    *) fail "the pinned certificateIdentityRegexp is not anchored at \$ ('${identity}'). cosign matches unanchored, so an expression without a tail anchor accepts any certificate identity that merely *begins* with this one — a tag name may contain '/', so trailing content is reachable. Repair release/identity.json." ;;
  esac

  sums="$dir/SHA256SUMS"
  [ -f "$sums" ] || fail "$sums not found — download SHA256SUMS from the same GitHub Release as the assets."

  skip_signature=0
  if [ "${TL_INSTALL_SKIP_SIGNATURE-}" = "1" ]; then
    if [ "$require_signature" -eq 1 ]; then
      fail "TL_INSTALL_SKIP_SIGNATURE=1 is set, but this run was invoked with --require-signature. That combination is refused rather than resolved: the caller is a release gate whose entire purpose is to reject anything the published verification procedure would reject, and honouring the escape here would reduce it to comparing SHA256SUMS against itself. Unset the variable in this environment."
    fi
    skip_signature=1
    echo "verify-release-artifacts: TL_INSTALL_SKIP_SIGNATURE=1 — skipping Sigstore checks. SHA-256 verification still applies; you are trusting that SHA256SUMS is authentic by some other means."
  elif ! command -v cosign >/dev/null 2>&1; then
    if [ "$require_signature" -eq 1 ]; then
      fail "cosign not found on PATH, and this run was invoked with --require-signature. A release gate cannot fall back to a digest-only check: install cosign in this job (sigstore/cosign-installer) before verifying candidates."
    fi
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

    # Pull this asset's line out of the sums file by exact name, and prove it
    # is a digest. Shared with the installer through the library, because the
    # two copies of this had already diverged on what they accepted.
    expected=$(rc_sums_digest "$sums" "$asset" 2>"$dir/.rc-sums-err") || {
      fail "$(cat "$dir/.rc-sums-err")"
    }
    rm -f "$dir/.rc-sums-err"

    # Both sides lowercased: `rc_sha256_of` always produces lowercase, and the
    # sums file may legitimately carry uppercase, which the hex check accepts.
    actual=$(rc_lower "$(rc_sha256_of "$path")") \
      || fail "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)."
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
# The Sigstore arms are exercised against the shared stub `cosign` placed first
# on PATH. That is deliberate: the stub covers *this script's* branching on a
# verifier verdict, which is what could regress here. Whether real cosign
# checks a Rekor inclusion proof correctly is cosign's own business, and the
# release workflow runs the real thing over real artifacts before publishing.
# ---------------------------------------------------------------------------
selftest() {
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  self=$script_dir/$(basename -- "$0")

  rc_selftest_begin "verify-release-artifacts" "$work"

  rc_write_stub_cosign "$work/bin" "$identity_file" "$work"

  # A release directory that verifies cleanly.
  fixture() {
    d="$work/$1"
    mkdir -p "$d"
    printf 'binary contents\n' > "$d/tl-linux-x64"
    digest=$(rc_sha256_of "$d/tl-linux-x64")
    printf '%s  tl-linux-x64\n' "$digest" > "$d/SHA256SUMS"
    printf '{}\n' > "$d/SHA256SUMS.sigstore.json"
    printf '{}\n' > "$d/tl-linux-x64.sigstore.json"
    echo "$d"
  }

  # Run the verifier with the stub first on PATH.
  verify() {
    PATH="$work/bin:$PATH" "$self" "$@"
  }
  # …and without it, for the cases that must not find cosign at all.
  verify_bare() {
    PATH="/usr/bin:/bin" "$self" "$@"
  }

  d=$(fixture happy)
  rc_expect_status 0 "a complete, consistent release verifies" verify "$d" tl-linux-x64

  d=$(fixture no-sums); rm "$d/SHA256SUMS"
  rc_expect_status 1 "a missing SHA256SUMS is refused" verify "$d" tl-linux-x64
  d=$(fixture no-sums-bundle); rm "$d/SHA256SUMS.sigstore.json"
  rc_expect_status 1 "a missing SHA256SUMS bundle is refused" verify "$d" tl-linux-x64
  d=$(fixture no-asset-bundle); rm "$d/tl-linux-x64.sigstore.json"
  rc_expect_status 1 "a missing per-asset bundle is refused" verify "$d" tl-linux-x64
  d=$(fixture no-asset); rm "$d/tl-linux-x64"
  rc_expect_status 1 "a missing asset is refused" verify "$d" tl-linux-x64

  d=$(fixture unlisted); printf 'deadbeef  some-other-asset\n' > "$d/SHA256SUMS"
  rc_expect_status 1 "an asset absent from SHA256SUMS is refused" verify "$d" tl-linux-x64
  d=$(fixture malformed); printf 'not-a-digest  tl-linux-x64\n' > "$d/SHA256SUMS"
  rc_expect_status 1 "a non-hex digest line is refused" verify "$d" tl-linux-x64
  d=$(fixture truncated); printf 'abcdef  tl-linux-x64\n' > "$d/SHA256SUMS"
  rc_expect_output 1 "not the 64" "a short digest line is refused as truncated, not as tampering" \
    verify "$d" tl-linux-x64
  d=$(fixture mismatch); printf 'tampered\n' >> "$d/tl-linux-x64"
  rc_expect_output 1 "digest mismatch" "a digest mismatch is refused" verify "$d" tl-linux-x64

  # An uppercase sums file is valid and must verify. The hex check accepts A-F
  # deliberately, so comparing case-sensitively against lowercase output would
  # report correct bytes as tampering — the worst possible false positive.
  d=$(fixture uppercase)
  awk '{ print toupper($1) "  " $2 }' "$d/SHA256SUMS" > "$d/SHA256SUMS.up"
  mv "$d/SHA256SUMS.up" "$d/SHA256SUMS"
  rc_expect_status 0 "an uppercase SHA256SUMS verifies rather than reading as tampering" \
    verify "$d" tl-linux-x64

  # Signature verdicts, via the stub.
  d=$(fixture bad-signature)
  rc_expect_output 1 "did not verify against the pinned identity" "a rejected signature is refused" \
    env COSIGN_STUB_VERDICT=bad PATH="$work/bin:$PATH" "$self" "$d" tl-linux-x64

  # The escape hatch drops signatures and keeps digests.
  d=$(fixture skip-ok); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  rc_expect_status 0 "TL_INSTALL_SKIP_SIGNATURE=1 verifies without bundles" \
    env TL_INSTALL_SKIP_SIGNATURE=1 PATH="/usr/bin:/bin" "$self" "$d" tl-linux-x64
  d=$(fixture skip-mismatch); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  printf 'tampered\n' >> "$d/tl-linux-x64"
  rc_expect_status 1 "TL_INSTALL_SKIP_SIGNATURE=1 still refuses a digest mismatch" \
    env TL_INSTALL_SKIP_SIGNATURE=1 PATH="/usr/bin:/bin" "$self" "$d" tl-linux-x64

  # --require-signature is the release gate's mode: the escape is refused, not
  # honoured, because a gate that can be switched off by an inherited
  # environment variable is not a gate. Both arms — the variable set, and
  # cosign simply absent — must refuse.
  d=$(fixture require-vs-skip)
  rc_expect_output 1 "invoked with --require-signature" \
    "--require-signature refuses an inherited TL_INSTALL_SKIP_SIGNATURE" \
    env TL_INSTALL_SKIP_SIGNATURE=1 PATH="$work/bin:$PATH" "$self" --require-signature "$d" tl-linux-x64
  d=$(fixture require-no-cosign)
  rc_expect_output 1 "cannot fall back to a digest-only check" \
    "--require-signature refuses when cosign is absent" \
    env PATH="/usr/bin:/bin" "$self" --require-signature "$d" tl-linux-x64
  d=$(fixture require-happy)
  rc_expect_status 0 "--require-signature still verifies a good release" \
    verify --require-signature "$d" tl-linux-x64

  # Without cosign and without the explicit opt-out, refuse rather than
  # silently degrade to a digest-only check.
  d=$(fixture no-cosign)
  rc_expect_output 1 "cosign not found" "a missing cosign is refused rather than skipped" \
    verify_bare "$d" tl-linux-x64

  # The pin itself. These run the script against a substituted identity file,
  # so they check what happens when the *pin* is broken rather than when an
  # artifact is.
  pin_case() {
    # pin_case <name> <expected-status> <needle> <identity-json-content>
    name=$1; want=$2; needle=$3; content=$4
    d=$(fixture "pin-$(echo "$name" | tr ' /$^' '____')")
    alt_root="$work/alt-$(echo "$name" | tr ' /$^' '____')"
    mkdir -p "$alt_root/scripts/lib" "$alt_root/release"
    cp "$self" "$alt_root/scripts/"
    cp "$RC_LIB_SELF" "$alt_root/scripts/lib/"
    printf '%s\n' "$content" > "$alt_root/release/identity.json"
    rc_expect_output "$want" "$needle" "$name" \
      env PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64
  }
  pin_case "a malformed identity.json is refused" 1 "repair the pin" '{ not json'
  pin_case "an identity.json without the issuer is refused" 1 "certificateOidcIssuer" \
    '{"certificateIdentityRegexp": "^x$"}'
  pin_case "an identity.json without the expression is refused" 1 "certificateIdentityRegexp" \
    '{"certificateOidcIssuer": "https://example.invalid"}'
  pin_case "an empty certificate expression is refused" 1 "empty certificateIdentityRegexp" \
    '{"certificateOidcIssuer": "https://example.invalid", "certificateIdentityRegexp": ""}'
  # An unanchored expression is the failure a text-equality drift guard cannot
  # see: it is well-formed, it verifies real artifacts, and it also accepts a
  # certificate whose identity merely contains this repository's.
  pin_case "an expression unanchored at the head is refused" 1 "not anchored at ^" \
    '{"certificateOidcIssuer": "https://example.invalid", "certificateIdentityRegexp": "https://github.com/x$"}'
  # The tail anchor is the half this verifier used to drop. A tag name may
  # contain a slash, so trailing content past the pinned identity is reachable.
  pin_case "an expression unanchored at the tail is refused" 1 "not anchored at" \
    '{"certificateOidcIssuer": "https://example.invalid", "certificateIdentityRegexp": "^https://github.com/x"}'

  # A verifier that cannot run must not be reported as tampering: the two
  # outcomes send a reader to entirely different places.
  d=$(fixture broken-verifier)
  rc_expect_output 1 "not evidence of tampering" \
    "a verifier that cannot run is not reported as tampering" \
    env COSIGN_STUB_VERDICT=broken PATH="$work/bin:$PATH" "$self" "$d" tl-linux-x64

  # Usage and argument handling: exit 2, distinct from a verification refusal.
  d=$(fixture usage)
  rc_expect_status 2 "no arguments is a usage error" verify
  rc_expect_status 2 "an unknown flag is a usage error" verify --bogus
  rc_expect_status 2 "--selftest with extra arguments is a usage error" verify --selftest extra
  rc_expect_status 2 "a directory with no assets named is a usage error" verify "$d"
  rc_expect_status 2 "--require-signature with no assets named is a usage error" \
    verify --require-signature "$d"
  rc_expect_output 1 "is not a directory" "a nonexistent directory refuses with a naming message" \
    verify "$work/no-such-dir" tl-linux-x64
  rc_expect_output 1 "for example" "the not-a-directory message shows the expected invocation" \
    verify "$work/no-such-dir" tl-linux-x64

  # What was actually passed to cosign, from the stub's own log of the happy
  # path. The transparency-log check is not ours to skip, and the bundle the
  # proof lives in has to be named on every call.
  if [ -s "$work/cosign-argv" ]; then
    if grep -q 'insecure-ignore-tlog' "$work/cosign-argv"; then
      rc_note 1 "cosign is never invoked with a transparency-log bypass"
    else
      rc_note 0 "cosign is never invoked with a transparency-log bypass"
    fi
    calls=$(grep -c 'verify-blob' "$work/cosign-argv" || true)
    bundles=$(grep -c -- '--bundle' "$work/cosign-argv" || true)
    if [ "$calls" -ge 2 ] && [ "$calls" = "$bundles" ]; then
      rc_note 0 "every cosign call names a bundle ($calls calls)"
    else
      rc_note 1 "every cosign call names a bundle ($calls verify-blob calls, $bundles with --bundle)"
    fi
    # Which blobs, not just how many calls. An aggregate count is satisfied by
    # the sums-file call alone, so deleting the per-asset check would pass it.
    : > "$work/cosign-blobs"
    d=$(fixture blob-coverage)
    rc_run verify "$d" tl-linux-x64
    if grep -qx SHA256SUMS "$work/cosign-blobs" && grep -qx tl-linux-x64 "$work/cosign-blobs"; then
      rc_note 0 "cosign is handed both the sums file and each asset"
    else
      rc_note 1 "cosign is handed both the sums file and each asset (saw: $(tr '\n' ' ' < "$work/cosign-blobs"))"
    fi
  else
    rc_note 1 "cosign was never invoked, so the signature checks did not run"
  fi

  rc_selftest_end "This verifier no longer refuses what it claims to refuse — repair it before trusting anything it accepts."
}

require_signature=0
case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  --require-signature)
    require_signature=1
    shift
    [ "$#" -gt 0 ] || usage
    case "${1-}" in
      -*) usage ;;
    esac
    verify_dir "$require_signature" "$@"
    ;;
  -*) usage ;;
  *) verify_dir "$require_signature" "$@" ;;
esac
