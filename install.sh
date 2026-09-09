#!/bin/sh
# tl installer.
#
#   curl -fsSL https://raw.githubusercontent.com/DmitryKorolev/tl/main/install.sh | sh
#
# Downloads the release binary for this platform from GitHub Releases, verifies
# it, and installs it. Environment:
#
#   TL_VERSION                 tag to install (default: the latest release)
#   TL_INSTALL_DIR             where to put the binary (default: ~/.local/bin)
#   TL_INSTALL_SKIP_SIGNATURE  set to 1 to skip the Sigstore checks only; the
#                              SHA-256 check stays mandatory
#   TL_INSTALL_BASE_URL        fetch the assets from here instead of GitHub
#                              (used by --selftest; also useful for a mirror)
#
# Verification is not optional and not best-effort. The signature on
# SHA256SUMS is checked first, because every digest below is compared against
# that file — checking a digest against an unverified sums file would prove
# only that whoever produced both was consistent. The certificate identity and
# issuer below are pinned: without them a "valid Sigstore signature" means only
# that *somebody* signed this, which is not a check.
#
# These two values are a copy of release/identity.json. That copy is
# deliberate — a piped installer cannot read a file out of the repository — and
# Tests/ReleaseTests.lean fails if it ever drifts from the canonical pin.
set -eu

TL_ISSUER='https://token.actions.githubusercontent.com'
TL_IDENTITY='^https://github\.com/DmitryKorolev/tl/\.github/workflows/release\.yml@refs/tags/v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$'
TL_REPO='DmitryKorolev/tl'

die() {
  echo "tl-install: $1" >&2
  exit 1
}

need() {
  command -v "$1" >/dev/null 2>&1 || die "$2"
}

# Verify one blob, and tell apart the two outcomes that look alike from the
# outside. A rejected certificate means these bytes are not what this
# repository signed. Anything else — cosign missing a dependency, no network
# for the trust-root refresh, a damaged bundle — means the check did not run,
# and calling that tampering sends the reader hunting for an attacker who is
# not there.
verify_signature() {
  blob=$1
  bundle=$2
  label=$3
  out=$(cosign verify-blob "$blob" \
          --bundle "$bundle" \
          --certificate-oidc-issuer "$TL_ISSUER" \
          --certificate-identity-regexp "$TL_IDENTITY" 2>&1) && return 0
  printf '%s\n' "$out" >&2
  case $out in
    *"no matching signatures"* | *"none of the expected identities matched"* | \
    *"certificate identity"* | *"invalid signature"* | *"inclusion proof"* | \
    *"transparency log"* | *"tlog"*)
      die "the signature on ${label} did not verify against this repository's pinned release identity. Nothing has been installed. Do not work around this — re-run to rule out a corrupted download, and if it persists, report it at https://github.com/${TL_REPO}/issues."
      ;;
    *)
      die "cosign could not complete the check on ${label}, so whether it is authentic is unknown — this is not evidence of tampering. Nothing has been installed. The usual causes are a cosign version mismatch or no network for the trust-root refresh; re-run once, and if it persists, verify by hand with the commands in VERIFYING.md."
      ;;
  esac
}

# The platform mapping and the digest helper below live here rather than in a
# shared library, because this script is piped straight into a shell and has no
# checkout to source from.
#
# They are held to different things, because they are different kinds of claim.
# The mapping is a decision — which uname is which target — and `tlrelease
# platform-classification` compares the marked block below against the typed
# authority in release/Platform.lean, which is itself cross-checked against
# release/targets.json. The digest and case helpers are behaviour, and the
# installer corpus in Tests/ReleaseToolTests.lean runs this script over a
# planted release to establish what they actually do: a correct digest installs,
# the same digest in uppercase also installs, a wrong one is refused as a
# mismatch, and with no digest tool on PATH nothing installs at all.
# EMBEDDED-COPY-BEGIN detect_os
detect_os() {
  case $(uname -s) in
    Darwin) install_os=darwin ;;
    Linux) install_os=linux ;;
    MINGW* | MSYS* | CYGWIN* | Windows_NT)
      die "native Windows is not supported — tl's filesystem primitives are unimplemented there, so a binary would start but could not safely create or mutate task state. Install inside WSL2, where this script installs the Linux build and everything is supported."
      ;;
    *)
      die "unsupported operating system '$(uname -s)'. tl publishes binaries for Linux and macOS only; to use it elsewhere, build from source with Lean 4 (see https://github.com/${TL_REPO})."
      ;;
  esac
}
# EMBEDDED-COPY-END detect_os
# EMBEDDED-COPY-BEGIN detect_arch
detect_arch() {
  case $(uname -m) in
    arm64 | aarch64) install_arch=arm64 ;;
    x86_64 | amd64) install_arch=x64 ;;
    *)
      die "unsupported CPU architecture '$(uname -m)'. tl publishes arm64 and x86-64 binaries; to use it elsewhere, build from source with Lean 4 (see https://github.com/${TL_REPO})."
      ;;
  esac
}
# EMBEDDED-COPY-END detect_arch

detect_target() {
  detect_os
  detect_arch
  # `uname -m` reports the architecture of the *process*, not of the machine.
  # Under Rosetta 2 an x86-64 shell on an Apple-silicon Mac reports x86_64, so
  # this script would otherwise install the Best-effort Intel binary — or, on a
  # release whose Best-effort leg failed, report no asset at all — on hardware
  # that has a Supported native build. Say so rather than silently downgrading.
  if [ "$install_os" = darwin ] && [ "$install_arch" = x64 ] \
     && [ "$(sysctl -n sysctl.proc_translated 2>/dev/null || echo 0)" = 1 ]; then
    echo "tl-install: this shell is running under Rosetta on Apple silicon, so it reports an x86-64 architecture and this script would install the Best-effort Intel binary. For the Supported native build, re-run from a native arm64 shell (for example 'arch -arm64 /bin/sh')." >&2
  fi
  asset="tl-${install_os}-${install_arch}"
}

# EMBEDDED-COPY-BEGIN sha256_of
sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    digest_out=$(sha256sum "$1") || digest_out=''
  elif command -v shasum >/dev/null 2>&1; then
    digest_out=$(shasum -a 256 "$1") || digest_out=''
  else
    echo "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)." >&2
    return 1
  fi
  if [ -z "$digest_out" ]; then
    echo "the digest tool on PATH produced no output for '$1' — it is present but not working. The digest check is mandatory and cannot be skipped; repair the installation of coreutils or shasum." >&2
    return 1
  fi
  printf '%s' "${digest_out%% *}"
}
# EMBEDDED-COPY-END sha256_of

# EMBEDDED-COPY-BEGIN lower
lower() {
  printf '%s' "$1" | tr 'ABCDEF' 'abcdef'
}
# EMBEDDED-COPY-END lower

fetch() {
  # $1 url, $2 destination. Fails loudly: a partial or 404 download that is
  # later "verified" against a sums file from the same source proves nothing,
  # so nothing continues past a failed fetch.
  # --proto and --proto-redir together, so neither the request nor a redirect
  # can drop to cleartext. There is no unrestricted retry: a fallback that
  # permits what the first call refuses would make the restriction decorative.
  curl -fsSL --retry 3 --proto '=https,file' --proto-redir '=https,file' \
       -o "$2" "$1" \
    || die "could not download $1. Check the network and that the release exists; if you passed TL_VERSION, confirm that tag has published assets. Only https (and file:// for a local mirror) is accepted, including after a redirect."
}

# Turn the effective URL of /releases/latest into a tag, or refuse. Split out
# from the fetch so the three outcomes are reachable without a network: the
# selftest sources this file and calls it directly. The curl below stays
# untested here — asserting that GitHub still redirects is not this script's
# job, and doing it would make the suite depend on the network.
version_from_effective_url() {
  effective=$1
  case $effective in
    */releases)
      # GitHub answers /releases/latest with the releases index when every
      # release is a prerelease, so this is "nothing stable yet", not a broken
      # redirect.
      die "https://github.com/${TL_REPO} has no stable release yet — /releases/latest resolved to the releases index, which is what GitHub returns when only prereleases exist. Pick one explicitly, for example TL_VERSION=v0.1.0-rc.1, from https://github.com/${TL_REPO}/releases."
      ;;
  esac
  version=${effective##*/}
  case $version in
    v[0-9]*) ;;
    *) die "could not work out the latest version from '${effective}' — GitHub's redirect changed shape. Set TL_VERSION to a tag such as v0.1.0 and report this at https://github.com/${TL_REPO}/issues." ;;
  esac
  printf '%s\n' "$version"
}

resolve_version() {
  if [ -n "${TL_VERSION-}" ]; then
    version=$TL_VERSION
    return 0
  fi
  if [ -n "${TL_INSTALL_BASE_URL-}" ]; then
    die "TL_INSTALL_BASE_URL is set but TL_VERSION is not. A custom asset location has no 'latest' to resolve, so name the version explicitly."
  fi
  # The redirect target of /releases/latest names the tag, which avoids a JSON
  # parse and avoids the API rate limit an unauthenticated curl would hit.
  # --proto/--proto-redir for the same reason `fetch` carries them: a redirect
  # must not be able to walk this request down to cleartext, where the tag we
  # resolve — and therefore which release gets installed — would be chosen by
  # whoever is on the path.
  latest_url=$(curl -fsSLI -o /dev/null -w '%{url_effective}' \
    --proto '=https' --proto-redir '=https' \
    "https://github.com/${TL_REPO}/releases/latest" 2>/dev/null) \
    || die "could not reach GitHub to find the latest release. Check the network, or set TL_VERSION to install a specific tag."
  version=$(version_from_effective_url "$latest_url")
}

# Fetch, verify and place the third-party notice. Returns non-zero on any
# problem, having said what happened; the caller does not treat that as fatal.
#
# The digest checks are the binary path's, not a shortened version of them: the
# hex-shape and 64-character tests are what separate "this file is corrupt"
# from "these bytes are not what was signed", and the first version of this
# helper omitted both — so a truncated sums line told the user a signed-release
# integrity check had failed.
install_notice() {
  notice=$1
  expected=$2
  case $expected in
    *[!0-9a-fA-F]* | '')
      echo "tl-install: the SHA256SUMS entry for ${notice} is not a hex digest, so the notice was not installed. The file is corrupt or truncated; the binary is installed and verified. 'tl licenses' prints the same content." >&2
      return 1
      ;;
  esac
  if [ "${#expected}" -ne 64 ]; then
    echo "tl-install: the SHA256SUMS entry for ${notice} is ${#expected} characters, not the 64 of a SHA-256 digest, so the notice was not installed. The file is corrupt or truncated; the binary is installed and verified." >&2
    return 1
  fi
  if ! curl -fsSL --retry 3 --proto '=https,file' --proto-redir '=https,file' \
         -o "$work/$notice" "${base}/${notice}" 2>/dev/null; then
    echo "tl-install: could not download ${notice}, so it was not installed. The binary is installed and verified; 'tl licenses' prints the same content." >&2
    return 1
  fi
  actual=$(sha256_of "$work/$notice") || {
    echo "tl-install: no sha256sum or shasum on PATH, so ${notice} could not be checked and was not installed." >&2
    return 1
  }
  if [ "$(lower "$actual")" != "$(lower "$expected")" ]; then
    echo "tl-install: digest mismatch for ${notice}: downloaded ${actual}, expected ${expected}. It was not installed. The binary itself is installed and was verified against this same signed sums file, so this is a problem with the notice asset alone — report it if it persists." >&2
    return 1
  fi
  share_dir=${TL_INSTALL_SHARE_DIR:-"$(dirname -- "$install_dir")/share/tl"}
  if mkdir -p "$share_dir" 2>/dev/null && cp "$work/$notice" "$share_dir/$notice" 2>/dev/null; then
    echo "tl-install: ${notice} installed at ${share_dir}/${notice}"
    return 0
  fi
  echo "tl-install: could not write ${share_dir}; the notice is not installed. It is published with the release, and 'tl licenses' prints the same content from the binary." >&2
  return 1
}

main() {
  need curl "curl not found — this installer downloads over HTTPS and needs it. Install curl, or download the binary manually from https://github.com/${TL_REPO}/releases and verify it per VERIFYING.md."
  detect_target
  resolve_version

  base=${TL_INSTALL_BASE_URL:-"https://github.com/${TL_REPO}/releases/download/${version}"}
  install_dir=${TL_INSTALL_DIR:-"$HOME/.local/bin"}

  skip_signature=0
  if [ "${TL_INSTALL_SKIP_SIGNATURE-}" = "1" ]; then
    skip_signature=1
    echo "tl-install: TL_INSTALL_SKIP_SIGNATURE=1 — skipping the signature checks. The SHA-256 check still runs, but you are trusting that SHA256SUMS is authentic by some other means."
  elif ! command -v cosign >/dev/null 2>&1; then
    die "cosign not found. It verifies that these artifacts were signed by this repository's release workflow, which is the check that makes a download trustworthy. Install it from https://github.com/sigstore/cosign/releases and re-run. If cosign genuinely cannot run here, re-run with TL_INSTALL_SKIP_SIGNATURE=1 — that drops only the signature check and keeps SHA-256."
  fi

  work=$(mktemp -d)
  # `staged` is the temporary inside the *install* directory (see the atomic
  # replace below), so it is not covered by removing $work. It is named here
  # and swept by the same trap: an interrupted install would otherwise leave a
  # `.tl.install.<pid>` file sitting in the user's bin directory forever, one
  # per attempt. INT and TERM as well as EXIT, because a Ctrl-C during the
  # download is the common case and a bare EXIT trap does not fire for it in
  # every shell.
  staged=''
  trap 'rm -rf "$work"; [ -z "$staged" ] || rm -f "$staged"' EXIT INT TERM

  echo "tl-install: installing ${asset} from ${version}"
  fetch "${base}/${asset}" "$work/$asset"
  fetch "${base}/SHA256SUMS" "$work/SHA256SUMS"

  # The sums file first: everything after this trusts it.
  if [ "$skip_signature" -eq 0 ]; then
    fetch "${base}/SHA256SUMS.sigstore.json" "$work/SHA256SUMS.sigstore.json"
    verify_signature "$work/SHA256SUMS" "$work/SHA256SUMS.sigstore.json" SHA256SUMS
    echo "tl-install: SHA256SUMS signature verified"
  fi

  expected=$(awk -v want="$asset" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' \
    "$work/SHA256SUMS") \
    || die "SHA256SUMS from ${version} has no entry for ${asset}. That release may not publish a binary for this platform; check https://github.com/${TL_REPO}/releases/tag/${version}."
  case $expected in
    *[!0-9a-fA-F]* | '') die "the SHA256SUMS entry for ${asset} is not a hex digest. The file is corrupt or truncated; re-run to download it again." ;;
  esac
  # A truncated sums line is a broken download, not a tampered binary, and the
  # two send the reader to entirely different places. Without this the short
  # digest simply fails the comparison below and is reported as tampering.
  [ "${#expected}" -eq 64 ] \
    || die "the SHA256SUMS entry for ${asset} is ${#expected} characters, not the 64 of a SHA-256 digest. The file is corrupt or truncated; re-run to download it again."
  # Compared in one case. `sha256_of` always produces lowercase, while a sums
  # file regenerated by other tooling may legitimately carry uppercase — which
  # the hex check above deliberately accepts. Comparing them as-is would call
  # correct bytes tampering, the one verdict this script must not get wrong.
  actual=$(sha256_of "$work/$asset") \
    || die "no sha256sum or shasum found. The digest check is mandatory and there is no way to skip it; install coreutils (Linux) or use the system shasum (macOS)."
  [ "$(lower "$actual")" = "$(lower "$expected")" ] \
    || die "digest mismatch for ${asset}: downloaded ${actual}, expected ${expected}. Nothing has been installed. Re-run to rule out a corrupted download; if it persists, do not run the binary — report it at https://github.com/${TL_REPO}/issues."
  echo "tl-install: ${asset} digest verified"

  if [ "$skip_signature" -eq 0 ]; then
    fetch "${base}/${asset}.sigstore.json" "$work/${asset}.sigstore.json"
    verify_signature "$work/$asset" "$work/${asset}.sigstore.json" "$asset"
    echo "tl-install: ${asset} signature verified"
  fi

  mkdir -p "$install_dir" 2>/dev/null \
    || die "could not create ${install_dir}. Choose a writable location with TL_INSTALL_DIR=/some/dir, or create that directory first."
  [ -w "$install_dir" ] \
    || die "${install_dir} is not writable. Set TL_INSTALL_DIR to a directory you own (for example TL_INSTALL_DIR=\"\$HOME/.local/bin\"), or re-run with elevated privileges if a system-wide install is what you want."

  chmod +x "$work/$asset"
  # `mv -f file dir` moves the file *into* dir rather than replacing it, so a
  # directory sitting where the binary belongs would end up holding
  # `tl/.tl.install.<pid>` while every step below reported success and nothing
  # landed on PATH. Refuse before staging instead: a non-file here is somebody
  # else's, and silently burying a binary inside it is not a repair.
  if [ -e "$install_dir/tl" ] && [ ! -f "$install_dir/tl" ]; then
    die "${install_dir}/tl exists and is not a regular file, so it cannot be replaced by the binary. Remove or rename it, or choose another location with TL_INSTALL_DIR."
  fi
  # Install through a rename within the destination directory, so a concurrent
  # `tl` either sees the old binary or the new one — never a half-written file.
  # The temporary lives in $install_dir rather than $work because a rename
  # across filesystems is not atomic and would fall back to a copy.
  staged="$install_dir/.tl.install.$$"
  cp "$work/$asset" "$staged" \
    || die "could not write to ${install_dir}. Choose a writable location with TL_INSTALL_DIR."
  chmod +x "$staged"
  mv -f "$staged" "$install_dir/tl" \
    || die "could not replace ${install_dir}/tl. Close any running tl and re-run, or choose another TL_INSTALL_DIR."
  # The rename consumed it; clear the name so the trap does not chase a path
  # that is now the installed binary.
  staged=''

  # ADR-0006: the third-party notice travels with every distribution artifact.
  # The npm packages bundle it because a package has somewhere to put it; a
  # bare binary does not, so the release publishes it as a companion asset and
  # the installer places it beside the binary. Verified against the same signed
  # SHA256SUMS as everything else — an unverified notice would be a file
  # claiming to describe what you just installed, from nobody in particular.
  #
  # Skipped, with a note, for a release that does not list it: `TL_VERSION` can
  # name an older tag, and refusing to install a perfectly good binary over a
  # missing notice would be the wrong trade.
  # Nothing below may fail the install. The binary is already in place and
  # verified by this point, so a problem with the sidecar is a *warning* about
  # the sidecar — the previous shape called `fetch`, which dies, so a release
  # that listed the notice but could not serve it exited 1 having installed the
  # binary, printing neither the success line nor the PATH advice. A licence
  # file the user can also get from `tl licenses` is not worth failing over.
  notice=THIRD-PARTY-LICENSES
  notice_expected=$(awk -v want="$notice" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' "$work/SHA256SUMS") || notice_expected=''
  if [ -z "$notice_expected" ]; then
    echo "tl-install: ${version} publishes no ${notice} asset, so none was installed. 'tl licenses' prints the same content from the binary."
  else
    install_notice "$notice" "$notice_expected" || true
  fi

  echo "tl-install: installed ${install_dir}/tl"
  case ":${PATH}:" in
    *":${install_dir}:"*) ;;
    *) echo "tl-install: ${install_dir} is not on your PATH — add it (for example, append 'export PATH=\"${install_dir}:\$PATH\"' to your shell profile) or invoke ${install_dir}/tl directly." ;;
  esac
  "$install_dir/tl" version || true
}

# ---------------------------------------------------------------------------
# Selftest: every refusal path, against a fabricated local release. Run from a
# checkout: `sh install.sh --selftest`.
# ---------------------------------------------------------------------------
selftest() {
  # The selftest runs from a checkout, so the stub can read the published pin
  # and compare it against what install.sh actually passes. install.sh itself
  # keeps its embedded copy: it has no checkout when piped from curl.
  TL_IDENTITY_FILE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)/release/identity.pin
  [ -f "$TL_IDENTITY_FILE" ] || {
    echo "tl-install: --selftest needs release/identity.pin beside this script (looked at $TL_IDENTITY_FILE) — run it from a checkout." >&2
    exit 2
  }
  # The selftest runs from a checkout, so unlike `main` it *can* use the shared
  # library — and does, for the stub cosign and the reporting harness that were
  # previously copy-pasted between here and the artifact verifier.
  repo_root=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
  RC_LIB_SELF="$repo_root/scripts/lib/release-common.sh"
  [ -f "$RC_LIB_SELF" ] || {
    echo "tl-install: --selftest needs scripts/lib/release-common.sh beside this script — run it from a checkout." >&2
    exit 2
  }
  # shellcheck source=scripts/lib/release-common.sh
  . "$RC_LIB_SELF"

  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  failures=0
  case $0 in
    /*) self=$0 ;;
    *) self="$(pwd -P)/$0" ;;
  esac

  note() {
    if [ "$1" -eq 0 ]; then
      echo "  ok   $2"
    else
      echo "  FAIL $2" >&2
      failures=$((failures + 1))
    fi
  }

  bin="$work/bin"
  rc_write_stub_cosign "$bin" "$TL_IDENTITY_FILE" "$work"

  host_os=$(uname -s)
  host_arch=$(uname -m)
  case $host_os in
    Darwin) target_os=darwin ;;
    *) target_os=linux ;;
  esac
  case $host_arch in
    arm64 | aarch64) target_arch=arm64 ;;
    *) target_arch=x64 ;;
  esac
  host_asset="tl-${target_os}-${target_arch}"

  # A fabricated release directory, served over file://.
  release="$work/release"
  mkdir -p "$release"
  printf '#!/bin/sh\necho "stub tl 0.0.0-selftest"\n' > "$release/$host_asset"
  chmod +x "$release/$host_asset"
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$host_asset" > SHA256SUMS \
      || shasum -a 256 "$host_asset" > SHA256SUMS; } )
  printf '{}\n' > "$release/SHA256SUMS.sigstore.json"
  printf '{}\n' > "$release/${host_asset}.sigstore.json"

  run() {
    # run <expected-status> <name> [VAR=value ...]
    want=$1; name=$2; shift 2
    got=0
    ( PATH="$bin:$PATH" TL_VERSION=v0.0.0-selftest \
        TL_INSTALL_BASE_URL="file://$release" \
        TL_INSTALL_DIR="$work/dest" \
        env "$@" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
    if [ "$got" -ne "$want" ]; then
      echo "  FAIL $name: expected exit $want, got $got" >&2
      sed 's/^/    /' "$work/err" >&2
      failures=$((failures + 1))
      return 0
    fi
    echo "  ok   $name (exit $got)"
  }

  echo "tl-install --selftest:"

  rm -rf "$work/dest"
  run 0 "a complete, consistent release installs" IGNORE=1
  note "$([ -x "$work/dest/tl" ] && echo 0 || echo 1)" "the binary lands executable at the install dir"

  # Re-installing over an existing binary must succeed (atomic replace).
  run 0 "re-installing over an existing binary succeeds" IGNORE=1

  rm -rf "$work/dest"
  run 1 "a rejected SHA256SUMS signature refuses" COSIGN_STUB_VERDICT=bad
  note "$([ ! -e "$work/dest/tl" ] && echo 0 || echo 1)" "nothing is installed when a signature is rejected"

  # A digest mismatch, with signatures passing.
  cp "$release/SHA256SUMS" "$work/sums.bak"
  printf 'tampered\n' >> "$release/$host_asset"
  rm -rf "$work/dest"
  run 1 "a digest mismatch refuses" IGNORE=1
  note "$(grep -q 'digest mismatch' "$work/err" && echo 0 || echo 1)" "the digest-mismatch message names the cause"
  note "$([ ! -e "$work/dest/tl" ] && echo 0 || echo 1)" "nothing is installed on a digest mismatch"
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$host_asset" > SHA256SUMS \
      || shasum -a 256 "$host_asset" > SHA256SUMS; } )

  # A sums file with no entry for this asset.
  cp "$release/SHA256SUMS" "$work/sums.good"
  printf 'deadbeef  tl-some-other-target\n' > "$release/SHA256SUMS"
  rm -rf "$work/dest"
  run 1 "an asset absent from SHA256SUMS refuses" IGNORE=1
  printf 'not-a-digest  %s\n' "$host_asset" > "$release/SHA256SUMS"
  run 1 "a non-hex digest line refuses" IGNORE=1
  cp "$work/sums.good" "$release/SHA256SUMS"

  # Missing files.
  mv "$release/SHA256SUMS.sigstore.json" "$work/held"
  rm -rf "$work/dest"
  run 1 "a missing SHA256SUMS bundle refuses" IGNORE=1
  mv "$work/held" "$release/SHA256SUMS.sigstore.json"
  mv "$release/${host_asset}.sigstore.json" "$work/held"
  rm -rf "$work/dest"
  run 1 "a missing per-asset bundle refuses" IGNORE=1
  mv "$work/held" "$release/${host_asset}.sigstore.json"

  # The escape hatch: signatures skipped, digest still enforced.
  rm -rf "$work/dest" "$release/SHA256SUMS.sigstore.json" "$release/${host_asset}.sigstore.json"
  run 0 "TL_INSTALL_SKIP_SIGNATURE=1 installs without bundles" TL_INSTALL_SKIP_SIGNATURE=1
  printf 'tampered\n' >> "$release/$host_asset"
  rm -rf "$work/dest"
  run 1 "TL_INSTALL_SKIP_SIGNATURE=1 still refuses a digest mismatch" TL_INSTALL_SKIP_SIGNATURE=1
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$host_asset" > SHA256SUMS \
      || shasum -a 256 "$host_asset" > SHA256SUMS; } )
  printf '{}\n' > "$release/SHA256SUMS.sigstore.json"
  printf '{}\n' > "$release/${host_asset}.sigstore.json"

  # No cosign and no explicit opt-out: refuse rather than silently degrade.
  #
  # The PATH is built by dropping every directory that holds a cosign, rather
  # than by naming two that usually do not. `PATH=/usr/bin:/bin` is only
  # cosign-free where cosign is not packaged there, and on Fedora, Arch and
  # Alpine it is — so this row drove the *real* cosign against a fixture bundle
  # containing `{}`, failing on those hosts and nowhere else.
  bare_path=''
  rest=$PATH
  while [ -n "$rest" ]; do
    case $rest in
      *:*) dir=${rest%%:*}; rest=${rest#*:} ;;
      *) dir=$rest; rest='' ;;
    esac
    [ -n "$dir" ] || continue
    [ -x "$dir/cosign" ] && continue
    if [ -z "$bare_path" ]; then bare_path=$dir; else bare_path="$bare_path:$dir"; fi
  done
  # The premise this row rests on, checked rather than assumed: without it the
  # row passes on a host where cosign happens to be absent and says nothing on
  # one where it is not.
  note "$(PATH="$bare_path" command -v cosign >/dev/null 2>&1 && echo 1 || echo 0)" \
    "the missing-cosign row below really runs without cosign on PATH"
  got=0
  ( PATH="$bare_path" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
      TL_INSTALL_DIR="$work/dest" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'cosign not found' "$work/err" && echo 0 || echo 1)" \
    "a missing cosign refuses rather than skipping the check"

  # An unwritable install directory.
  ro="$work/readonly"
  mkdir -p "$ro"
  chmod a-w "$ro"
  got=0
  ( PATH="$bin:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
      TL_INSTALL_DIR="$ro/sub" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && echo 0 || echo 1)" "an unwritable install directory refuses (exit $got)"
  note "$(grep -q 'TL_INSTALL_DIR' "$work/err" && echo 0 || echo 1)" \
    "the unwritable-directory message names the variable to set"
  chmod u+w "$ro"

  # A custom asset location with no version to resolve.
  got=0
  ( PATH="$bin:$PATH" TL_INSTALL_BASE_URL="file://$release" TL_INSTALL_DIR="$work/dest" \
      sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'TL_VERSION' "$work/err" && echo 0 || echo 1)" \
    "a base URL without TL_VERSION refuses and says so"

  # Unsupported platforms, driven through the real uname branches.
  stub_uname() {
    d="$work/stub-$1-$2"
    mkdir -p "$d"
    cp "$bin/cosign" "$d/cosign"
    cat > "$d/uname" <<UNAME
#!/bin/sh
case "\$1" in
  -s) echo "$1" ;;
  -m) echo "$2" ;;
  *) echo "$1" ;;
esac
UNAME
    chmod +x "$d/uname"
    echo "$d"
  }
  for case_spec in "MINGW64_NT-10.0 x86_64 WSL2" "FreeBSD amd64 unsupported_operating_system" "Linux riscv64 unsupported_CPU_architecture"; do
    set -- $case_spec
    d=$(stub_uname "$1" "$2")
    expect=$(echo "$3" | tr '_' ' ')
    got=0
    ( PATH="$d:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
        TL_INSTALL_DIR="$work/dest" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
    note "$([ "$got" -eq 1 ] && grep -q "$expect" "$work/err" && echo 0 || echo 1)" \
      "$1/$2 refuses and explains ($expect)"
  done

  # Every supported platform-selection body, including the aliases the two
  # operating systems report in practice. These are injected observations over
  # the public installer, not calls to its helper functions, so a branch that
  # selected the wrong asset would try to fetch a file that is not present.
  for case_spec in "Darwin arm64 darwin-arm64" "Darwin x86_64 darwin-x64" \
                   "Linux aarch64 linux-arm64" "Linux amd64 linux-x64"; do
    set -- $case_spec
    selected_asset="tl-$3"
    printf '#!/bin/sh\necho "selected %s"\n' "$3" > "$release/$selected_asset"
    chmod +x "$release/$selected_asset"
    ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
        && sha256sum "$selected_asset" > SHA256SUMS \
        || shasum -a 256 "$selected_asset" > SHA256SUMS; } )
    printf '{}\n' > "$release/${selected_asset}.sigstore.json"
    d=$(stub_uname "$1" "$2")
    rm -rf "$work/dest"
    got=0
    ( PATH="$d:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
        TL_INSTALL_DIR="$work/dest" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
    installed=$("$work/dest/tl" 2>/dev/null || true)
    note "$([ "$got" -eq 0 ] && [ "$installed" = "selected $3" ] && echo 0 || echo 1)" \
      "$1/$2 selects tl-$3 through the public installer"
  done

  # The supported native arm64 build is the remedy for an Intel shell under
  # Rosetta. `sysctl` is the observable boundary, so a declared stub drives the
  # warning without needing an actual Darwin host.
  selected_platform=darwin-x64
  selected_asset="tl-$selected_platform"
  printf '#!/bin/sh\necho "selected darwin-x64"\n' > "$release/$selected_asset"
  chmod +x "$release/$selected_asset"
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$selected_asset" > SHA256SUMS \
      || shasum -a 256 "$selected_asset" > SHA256SUMS; } )
  printf '{}\n' > "$release/${selected_asset}.sigstore.json"
  d=$(stub_uname Darwin x86_64)
  cat > "$d/sysctl" <<'SYSCTL'
#!/bin/sh
[ "${1-}" = -n ] && [ "${2-}" = sysctl.proc_translated ] || exit 64
printf '1\n'
SYSCTL
  chmod +x "$d/sysctl"
  rm -rf "$work/dest"
  got=0
  ( PATH="$d:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
      TL_INSTALL_DIR="$work/dest" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 0 ] && grep -q 'running under Rosetta' "$work/err" && echo 0 || echo 1)" \
    "an Intel shell translated on Apple silicon installs and recommends the native arm64 build"

  # Restore the host fixture the remaining verifier rows use.
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$host_asset" > SHA256SUMS \
      || shasum -a 256 "$host_asset" > SHA256SUMS; } )

  # Tool availability, not the observed OS, selects the independent installer
  # digest fallback. Exercise it without sha256sum on PATH even on Linux, and
  # record both the binary and notice reaching the declared shasum collaborator.
  fallback_bin="$work/installer-shasum-bin"
  fallback_release="$work/installer-shasum-release"
  mkdir -p "$fallback_bin" "$fallback_release"
  for tool in awk chmod cp curl dirname mkdir mktemp mv rm sh tr uname; do
    tool_path=$(command -v "$tool") || {
      echo "tl-install: --selftest needs $tool to build the isolated shasum fixture" >&2
      exit 2
    }
    ln -s "$tool_path" "$fallback_bin/$tool"
  done
  cat > "$fallback_bin/shasum" <<SHASUM
#!/bin/sh
[ "\${1-}" = -a ] && [ "\${2-}" = 256 ] || exit 64
shift 2
printf '%s\n' "\${1##*/}" >> '$work/installer-shasum-reached'
SHASUM
  if digest_backend=$(command -v sha256sum); then
    printf '%s\n' "exec '$digest_backend' \"\$@\"" >> "$fallback_bin/shasum"
  elif digest_backend=$(command -v shasum); then
    printf '%s\n' "exec '$digest_backend' -a 256 \"\$@\"" >> "$fallback_bin/shasum"
  else
    echo "tl-install: --selftest needs a real digest tool behind its shasum fixture" >&2
    exit 2
  fi
  chmod +x "$fallback_bin/shasum"
  cp "$release/$host_asset" "$fallback_release/$host_asset"
  printf 'fallback notice\n' > "$fallback_release/THIRD-PARTY-LICENSES"
  ( cd "$fallback_release" && "$fallback_bin/shasum" -a 256 "$host_asset" THIRD-PARTY-LICENSES > SHA256SUMS )
  rm -f "$work/installer-shasum-reached"
  note "$(PATH="$fallback_bin" command -v sha256sum >/dev/null 2>&1 && echo 1 || echo 0)" \
    "the installer fallback runs with sha256sum absent from PATH"
  got=0
  ( PATH="$fallback_bin" TL_VERSION=v0.0.0-selftest TL_INSTALL_SKIP_SIGNATURE=1 \
      TL_INSTALL_BASE_URL="file://$fallback_release" TL_INSTALL_DIR="$work/fallback-dest" \
      TL_INSTALL_SHARE_DIR="$work/fallback-share" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 0 ] && [ -x "$work/fallback-dest/tl" ] \
      && [ "$(cat "$work/fallback-share/THIRD-PARTY-LICENSES" 2>/dev/null)" = 'fallback notice' ] && echo 0 || echo 1)" \
    "the shasum fallback installs the verified binary and notice"
  note "$(grep -qx "$host_asset" "$work/installer-shasum-reached" \
      && grep -qx THIRD-PARTY-LICENSES "$work/installer-shasum-reached" && echo 0 || echo 1)" \
    "both installer digest paths reached the shasum fixture"
  printf 'tampered\n' >> "$fallback_release/$host_asset"
  rm -rf "$work/fallback-dest"
  got=0
  ( PATH="$fallback_bin" TL_VERSION=v0.0.0-selftest TL_INSTALL_SKIP_SIGNATURE=1 \
      TL_INSTALL_BASE_URL="file://$fallback_release" TL_INSTALL_DIR="$work/fallback-dest" \
      TL_INSTALL_SHARE_DIR="$work/fallback-share" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && [ ! -e "$work/fallback-dest/tl" ] \
      && grep -q "digest mismatch for $host_asset" "$work/err" && echo 0 || echo 1)" \
    "the shasum fallback refuses a tampered binary before installation"

  # The per-asset signature check needs a case that reaches it: a stub failing
  # every call dies on SHA256SUMS first, so nothing would notice the second
  # call being deleted.
  rm -rf "$work/dest"
  got=0
  ( PATH="$bin:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
      TL_INSTALL_DIR="$work/dest" COSIGN_STUB_FAIL_ON="$host_asset" sh "$self" \
      >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q "signature on ${host_asset}" "$work/err" && echo 0 || echo 1)" \
    "a rejected per-asset signature refuses, naming the asset"
  note "$([ ! -e "$work/dest/tl" ] && echo 0 || echo 1)" \
    "nothing is installed when the per-asset signature is rejected"
  note "$(grep -q "$host_asset" "$work/cosign-blobs" && grep -q SHA256SUMS "$work/cosign-blobs" && echo 0 || echo 1)" \
    "both the sums file and the asset were handed to cosign"

  # A verifier that cannot run is a different thing from a rejected signature.
  rm -rf "$work/dest"
  got=0
  ( PATH="$bin:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
      TL_INSTALL_DIR="$work/dest" COSIGN_STUB_VERDICT=broken sh "$self" \
      >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'not evidence of tampering' "$work/err" && echo 0 || echo 1)" \
    "a verifier that cannot run is not reported as tampering"

  # Cleartext must be refused, not silently retried without the restriction.
  rm -rf "$work/dest"
  got=0
  ( PATH="$bin:$PATH" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="http://127.0.0.1:1/x" \
      TL_INSTALL_DIR="$work/dest" sh "$self" >"$work/out" 2>"$work/err" ) || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'could not download' "$work/err" && echo 0 || echo 1)" \
    "an http base URL is refused rather than fetched in cleartext"

  # The third-party notice ADR-0006 requires alongside every distributed
  # binary. Both arms: published and installed, and absent from an older
  # release, where a missing notice must not stop a good binary installing.
  printf 'notice for the selftest\n' > "$release/THIRD-PARTY-LICENSES"
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$host_asset" THIRD-PARTY-LICENSES > SHA256SUMS \
      || shasum -a 256 "$host_asset" THIRD-PARTY-LICENSES > SHA256SUMS; } )
  rm -rf "$work/dest" "$work/share"
  run 0 "a release publishing the notice installs it" TL_INSTALL_SHARE_DIR="$work/share"
  note "$([ -f "$work/share/THIRD-PARTY-LICENSES" ] && echo 0 || echo 1)" \
    "the notice lands beside the binary"
  # A notice whose digest does not match is refused *as a notice*: it is not
  # installed and the mismatch is reported, but the install still succeeds,
  # because the binary was already verified against the same signed sums file
  # and is on disk. Failing here would exit 1 on a good install and skip the
  # success line, the PATH advice and the version check.
  printf 'tampered\n' >> "$release/THIRD-PARTY-LICENSES"
  rm -rf "$work/dest" "$work/share"
  run 0 "a notice whose digest does not match does not fail the install" TL_INSTALL_SHARE_DIR="$work/share"
  note "$(grep -q 'digest mismatch for THIRD-PARTY-LICENSES' "$work/err" && echo 0 || echo 1)" \
    "the mismatch is reported, and names the notice rather than the binary"
  note "$([ ! -f "$work/share/THIRD-PARTY-LICENSES" ] && echo 0 || echo 1)" \
    "the mismatched notice is not installed"
  note "$([ -x "$work/dest/tl" ] && echo 0 || echo 1)" \
    "the binary is installed regardless"
  note "$(grep -q 'tl-install: installed' "$work/out" && echo 0 || echo 1)" \
    "the success line and PATH advice still run"

  # A truncated sums entry for the notice is a corrupt download, not tampering,
  # and must not be reported as the latter — the same distinction the binary
  # path makes twenty lines above, which the notice path originally omitted.
  cp "$work/sums.lower" "$release/SHA256SUMS" 2>/dev/null || true
  awk '$2 == "THIRD-PARTY-LICENSES" { print "abcdef  " $2; next } { print }' \
    "$release/SHA256SUMS" > "$release/SHA256SUMS.trunc" && mv "$release/SHA256SUMS.trunc" "$release/SHA256SUMS"
  rm -rf "$work/dest" "$work/share"
  run 0 "a truncated notice digest does not fail the install" TL_INSTALL_SHARE_DIR="$work/share"
  note "$(grep -q 'not the 64' "$work/err" && echo 0 || echo 1)" \
    "the truncated notice entry is reported as corrupt, not as a mismatch"
  note "$(! grep -q 'digest mismatch for THIRD-PARTY-LICENSES' "$work/err" && echo 0 || echo 1)"  \
    "a truncated notice entry is not reported as tampering"
  rm -f "$release/THIRD-PARTY-LICENSES"
  ( cd "$release" && { command -v sha256sum >/dev/null 2>&1 \
      && sha256sum "$host_asset" > SHA256SUMS \
      || shasum -a 256 "$host_asset" > SHA256SUMS; } )
  rm -rf "$work/dest" "$work/share"
  run 0 "a release without the notice still installs the binary" TL_INSTALL_SHARE_DIR="$work/share"
  note "$(grep -q 'publishes no THIRD-PARTY-LICENSES' "$work/out" && echo 0 || echo 1)" \
    "the absent notice is reported rather than passed over"
  cp "$release/SHA256SUMS" "$work/sums.lower"

  # An uppercase sums file is valid — the hex check deliberately accepts A-F —
  # and must install rather than read as tampering. This is the case the
  # case-sensitive comparison used to fail, with the loudest possible message.
  rm -rf "$work/dest"
  cp "$release/SHA256SUMS" "$work/sums.lower"
  awk '{ print toupper($1) "  " $2 }' "$work/sums.lower" > "$release/SHA256SUMS"
  run 0 "an uppercase SHA256SUMS installs rather than reading as tampering" IGNORE=1
  cp "$work/sums.lower" "$release/SHA256SUMS"

  # A truncated digest is a broken download, not a tampered binary; the two
  # messages send the reader to different places.
  rm -rf "$work/dest"
  printf 'abcdef  %s\n' "$host_asset" > "$release/SHA256SUMS"
  run 1 "a digest of the wrong length refuses" IGNORE=1
  note "$(grep -q 'not the 64' "$work/err" && echo 0 || echo 1)" \
    "the short-digest message says the file is truncated, not that it was tampered with"
  note "$(! grep -q 'digest mismatch' "$work/err" && echo 0 || echo 1)" \
    "a short digest is not reported as a mismatch"
  cp "$work/sums.lower" "$release/SHA256SUMS"

  # Nothing is left behind in the user's bin directory after a good install.
  rm -rf "$work/dest"
  run 0 "a second complete install still succeeds" IGNORE=1
  leftover=$(find "$work/dest" -name '.tl.install.*' 2>/dev/null | wc -l | tr -d ' ')
  note "$([ "$leftover" -eq 0 ] && echo 0 || echo 1)" \
    "no .tl.install.<pid> temporary survives a successful install (found $leftover)"

  # …nor after one that fails *after* staging. A non-empty directory where the
  # binary belongs makes the atomic rename fail, which is the one path that
  # reaches `die` with the temporary already written. Before the trap covered
  # it, every such attempt left another `.tl.install.<pid>` in the user's bin
  # directory. This is the failure arm the successful-install row cannot reach.
  rm -rf "$work/dest"
  mkdir -p "$work/dest/tl/occupied"
  : > "$work/dest/tl/occupied/keep"
  run 1 "a non-file where the binary belongs refuses" IGNORE=1
  note "$(grep -q 'not a regular file' "$work/err" && echo 0 || echo 1)" \
    "the occupied-destination message names the remedy"
  buried=$(find "$work/dest/tl" -maxdepth 1 -name '.tl.install.*' 2>/dev/null | wc -l | tr -d ' ')
  note "$([ "$buried" -eq 0 ] && echo 0 || echo 1)" \
    "the binary is not buried inside the directory that occupies its name (found $buried)"
  leftover=$(find "$work/dest" -name '.tl.install.*' 2>/dev/null | wc -l | tr -d ' ')
  note "$([ "$leftover" -eq 0 ] && echo 0 || echo 1)" \
    "no .tl.install.<pid> temporary survives a failed install (found $leftover)"
  rm -rf "$work/dest"

  # `resolve_version` is the branch a bare `curl … | sh` takes, and its three
  # outcomes sat behind a network call. The parsing half is driven here from a
  # *copy* of this script with the dispatch stripped off, rather than through
  # an environment variable that makes the shipped file return early: such a
  # variable is readable by whatever environment the installer runs in, and
  # under dash an inherited one made both a real install and this selftest
  # exit 0 having done nothing. A test seam that can disable production from
  # the ambient environment is worse than the coverage it buys.
  probe="$work/probe.sh"
  sed '/^case "${1-}" in$/,$d' "$self" > "$probe"
  printf 'version_from_effective_url "$1"\n' >> "$probe"
  note "$(grep -c 'version_from_effective_url' "$probe" | grep -qv '^0$' && echo 0 || echo 1)" \
    "the probe carries the function under test (the dispatch strip still works)"

  drive() { sh "$probe" "$1"; }

  out=$(drive "https://github.com/${TL_REPO}/releases/tag/v1.2.3" 2>"$work/err") && got=0 || got=$?
  note "$([ "$got" -eq 0 ] && [ "$out" = v1.2.3 ] && echo 0 || echo 1)" \
    "version_from_effective_url reads the tag out of a release redirect (got '$out')"
  out=$(drive "https://github.com/${TL_REPO}/releases/tag/v0.1.0-rc.1" 2>"$work/err") && got=0 || got=$?
  note "$([ "$got" -eq 0 ] && [ "$out" = v0.1.0-rc.1 ] && echo 0 || echo 1)" \
    "a prerelease tag survives intact (got '$out')"

  got=0; drive "https://github.com/${TL_REPO}/releases" >"$work/out" 2>"$work/err" || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'no stable release yet' "$work/err" && echo 0 || echo 1)" \
    "a prerelease-only repository is reported as 'nothing stable yet', not as a broken redirect"

  got=0; drive "https://github.com/${TL_REPO}/something/else" >"$work/out" 2>"$work/err" || got=$?
  note "$([ "$got" -eq 1 ] && grep -q 'redirect changed shape' "$work/err" && echo 0 || echo 1)" \
    "an unrecognised redirect target refuses instead of installing a guessed tag"

  # The early-return hatch is gone and must stay gone: while it existed, any
  # environment carrying its name turned this whole selftest into a no-op that
  # the release-policy gate read as a pass. Checked behaviourally rather than
  # by grepping for a name — a textual check matches its own comment, and what
  # matters is that no inherited variable can stop the installer working.
  rm -rf "$work/dest" "$work/share"
  run 0 "a polluted environment does not stop the installer" \
    TL_INSTALL_SOURCE_ONLY=1 TL_INSTALL_SELFTEST=1 TL_SOURCE_ONLY=1
  note "$([ -x "$work/dest/tl" ] && echo 0 || echo 1)" \
    "the binary is installed even with an early-return-shaped variable set"

  if [ "$failures" -ne 0 ]; then
    echo "tl-install: --selftest found $failures broken case(s). Do not publish this installer — a user piping it into a shell has no way to notice a check that stopped running." >&2
    exit 1
  fi
  echo "tl-install: --selftest passed"
  exit 0
}

case "${1-}" in
  '') main ;;
  --selftest)
    [ "$#" -eq 1 ] || { echo "usage: $0 [--selftest]" >&2; exit 2; }
    selftest
    ;;
  *)
    echo "tl-install: unknown argument '$1' — this installer takes no options; configure it with the TL_* environment variables documented at the top of the script." >&2
    exit 2
    ;;
esac
