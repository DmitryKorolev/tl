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

detect_target() {
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
  case $(uname -m) in
    arm64 | aarch64) install_arch=arm64 ;;
    x86_64 | amd64) install_arch=x64 ;;
    *)
      die "unsupported CPU architecture '$(uname -m)'. tl publishes arm64 and x86-64 binaries; to use it elsewhere, build from source with Lean 4 (see https://github.com/${TL_REPO})."
      ;;
  esac
  asset="tl-${install_os}-${install_arch}"
}

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    die "no sha256sum or shasum found. The digest check is mandatory and there is no way to skip it; install coreutils (Linux) or use the system shasum (macOS)."
  fi
}

fetch() {
  # $1 url, $2 destination. Fails loudly: a partial or 404 download that is
  # later "verified" against a sums file from the same source proves nothing,
  # so nothing continues past a failed fetch.
  curl -fsSL --retry 3 --proto '=https,file' -o "$2" "$1" 2>/dev/null \
    || curl -fsSL --retry 3 -o "$2" "$1" 2>/dev/null \
    || die "could not download $1. Check the network and that the release exists; if you passed TL_VERSION, confirm that tag has published assets."
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
  latest_url=$(curl -fsSLI -o /dev/null -w '%{url_effective}' \
    "https://github.com/${TL_REPO}/releases/latest" 2>/dev/null) \
    || die "could not reach GitHub to find the latest release. Check the network, or set TL_VERSION to install a specific tag."
  version=${latest_url##*/}
  case $version in
    v*) ;;
    *) die "could not work out the latest version from '${latest_url}' — GitHub's redirect changed shape. Set TL_VERSION to a tag such as v0.1.0 and report this." ;;
  esac
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
  trap 'rm -rf "$work"' EXIT

  echo "tl-install: installing ${asset} from ${version}"
  fetch "${base}/${asset}" "$work/$asset"
  fetch "${base}/SHA256SUMS" "$work/SHA256SUMS"

  # The sums file first: everything after this trusts it.
  if [ "$skip_signature" -eq 0 ]; then
    fetch "${base}/SHA256SUMS.sigstore.json" "$work/SHA256SUMS.sigstore.json"
    cosign verify-blob "$work/SHA256SUMS" \
      --bundle "$work/SHA256SUMS.sigstore.json" \
      --certificate-oidc-issuer "$TL_ISSUER" \
      --certificate-identity-regexp "$TL_IDENTITY" >/dev/null \
      || die "the signature on SHA256SUMS did not verify against this repository's pinned release identity. Nothing has been installed. Do not work around this — re-run to rule out a corrupted download, and if it persists, report it at https://github.com/${TL_REPO}/issues."
    echo "tl-install: SHA256SUMS signature verified"
  fi

  expected=$(awk -v want="$asset" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' \
    "$work/SHA256SUMS") \
    || die "SHA256SUMS from ${version} has no entry for ${asset}. That release may not publish a binary for this platform; check https://github.com/${TL_REPO}/releases/tag/${version}."
  case $expected in
    *[!0-9a-fA-F]* | '') die "the SHA256SUMS entry for ${asset} is not a hex digest. The file is corrupt or truncated; re-run to download it again." ;;
  esac
  actual=$(sha256_of "$work/$asset")
  [ "$actual" = "$expected" ] \
    || die "digest mismatch for ${asset}: downloaded ${actual}, expected ${expected}. Nothing has been installed. Re-run to rule out a corrupted download; if it persists, do not run the binary — report it at https://github.com/${TL_REPO}/issues."
  echo "tl-install: ${asset} digest verified"

  if [ "$skip_signature" -eq 0 ]; then
    fetch "${base}/${asset}.sigstore.json" "$work/${asset}.sigstore.json"
    cosign verify-blob "$work/$asset" \
      --bundle "$work/${asset}.sigstore.json" \
      --certificate-oidc-issuer "$TL_ISSUER" \
      --certificate-identity-regexp "$TL_IDENTITY" >/dev/null \
      || die "the signature on ${asset} did not verify against this repository's pinned release identity. Nothing has been installed. Do not run this binary; report it at https://github.com/${TL_REPO}/issues."
    echo "tl-install: ${asset} signature verified"
  fi

  mkdir -p "$install_dir" 2>/dev/null \
    || die "could not create ${install_dir}. Choose a writable location with TL_INSTALL_DIR=/some/dir, or create that directory first."
  [ -w "$install_dir" ] \
    || die "${install_dir} is not writable. Set TL_INSTALL_DIR to a directory you own (for example TL_INSTALL_DIR=\"\$HOME/.local/bin\"), or re-run with elevated privileges if a system-wide install is what you want."

  chmod +x "$work/$asset"
  # Install through a rename within the destination directory, so a concurrent
  # `tl` either sees the old binary or the new one — never a half-written file.
  # The temporary lives in $install_dir rather than $work because a rename
  # across filesystems is not atomic and would fall back to a copy.
  staged="$install_dir/.tl.install.$$"
  cp "$work/$asset" "$staged" \
    || die "could not write to ${install_dir}. Choose a writable location with TL_INSTALL_DIR."
  chmod +x "$staged"
  mv -f "$staged" "$install_dir/tl" \
    || { rm -f "$staged"; die "could not replace ${install_dir}/tl. Close any running tl and re-run, or choose another TL_INSTALL_DIR."; }

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

  # A stub cosign whose verdict comes from COSIGN_STUB_VERDICT, and stub
  # uname/sha256 tools, all ahead of the real ones on PATH.
  bin="$work/bin"
  mkdir -p "$bin"
  cat > "$bin/cosign" <<'STUB'
#!/bin/sh
[ "${COSIGN_STUB_VERDICT:-ok}" = "ok" ] && exit 0
echo "stub cosign: refusing" >&2
exit 1
STUB
  chmod +x "$bin/cosign"

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
  got=0
  ( PATH="/usr/bin:/bin" TL_VERSION=v0.0.0-selftest TL_INSTALL_BASE_URL="file://$release" \
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
