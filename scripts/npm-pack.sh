#!/bin/sh
# Stage the npm packages for publication, and test that they install and work.
#
#   scripts/npm-pack.sh <staging-dir> <assets-dir>
#       Copy npm/tl and the four npm/platform packages into <staging-dir>,
#       placing the release binary from <assets-dir>/tl-<target> into each
#       platform package. <staging-dir> is then ready for `npm publish`.
#
#   scripts/npm-pack.sh --selftest
#       Stage the same layout with stub binaries, then actually `npm pack` and
#       `npm install` it and drive the launcher.
#
# The staged tree is a copy: publishing must never depend on files being
# rearranged inside the working checkout, and the platform packages hold no
# binary in git.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)

# The Supported tier is release-blocking; macOS x86-64 is Best-effort, so a
# release may legitimately ship without it (ADR-0006). Staging follows that
# policy rather than demanding all four: a Best-effort binary that never got
# built must not stop the other four packages from being published.
REQUIRED_TARGETS='darwin-arm64 linux-arm64 linux-x64'
OPTIONAL_TARGETS='darwin-x64'
TARGETS="$REQUIRED_TARGETS $OPTIONAL_TARGETS"

usage() {
  echo "usage: $0 <staging-dir> <assets-dir> | $0 --check-staged <staging-dir> <commit> | $0 --selftest" >&2
  exit 2
}

# ADR-0006: the license notice travels in every distribution artifact. npm
# includes a LICENSE file automatically only when one sits in the package
# directory, and neither file is checked into npm/ — they belong to the
# repository root, and a second copy in git would be a second thing to drift.
copy_license_files() {
  cp "$repo_root/LICENSE" "$1/LICENSE"
  cp "$repo_root/THIRD-PARTY-LICENSES" "$1/THIRD-PARTY-LICENSES"
}

# Copy the package sources into <staging>, with each platform package's binary
# taken from <assets>/tl-<target>. <require_assets>=0 fabricates a stub binary
# for every target, which is what the selftest wants and what a release must
# never do. Writes the staged platform target names to <staging>/.staged.
stage() {
  staging=$1
  assets=$2
  require_assets=$3

  mkdir -p "$staging"
  cp -R "$repo_root/npm/tl" "$staging/tl"
  chmod +x "$staging/tl/bin/tl"
  copy_license_files "$staging/tl"
  : > "$staging/.staged"

  for target in $TARGETS; do
    dest="$staging/tl-bin-$target"
    if [ "$require_assets" -eq 1 ] && [ ! -f "$assets/tl-$target" ]; then
      case " $REQUIRED_TARGETS " in
        *" $target "*)
          echo "npm-pack: $assets/tl-$target not found, and $target is a Supported target. Publishing without it would leave users there with a package that installs and then cannot run. Build the missing target, or move it out of REQUIRED_TARGETS deliberately and record that in ADR-0006." >&2
          exit 1
          ;;
        *)
          echo "npm-pack: no binary for $target — skipping @taskloop/tl-bin-$target. It is a Best-effort target (ADR-0006), so its absence does not block the release; users there get the launcher's missing-package message."
          continue
          ;;
      esac
    fi
    cp -R "$repo_root/npm/platform/$target" "$dest"
    mkdir -p "$dest/bin"
    if [ -f "$assets/tl-$target" ]; then
      cp "$assets/tl-$target" "$dest/bin/tl"
    else
      printf '#!/bin/sh\necho "stub tl for %s: $*"\nexit 0\n' "$target" > "$dest/bin/tl"
    fi
    chmod +x "$dest/bin/tl"
    copy_license_files "$dest"
    echo "$target" >> "$staging/.staged"
  done

  # The staged launcher pins exactly the platform packages this release
  # publishes. A pin for a package that was skipped would have npm try to
  # resolve something the registry never received; dropping it means a user on
  # that platform gets the launcher's teaching message instead of an install
  # warning about a missing dependency.
  python3 - "$staging" <<'PYEOF'
import json, pathlib, sys

staging = pathlib.Path(sys.argv[1])
staged = [t for t in staging.joinpath(".staged").read_text().split() if t]
manifest_path = staging / "tl" / "package.json"
manifest = json.loads(manifest_path.read_text())
version = manifest["version"]
kept = {f"@taskloop/tl-bin-{t}": version for t in staged}
dropped = sorted(set(manifest.get("optionalDependencies", {})) - set(kept))
manifest["optionalDependencies"] = {k: kept[k] for k in sorted(kept)}
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
for name in dropped:
    print(f"npm-pack: dropped the optionalDependency on {name}; it is not in this release")
PYEOF
}

check_versions() {
  staging=$1
  python3 - "$staging" "$repo_root" <<'PYEOF'
import json, pathlib, re, sys

staging, repo_root = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])

launcher = json.loads((staging / "tl" / "package.json").read_text())
version = launcher["version"]

product = None
for line in (repo_root / "Tl" / "Cli" / "Commands.lean").read_text().splitlines():
    if line.startswith("def productVersion : String := "):
        product = line.split('"')[1]
        break
if product is None:
    sys.exit("npm-pack: could not read productVersion from Tl/Cli/Commands.lean")
if product != version:
    sys.exit(
        f"npm-pack: @taskloop/tl is version {version} but the binary reports {product} "
        f"(productVersion in Tl/Cli/Commands.lean). Bring npm/tl/package.json, the "
        f"npm/platform/*/package.json files, and the lakefile package version to {product}."
    )

# The SPDX id the repository actually publishes under, read from LICENSE rather
# than written here. The manifest `license` field is the machine-readable
# license of record for the registry, and an npm version cannot be republished
# once it is wrong.
license_head = (repo_root / "LICENSE").read_text()[:400]
if "Apache License" in license_head and "Version 2.0" in license_head:
    spdx = "Apache-2.0"
elif re.search(r"\bMIT License\b", license_head):
    spdx = "MIT"
else:
    sys.exit(
        "npm-pack: could not identify the repository LICENSE. Teach this check the new license "
        "before publishing, so the manifests cannot claim one the repository does not use."
    )

deps = launcher.get("optionalDependencies", {})
staged_paths = sorted(staging.glob("tl-bin-*/package.json"))
staged_names = {json.loads(p.read_text())["name"] for p in staged_paths}
problems = []


def check_common(manifest, name):
    if manifest["version"] != version:
        problems.append(f"{name} is version {manifest['version']}, not {version}")
    if manifest.get("license") != spdx:
        problems.append(
            f"{name} declares license {manifest.get('license')!r} but the repository LICENSE is "
            f"{spdx}; the registry would record the wrong license permanently"
        )
    for required in ("LICENSE", "THIRD-PARTY-LICENSES"):
        if required not in manifest.get("files", []):
            problems.append(
                f"{name} does not ship {required}; ADR-0006 requires the notice to travel in "
                "every distribution artifact"
            )


check_common(launcher, "@taskloop/tl")
if launcher.get("scripts"):
    problems.append(
        "@taskloop/tl declares scripts. A lifecycle script runs with the user's privileges at "
        "install time; the launcher must have none (ADR-0014 T3)."
    )

for path in staged_paths:
    manifest = json.loads(path.read_text())
    name = manifest["name"]
    target = path.parent.name[len("tl-bin-"):]
    expect_os, expect_cpu = target.split("-", 1)
    check_common(manifest, name)
    pin = deps.get(name)
    if pin is None:
        problems.append(f"{name} is not an optionalDependency of @taskloop/tl")
    elif pin != version:
        problems.append(
            f"@taskloop/tl pins {name} at {pin!r}, which is not the exact version {version}"
        )
    # os/cpu decide which package npm installs where. Constraints that disagree
    # with the binary the package carries would select it on a platform it
    # cannot run on.
    if manifest.get("os") != [expect_os]:
        problems.append(f"{name} declares os {manifest.get('os')!r}, not ['{expect_os}']")
    if manifest.get("cpu") != [expect_cpu]:
        problems.append(f"{name} declares cpu {manifest.get('cpu')!r}, not ['{expect_cpu}']")
    if expect_os == "linux" and manifest.get("libc") != ["glibc"]:
        problems.append(
            f"{name} does not declare libc ['glibc']; the Linux binaries are glibc-linked, and "
            "without the constraint npm installs them on musl where they cannot exec"
        )
    if manifest.get("publishConfig", {}).get("access") != "public":
        problems.append(f"{name} is not marked publishConfig.access=public")
    for forbidden in ("scripts", "dependencies"):
        if manifest.get(forbidden):
            problems.append(
                f"{name} declares {forbidden}; platform packages carry a binary and nothing else"
            )

# A pin left behind after a platform package is dropped would make npm try to
# resolve a package this release never publishes.
for name in sorted(set(deps) - staged_names):
    problems.append(
        f"@taskloop/tl pins {name}, which is not among the staged platform packages "
        f"({', '.join(sorted(staged_names)) or 'none'})"
    )

if problems:
    sys.exit("npm-pack: manifest problems:\n  " + "\n  ".join(problems))
print(f"npm-pack: {1 + len(staged_paths)} manifests agree at version {version}, license {spdx}")
PYEOF
}

# Validate a staging tree that is about to be published: the real binaries are
# in place, they are the ones this release built, and they run. Distinct from
# --selftest, which exercises the package *sources* with stub binaries.
check_staged() {
  staging=$1
  expect_commit=$2
  [ -d "$staging" ] || {
    echo "npm-pack: '$staging' is not a directory — stage the packages first with '$0 <staging-dir> <assets-dir>'." >&2
    exit 1
  }
  check_versions "$staging"

  case $(uname -s) in
    Darwin) host_os=darwin ;;
    Linux) host_os=linux ;;
    *)
      echo "npm-pack: --check-staged runs the host platform's staged binary and does not know this OS ($(uname -s))." >&2
      exit 2
      ;;
  esac
  case $(uname -m) in
    arm64 | aarch64) host_arch=arm64 ;;
    x86_64 | amd64) host_arch=x64 ;;
    *)
      echo "npm-pack: --check-staged runs the host platform's staged binary and does not know this architecture ($(uname -m))." >&2
      exit 2
      ;;
  esac
  host="$staging/tl-bin-${host_os}-${host_arch}/bin/tl"
  [ -x "$host" ] || {
    echo "npm-pack: $host is missing or not executable, so the staged package for this platform would install and then fail to run." >&2
    exit 1
  }

  # Comparing the provenance the binary reports against the commit the release
  # names is what turns "a binary is present" into "the right binary is here".
  got=$("$host" version --json) || {
    echo "npm-pack: the staged binary for ${host_os}-${host_arch} did not run. Do not publish it." >&2
    exit 1
  }
  echo "$got"
  python3 - "$got" "$expect_commit" <<'PYEOF'
import json, sys

data = json.loads(sys.argv[1])["data"]
want = sys.argv[2]
build = data.get("build", {})
if build.get("commit") != want:
    sys.exit(
        f"npm-pack: the staged binary reports commit {build.get('commit')!r}, but this release is "
        f"built from {want!r}. The npm packages would ship a binary other than the one the release "
        "signed."
    )
if build.get("kind") != "clean":
    sys.exit(
        f"npm-pack: the staged binary reports a {build.get('kind')!r} build, not 'clean'. Only a "
        "binary corresponding exactly to the tagged commit may be published."
    )
print(f"npm-pack: the staged binary is tl {data['version']} from {build['commit']}")
PYEOF
  echo "npm-pack: the staging tree in $staging is ready to publish"
}

selftest() {
  command -v npm >/dev/null 2>&1 || {
    echo "npm-pack: --selftest needs npm on PATH" >&2
    exit 2
  }
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  failures=0
  note() {
    if [ "$1" -eq 0 ]; then
      echo "  ok   $2"
    else
      echo "  FAIL $2" >&2
      failures=$((failures + 1))
    fi
  }

  echo "npm-pack --selftest:"

  staging="$work/staging"
  stage "$staging" "$work/no-assets" 0
  check_versions "$staging"
  note $? "the five manifests agree on one version and pin exactly"

  # Host platform, for the "this platform resolves" cases below.
  case $(uname -s) in
    Darwin) host_os=darwin ;;
    Linux) host_os=linux ;;
    *) host_os=unknown ;;
  esac
  case $(uname -m) in
    arm64 | aarch64) host_arch=arm64 ;;
    x86_64 | amd64) host_arch=x64 ;;
    *) host_arch=unknown ;;
  esac
  host_target="$host_os-$host_arch"

  # Pack every package, then install the launcher from its tarball with the
  # platform tarballs available locally. `npm install <tarball>` resolves the
  # optionalDependencies from the registry, which we do not want to touch, so
  # the platform packages are installed explicitly alongside instead.
  packed="$work/packed"
  mkdir -p "$packed"
  ( cd "$staging/tl" && npm pack --pack-destination "$packed" >/dev/null 2>&1 )
  note $? "@taskloop/tl packs"
  for target in $TARGETS; do
    ( cd "$staging/tl-bin-$target" && npm pack --pack-destination "$packed" >/dev/null 2>&1 )
    note $? "@taskloop/tl-bin-$target packs"
  done

  # Exact tarball names, not globs: `taskloop-tl-*.tgz` also matches the four
  # `taskloop-tl-bin-*` tarballs, and the extra arguments would be read as
  # member names to extract rather than as further archives.
  version=$(sed -n 's/.*"version"[[:space:]]*:[[:space:]]*"\(.*\)".*/\1/p' "$staging/tl/package.json" | head -1)
  launcher_tgz="$packed/taskloop-tl-$version.tgz"
  host_tgz="$packed/taskloop-tl-bin-$host_target-$version.tgz"

  # The published tarball must contain the launcher and nothing surprising.
  contents=$(tar -tzf "$launcher_tgz")
  case $contents in
    *package/bin/tl*) note 0 "the launcher tarball contains bin/tl" ;;
    *) note 1 "the launcher tarball contains bin/tl" ;;
  esac
  case $contents in
    *node_modules*) note 1 "the launcher tarball ships no node_modules" ;;
    *) note 0 "the launcher tarball ships no node_modules" ;;
  esac

  # Local-style install: node_modules/.bin/tl, the layout a project gets.
  local_dir="$work/local"
  mkdir -p "$local_dir"
  ( cd "$local_dir" && npm init -y >/dev/null 2>&1 \
      && npm install --no-audit --no-fund --silent \
           "$launcher_tgz" "$host_tgz" >/dev/null 2>&1 )
  note $? "a local-style install succeeds"
  out=$("$local_dir/node_modules/.bin/tl" hello 2>&1) || out="<failed> $out"
  case $out in
    *"stub tl for $host_target"*) note 0 "the local .bin/tl symlink execs the host platform's binary" ;;
    *) note 1 "the local .bin/tl symlink execs the host platform's binary (got: $out)" ;;
  esac

  # Global-style install: a prefix with bin/tl, the layout `npm i -g` gets.
  global_dir="$work/global"
  mkdir -p "$global_dir"
  ( npm install --no-audit --no-fund --silent --prefix "$global_dir" --global \
      "$launcher_tgz" "$host_tgz" >/dev/null 2>&1 )
  note $? "a global-style install succeeds"
  out=$("$global_dir/bin/tl" hello 2>&1) || out="<failed> $out"
  case $out in
    *"stub tl for $host_target"*) note 0 "the global bin/tl symlink execs the host platform's binary" ;;
    *) note 1 "the global bin/tl symlink execs the host platform's binary (got: $out)" ;;
  esac

  # Exit status and arguments pass through untouched.
  probe="$work/probe"
  mkdir -p "$probe"
  cp -R "$staging/tl" "$probe/tl"
  mkdir -p "$probe/tl-bin-$host_target/bin"
  printf '#!/bin/sh\nprintf "%%s\\n" "$@"\nexit 42\n' > "$probe/tl-bin-$host_target/bin/tl"
  chmod +x "$probe/tl-bin-$host_target/bin/tl"
  out=$("$probe/tl/bin/tl" one "two three" 2>&1) && status=0 || status=$?
  note "$([ "$status" -eq 42 ] && echo 0 || echo 1)" "the launcher propagates the binary's exit status ($status)"
  case $out in
    "one
two three") note 0 "arguments reach the binary unsplit" ;;
    *) note 1 "arguments reach the binary unsplit (got: $out)" ;;
  esac

  # `exec` must replace the launcher rather than fork it, so that there is no
  # wrapper process between the shell and tl. Two consequences, both checked.
  #
  # First: the binary runs under the very pid the caller sees. A forking
  # launcher would report a child pid here.
  pidfile="$work/child.pid"
  printf '#!/bin/sh\necho $$ > "%s"\n' "$pidfile" > "$probe/tl-bin-$host_target/bin/tl"
  chmod +x "$probe/tl-bin-$host_target/bin/tl"
  "$probe/tl/bin/tl" &
  launcher_pid=$!
  wait "$launcher_pid" 2>/dev/null || true
  child_pid=$(cat "$pidfile" 2>/dev/null || echo none)
  note "$([ "$child_pid" = "$launcher_pid" ] && echo 0 || echo 1)" \
    "exec replaces the launcher: the binary runs as pid $launcher_pid (saw $child_pid)"

  # Second: a signal sent to that pid is handled by the binary itself. The
  # stub reports its pid before blocking, so the kill is sent only once exec
  # has happened — otherwise this races the exec and measures nothing.
  # `sleep &` plus `wait` rather than a foreground `sleep`, because a POSIX
  # shell defers trap handling until the foreground command returns.
  rm -f "$pidfile"
  printf '#!/bin/sh\ntrap "exit 7" TERM\necho $$ > "%s"\nsleep 30 &\nwait $!\n' "$pidfile" \
    > "$probe/tl-bin-$host_target/bin/tl"
  chmod +x "$probe/tl-bin-$host_target/bin/tl"
  "$probe/tl/bin/tl" &
  launcher_pid=$!
  waited=0
  while [ ! -s "$pidfile" ] && [ "$waited" -lt 100 ]; do
    sleep 0.05
    waited=$((waited + 1))
  done
  kill -TERM "$launcher_pid" 2>/dev/null || true
  wait "$launcher_pid" 2>/dev/null && status=0 || status=$?
  # 7 is the stub's own handler. 143 (128+SIGTERM) would mean the signal killed
  # a process that had no handler — a wrapper still sitting in the way.
  note "$([ "$status" -eq 7 ] && echo 0 || echo 1)" \
    "SIGTERM is handled by the binary, not by a wrapper (status $status)"

  # The missing-platform-package path: a real install with --omit=optional.
  missing="$work/missing"
  mkdir -p "$missing/tl"
  cp -R "$staging/tl/." "$missing/tl/"
  out=$("$missing/tl/bin/tl" 2>&1) && status=0 || status=$?
  note "$([ "$status" -eq 1 ] && echo 0 || echo 1)" "a missing platform package exits 1"
  case $out in
    *"not installed"*"optional"*) note 0 "the missing-package error names the cause and the fix" ;;
    *) note 1 "the missing-package error names the cause and the fix (got: $out)" ;;
  esac

  # Unsupported platforms are refused with an explanation, not a confusing
  # "not installed". uname is stubbed rather than the launcher parameterised:
  # the code under test is the real script, unmodified.
  stub_uname() {
    stub_dir="$work/stub-$1-$2"
    mkdir -p "$stub_dir"
    cat > "$stub_dir/uname" <<UNAME
#!/bin/sh
case "\$1" in
  -s) echo "$1" ;;
  -m) echo "$2" ;;
  *) echo "$1" ;;
esac
UNAME
    chmod +x "$stub_dir/uname"
    echo "$stub_dir"
  }
  d=$(stub_uname MINGW64_NT-10.0 x86_64)
  out=$(PATH="$d:$PATH" "$probe/tl/bin/tl" 2>&1) && status=0 || status=$?
  note "$([ "$status" -eq 1 ] && echo 0 || echo 1)" "native Windows exits 1"
  case $out in
    *WSL2*) note 0 "the native-Windows error points at WSL2" ;;
    *) note 1 "the native-Windows error points at WSL2 (got: $out)" ;;
  esac
  d=$(stub_uname FreeBSD amd64)
  out=$(PATH="$d:$PATH" "$probe/tl/bin/tl" 2>&1) && status=0 || status=$?
  note "$([ "$status" -eq 1 ] && echo 0 || echo 1)" "an unsupported OS exits 1"
  case $out in
    *"unsupported operating system"*) note 0 "the unsupported-OS error names the OS" ;;
    *) note 1 "the unsupported-OS error names the OS (got: $out)" ;;
  esac
  d=$(stub_uname Linux riscv64)
  out=$(PATH="$d:$PATH" "$probe/tl/bin/tl" 2>&1) && status=0 || status=$?
  note "$([ "$status" -eq 1 ] && echo 0 || echo 1)" "an unsupported CPU exits 1"
  case $out in
    *"unsupported CPU architecture"*) note 0 "the unsupported-CPU error names the architecture" ;;
    *) note 1 "the unsupported-CPU error names the architecture (got: $out)" ;;
  esac

  # All four selections resolve to the right package, driven through the real
  # uname branches rather than by inspecting the script.
  for target in $TARGETS; do
    sel_os=${target%-*}
    sel_arch=${target##*-}
    sel="$work/sel-$target"
    mkdir -p "$sel/tl" "$sel/tl-bin-$target/bin"
    cp -R "$staging/tl/." "$sel/tl/"
    printf '#!/bin/sh\necho "selected %s"\n' "$target" > "$sel/tl-bin-$target/bin/tl"
    chmod +x "$sel/tl-bin-$target/bin/tl"
    case $sel_os in
      darwin) uname_s=Darwin ;;
      *) uname_s=Linux ;;
    esac
    case $sel_arch in
      arm64) uname_m=arm64 ;;
      *) uname_m=x86_64 ;;
    esac
    d=$(stub_uname "$uname_s" "$uname_m")
    out=$(PATH="$d:$PATH" "$sel/tl/bin/tl" 2>&1) || out="<failed> $out"
    case $out in
      "selected $target") note 0 "$target resolves to its own package" ;;
      *) note 1 "$target resolves to its own package (got: $out)" ;;
    esac
  done

  # The tarballs must carry the license files ADR-0006 requires in every
  # distribution artifact. npm picks up a LICENSE only when one sits in the
  # package directory, so this is a property of staging, not of the manifest.
  for tgz in "$launcher_tgz" "$host_tgz"; do
    listing=$(tar -tzf "$tgz")
    for required in package/LICENSE package/THIRD-PARTY-LICENSES; do
      case $listing in
        *"$required"*) note 0 "$(basename -- "$tgz") ships ${required#package/}" ;;
        *) note 1 "$(basename -- "$tgz") ships ${required#package/}" ;;
      esac
    done
  done

  # Staging follows the ADR-0006 tiers: a missing Best-effort binary is skipped
  # with a warning, a missing Supported one aborts. Both arms, because a policy
  # only one of which is exercised is a policy half-implemented.
  assets="$work/assets"
  mkdir -p "$assets"
  for t in darwin-arm64 linux-arm64 linux-x64; do
    printf '#!/bin/sh\necho real\n' > "$assets/tl-$t"
    chmod +x "$assets/tl-$t"
  done
  tiered="$work/tiered"
  if "$0" "$tiered" "$assets" >"$work/out" 2>"$work/err"; then
    note 0 "a missing Best-effort binary is skipped, not fatal"
  else
    note 1 "a missing Best-effort binary is skipped, not fatal"
    sed 's/^/    /' "$work/err" >&2
  fi
  note "$([ ! -d "$tiered/tl-bin-darwin-x64" ] && echo 0 || echo 1)" \
    "the skipped Best-effort package is absent from the staging tree"
  rm -f "$assets/tl-linux-x64"
  if "$0" "$work/tiered2" "$assets" >"$work/out" 2>"$work/err"; then
    note 1 "a missing Supported binary aborts staging"
  else
    note 0 "a missing Supported binary aborts staging"
  fi
  note "$(grep -q 'Supported target' "$work/err" && echo 0 || echo 1)" \
    "the missing-Supported-binary message names the tier"

  # Usage and argument handling.
  for args in "" "--bogus" "--selftest extra" "--check-staged onearg"; do
    got=0
    # shellcheck disable=SC2086
    ( "$0" $args >/dev/null 2>&1 ) || got=$?
    note "$([ "$got" -eq 2 ] && echo 0 || echo 1)" "'$args' is a usage error (exit $got)"
  done
  got=0
  ( "$0" --check-staged "$work/nonexistent" deadbeef >/dev/null 2>&1 ) || got=$?
  note "$([ "$got" -eq 1 ] && echo 0 || echo 1)" "--check-staged on a missing directory refuses (exit $got)"

  if [ "$failures" -ne 0 ]; then
    echo "npm-pack: --selftest found $failures broken case(s). Do not publish these packages." >&2
    exit 1
  fi
  echo "npm-pack: --selftest passed"
  exit 0
}

case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  --check-staged)
    [ "$#" -eq 3 ] || usage
    check_staged "$2" "$3"
    ;;
  -*) usage ;;
  *)
    [ "$#" -eq 2 ] || usage
    stage "$1" "$2" 1
    check_versions "$1"
    echo "npm-pack: staged @taskloop/tl and $(wc -l < "$1/.staged" | tr -d ' ') platform package(s) in $1"
    ;;
esac
