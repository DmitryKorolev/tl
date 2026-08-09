#!/bin/sh
# Guard the copies of scripts/lib/release-common.sh that cannot be sourced.
#
#   scripts/check-embedded-copies.sh              check the committed copies
#   scripts/check-embedded-copies.sh --selftest   prove the checker can fail
#
# `install.sh` is piped straight into a shell — `curl … | sh` — so it has no
# checkout to read a library out of and must carry its own `sha256_of`, its own
# lowercasing, and its own uname mapping. That duplication is forced, not
# chosen. What is chosen is whether anyone notices when the copies drift, and
# before this gate nobody did: the three copies of the digest helper had already
# diverged into one that reported a length problem and two that reported it as
# tampering.
#
# Two comparison modes, because two kinds of copy are involved:
#
#   text  — the body must match the library's, modulo the `rc_` naming prefix.
#           Used where the code can be identical (`sha256_of`, `lower`).
#   cases — the `case` arms must classify identically: the same patterns
#           mapping to the same values. Used for the uname mapping, where the
#           installer legitimately words its refusals differently (it names
#           TL_INSTALL_DIR and the repository URL) but must not disagree about
#           which system is which.
#
# The npm launcher (`npm/tl/bin/tl`) carries the same mapping for the same
# reason — it ships inside a published package — so it is guarded here too.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)

command -v python3 >/dev/null 2>&1 || {
  echo "check-embedded-copies: python3 not found — it parses the shell blocks this gate compares. Install python3, or run this gate in CI only and say so in ADR-0026." >&2
  exit 2
}

case "${1-}" in
  '') mode=check ;;
  --selftest) mode=selftest ;;
  *)
    echo "check-embedded-copies: unknown argument '$1' — pass --selftest or nothing" >&2
    exit 2
    ;;
esac

MODE="$mode" python3 - "$repo_root" <<'PY'
import os
import re
import shutil
import sys
import tempfile

repo_root = sys.argv[1]
LIBRARY = os.path.join(repo_root, "scripts", "lib", "release-common.sh")

# consumer path -> [(block name, library function, comparison mode)]
CONSUMERS = {
    os.path.join(repo_root, "install.sh"): [
        ("sha256_of", "rc_sha256_of", "text"),
        ("lower", "rc_lower", "text"),
        ("detect_os", "rc_detect_os", "cases"),
        ("detect_arch", "rc_detect_arch", "cases"),
    ],
    os.path.join(repo_root, "npm", "tl", "bin", "tl"): [
        ("detect_os", "rc_detect_os", "cases"),
        ("detect_arch", "rc_detect_arch", "cases"),
    ],
}


def read(path):
    with open(path, encoding="utf-8") as handle:
        return handle.read()


def embedded_block(text, name, path):
    """The lines between the BEGIN/END markers for `name`."""
    pattern = re.compile(
        r"^# EMBEDDED-COPY-BEGIN " + re.escape(name) + r"\n(.*?)^# EMBEDDED-COPY-END "
        + re.escape(name) + r"\n",
        re.S | re.M,
    )
    found = pattern.search(text)
    if found is None:
        raise LookupError(
            f"{path} has no '# EMBEDDED-COPY-BEGIN {name}' / '# EMBEDDED-COPY-END {name}' "
            f"block. Either the copy was deleted (then delete its row in "
            f"scripts/check-embedded-copies.sh too, deliberately) or the markers were lost, "
            f"which silently retires this guard."
        )
    return found.group(1)


def library_function(text, name):
    """The body of a top-level `name() { … }` in the library."""
    start = re.search(r"^" + re.escape(name) + r"\(\) \{\n", text, re.M)
    if start is None:
        raise LookupError(
            f"scripts/lib/release-common.sh defines no function {name}(). The consumer copies "
            f"guarded here have nothing left to be compared against; restore it or retire the row."
        )
    rest = text[start.end():]
    end = re.search(r"^\}\n", rest, re.M)
    if end is None:
        raise LookupError(f"{name}() in the library has no closing brace at column 0")
    return rest[: end.start()]


def normalize_text(body):
    """Body lines, comments and blanks dropped, `rc_` naming prefixes removed."""
    out = []
    for line in body.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        # The library namespaces everything; the embedded copies cannot, since
        # they are not part of a library. That difference is naming, not
        # behaviour, so it is normalized away rather than reported as drift.
        stripped = re.sub(r"\brc__?", "", stripped)
        out.append(stripped)
    return out


# A case *pattern* is shell globs and alternation and nothing else. Message
# text is full of parentheses — `'$(uname -s)'` closes one on almost every
# refusal line — so a looser "everything before the first `)`" rule reads those
# as arms and reports the two files as disagreeing about wording rather than
# about classification.
ARM_HEAD = re.compile(r"^([A-Za-z0-9_*?.| \t-]+)\)\s*(.*)$")


def case_map(body, path, name):
    """pattern -> assigned value, for every arm of the single case statement."""
    arms = {}
    current = None
    for line in body.splitlines():
        stripped = line.strip()
        if stripped.startswith(("case ", "esac", "#")) or not stripped:
            continue
        head = ARM_HEAD.match(stripped)
        if head and not stripped.startswith(";;"):
            current = head.group(1).strip()
            arms.setdefault(current, None)
            stripped = head.group(2).strip()
        assign = re.match(r"^[A-Za-z_][A-Za-z0-9_]*=([A-Za-z0-9_-]+)", stripped)
        if assign and current is not None and arms.get(current) is None:
            arms[current] = assign.group(1)
    if not arms:
        raise LookupError(
            f"the {name} block in {path} has no case arms to compare — the block markers "
            "probably no longer wrap the mapping, which would leave this guard reporting "
            "success over nothing."
        )
    return arms


def compare(consumer_path, library_text, rows):
    problems = []
    consumer_text = read(consumer_path)
    rel = os.path.relpath(consumer_path, repo_root)
    for name, lib_name, mode in rows:
        block = embedded_block(consumer_text, name, rel)
        lib_body = library_function(library_text, lib_name)
        if mode == "text":
            got, want = normalize_text(block), normalize_text(lib_body)
            # The embedded copy is a bare function; the library's is too, so the
            # comparison is over the body lines only.
            got = [ln for ln in got if not re.fullmatch(r"\w+\(\) \{|\}", ln)]
            want = [ln for ln in want if not re.fullmatch(r"\w+\(\) \{|\}", ln)]
            if got != want:
                problems.append(
                    f"{rel}: the embedded {name} has drifted from {lib_name} in "
                    f"scripts/lib/release-common.sh.\n"
                    f"    embedded: {got}\n"
                    f"    library:  {want}\n"
                    f"    Bring the copy back in line, or change both together."
                )
        else:
            got = case_map(block, rel, name)
            want = case_map(lib_body, "scripts/lib/release-common.sh", lib_name)
            # Arms that only refuse assign nothing; compare the classification.
            got_map = {k: v for k, v in got.items() if v}
            want_map = {k: v for k, v in want.items() if v}
            if got_map != want_map or set(got) != set(want):
                problems.append(
                    f"{rel}: the embedded {name} classifies platforms differently from "
                    f"{lib_name} in scripts/lib/release-common.sh.\n"
                    f"    embedded: {got}\n"
                    f"    library:  {want}\n"
                    f"    A copy that maps a uname to a different target ships the wrong "
                    f"binary to that platform."
                )
    return problems


def run(library_path, consumers):
    library_text = read(library_path)
    problems = []
    for path, rows in consumers.items():
        problems.extend(compare(path, library_text, rows))
    return problems


if os.environ.get("MODE") == "selftest":
    # A gate that quietly stopped comparing would pass forever, so it proves it
    # can still catch each class of drift before its silence is believed. Every
    # case runs against copies in a throwaway tree; the checkout is untouched.
    failures = 0

    def note(ok, name):
        global failures
        if ok:
            print(f"  ok   {name}")
        else:
            print(f"  FAIL {name}", file=sys.stderr)
            failures += 1

    print("check-embedded-copies --selftest:")
    work = tempfile.mkdtemp()
    try:
        os.makedirs(os.path.join(work, "scripts", "lib"))
        os.makedirs(os.path.join(work, "npm", "tl", "bin"))
        shutil.copy(LIBRARY, os.path.join(work, "scripts", "lib", "release-common.sh"))
        for path in CONSUMERS:
            shutil.copy(path, os.path.join(work, os.path.relpath(path, repo_root)))

        def at(rel):
            return os.path.join(work, rel)

        def consumers_at():
            return {
                at(os.path.relpath(p, repo_root)): rows for p, rows in CONSUMERS.items()
            }

        lib_at = at("scripts/lib/release-common.sh")

        note(not run(lib_at, consumers_at()), "the committed copies agree (the fixture starts clean)")

        # Text drift: change one line of the installer's digest helper.
        original = read(at("install.sh"))
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original.replace("shasum -a 256 \"$1\"", "shasum -a 1 \"$1\""))
        note(bool(run(lib_at, consumers_at())), "a changed line in an embedded sha256_of is caught")
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original)

        # Classification drift: the installer maps aarch64 to the wrong target.
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original.replace("arm64 | aarch64) install_arch=arm64", "arm64 | aarch64) install_arch=x64"))
        note(bool(run(lib_at, consumers_at())), "an embedded uname mapping to the wrong target is caught")
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original)

        # A dropped arm: the installer stops recognising a platform the library does.
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original.replace("    x86_64 | amd64) install_arch=x64 ;;\n", ""))
        note(bool(run(lib_at, consumers_at())), "an arm dropped from an embedded mapping is caught")
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original)

        # A dropped *refusal* arm is the subtler half: nothing is misassigned,
        # the platform simply falls through to `*` and gets a worse message —
        # or, if `*` assigned anything, the wrong binary.
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original.replace("    MINGW* | MSYS* | CYGWIN* | Windows_NT)\n", "    MINGW-DROPPED)\n"))
        note(bool(run(lib_at, consumers_at())), "a refusal arm renamed out of an embedded mapping is caught")
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original)

        # A deleted marker must be an error, not a silently skipped row.
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original.replace("# EMBEDDED-COPY-BEGIN sha256_of\n", ""))
        try:
            run(lib_at, consumers_at())
            note(False, "a deleted block marker is refused rather than skipped")
        except LookupError:
            note(True, "a deleted block marker is refused rather than skipped")
        with open(at("install.sh"), "w", encoding="utf-8") as handle:
            handle.write(original)

        # A library function that vanished must be an error too.
        lib_original = read(lib_at)
        with open(lib_at, "w", encoding="utf-8") as handle:
            handle.write(lib_original.replace("rc_lower() {", "rc_lower_renamed() {"))
        try:
            run(lib_at, consumers_at())
            note(False, "a renamed library function is refused rather than skipped")
        except LookupError:
            note(True, "a renamed library function is refused rather than skipped")
        with open(lib_at, "w", encoding="utf-8") as handle:
            handle.write(lib_original)
    finally:
        shutil.rmtree(work, ignore_errors=True)

    if failures:
        print(
            f"check-embedded-copies: --selftest found {failures} broken case(s). This gate no "
            "longer detects drift between the library and the copies that cannot source it — "
            "repair it before trusting a green run.",
            file=sys.stderr,
        )
        sys.exit(1)
    print("check-embedded-copies: --selftest passed")
    sys.exit(0)

try:
    problems = run(LIBRARY, CONSUMERS)
except LookupError as exc:
    print(f"check-embedded-copies: {exc}", file=sys.stderr)
    sys.exit(1)

if problems:
    print("check-embedded-copies: an embedded copy has drifted from the library.", file=sys.stderr)
    for problem in problems:
        print(f"  {problem}", file=sys.stderr)
    sys.exit(1)

checked = sum(len(rows) for rows in CONSUMERS.values())
print(
    f"check-embedded-copies: {checked} embedded cop(ies) across {len(CONSUMERS)} file(s) "
    "still match scripts/lib/release-common.sh"
)
PY
