# Rebuilding tl, and relinking GMP

This file ships with every release, alongside `LICENSE`, `THIRD-PARTY-LICENSES`
and the SBOM. It exists for two audiences: anyone who wants to check that a
published binary corresponds to this source, and anyone exercising the LGPLv3
section 4 right to substitute their own GMP and relink.

## What the release tells you, and what it does not

Each release publishes, for every target, the binary, its SHA-256 in the signed
`SHA256SUMS`, a Sigstore bundle binding it to this repository's release
workflow, and `build-metadata-<target>.json` recording the runner, the Lean
toolchain and the `lake-manifest.json` digest that leg built with.

Together those establish *this binary was produced by that workflow from that
commit*. They do not establish that the bytes are derivable from the source by
anyone else: tl is not yet a reproducible build, and ADR-0006 carries that as an
open item. `tl version` reporting `clean build — commit X` is the workflow's
claim about its own inputs, not a property you can re-derive. Rebuilding from
the same commit gives you a binary that behaves identically and passes the same
proofs; it will not generally be byte-identical.

## Rebuilding from source

```sh
git clone https://github.com/DmitryKorolev/tl
cd tl
git checkout <the tag, for example v0.1.0>

# elan reads lean-toolchain and installs exactly the pinned compiler.
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

lake exe cache get   # prebuilt mathlib oleans; building them from source takes hours
lake build tl        # the binary, at .lake/build/bin/tl
```

Two pins fix the dependency set completely: `lean-toolchain` names the compiler,
and `lake-manifest.json` pins every Lake dependency to an immutable commit
(ADR-0009). The SBOM shipped with the release lists both. To confirm you built
from the same inputs as the release:

```sh
sha256sum lake-manifest.json     # matches lakeManifestSha256 in release-manifest.json
.lake/build/bin/tl version --json
```

To reproduce the release's own build environment rather than your machine's,
the Linux artifacts are built inside the glibc-floor container image pinned by
digest in `.github/workflows/release.yml`; the macOS ones are built on the
GitHub-hosted runner image named in `build-metadata-<target>.json`.

## Relinking GMP (LGPLv3 §4)

tl links GMP statically, inherited from the Lean toolchain rather than vendored
by this project: Lean's binary releases bundle `libgmp.a` and link it into
`libleanshared`, so every Lean-compiled binary contains it. tl elects the
LGPL-3.0 option of GMP's dual license (see the licensing section of ADR-0006).

Section 4 requires that a recipient be able to substitute a modified GMP and
relink. Because tl is Apache-2.0 open source with a pinned build system, that
obligation is met the same way Lean meets it — the full source and the exact
toolchain are public, so you can rebuild the whole binary against your own GMP:

1. Build or obtain your GMP.
2. Build a Lean toolchain against it. GMP enters tl's binary through the Lean
   runtime, so the substitution happens at the toolchain layer, not in tl:
   see the Lean 4 build instructions and point its GMP discovery at yours.
3. Rebuild tl with that toolchain, following the steps above but with `elan`
   overridden to your local toolchain (`elan toolchain link` and
   `elan override set`).

No separate object-file drop is required while tl remains open source. A closed
source fork would instead owe section 4 object files; that is out of scope here.

GMP upstream: <https://gmplib.org/>. The full LGPLv3 text and GMP's notice are
in the `THIRD-PARTY-LICENSES` file shipped with this release, along with every
other component of the link-time set. `link-audit-<target>.txt` records what
that target's binary actually links against, so the notice can be checked
against the artifact rather than taken on trust.
