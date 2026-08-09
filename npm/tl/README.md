# tl

A formally verified, git-native task tracker for AI agents.

```sh
npm install -g @taskloop/tl
tl init
tl ready --json
```

Every command takes `--json`. Agents should branch on the structured result —
`error.code` is a stable enum — never on prose. `tl help --json` is the
machine-readable grammar.

## What this package installs

`tl` is a compiled [Lean 4](https://lean-lang.org) binary, not JavaScript. This
package contains a small POSIX shell launcher and declares one optional
dependency per platform; npm installs the single matching one and the launcher
`exec`s it, so signals and exit status belong to `tl` directly.

There is no `postinstall` script and nothing is downloaded at install time. The
binaries arrive as ordinary npm tarballs whose integrity the registry client
checks, from packages pinned to an exact version.

| Platform | Package |
|---|---|
| macOS arm64 | `@taskloop/tl-bin-darwin-arm64` |
| macOS x86-64 | `@taskloop/tl-bin-darwin-x64` |
| Linux arm64 | `@taskloop/tl-bin-linux-arm64` |
| Linux x86-64 | `@taskloop/tl-bin-linux-x64` |

Windows is supported through WSL2, which installs the Linux x86-64 package
normally. Native Windows is refused rather than installed: `tl`'s filesystem
primitives are unimplemented there, so the binary would start but could not
safely create or mutate task state.

`git` must be on `PATH` (2.17 or newer) — `tl` shells out to it for transport.

## Verifying what you installed

The binaries in the platform packages are byte-identical to the assets on the
[GitHub Release](https://github.com/DmitryKorolev/tl/releases), which are signed
with Sigstore and pinned to this repository's release workflow. To check a
published npm tarball independently, compare its binary against the
correspondingly named release asset and verify that asset per
[VERIFYING.md](https://github.com/DmitryKorolev/tl/blob/main/VERIFYING.md).
This package is also published with npm provenance.

## Links

- [Repository, docs, and ADRs](https://github.com/DmitryKorolev/tl)
- [What `tl` is and why](https://github.com/DmitryKorolev/tl/blob/main/docs/vision.md)
- [The proved-versus-tested boundary](https://github.com/DmitryKorolev/tl/blob/main/docs/overview.md)
