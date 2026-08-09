# @taskloop/tl-bin-darwin-arm64

The prebuilt `tl` binary for macOS on Apple silicon.

This package exists so that `npm install @taskloop/tl` downloads one
binary rather than all four. Install [`@taskloop/tl`](https://www.npmjs.com/package/@taskloop/tl)
instead; npm selects this package through `os`/`cpu` constraints and the
launcher in that package execs the binary below.

The binary here is byte-identical to the correspondingly named asset on the
[GitHub Release](https://github.com/DmitryKorolev/tl/releases) (`tl-darwin-arm64`),
which carries a Sigstore signature you can verify independently — see
[VERIFYING.md](https://github.com/DmitryKorolev/tl/blob/main/VERIFYING.md).
