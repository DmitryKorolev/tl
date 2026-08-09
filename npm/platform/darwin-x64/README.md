# @taskloop/tl-bin-darwin-x64

The prebuilt `tl` binary for macOS on Intel.

This package exists so that `npm install @taskloop/tl` downloads one
binary rather than all four. Install [`@taskloop/tl`](https://www.npmjs.com/package/@taskloop/tl)
instead; npm selects this package through `os`/`cpu` constraints and the
launcher in that package execs the binary below.

The binary here is byte-identical to the correspondingly named asset on the
[GitHub Release](https://github.com/DmitryKorolev/tl/releases) (`tl-darwin-x64`),
which carries a Sigstore signature you can verify independently — see
[VERIFYING.md](https://github.com/DmitryKorolev/tl/blob/main/VERIFYING.md).
