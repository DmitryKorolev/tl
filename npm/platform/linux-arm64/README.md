# @taskloop/tl-bin-linux-arm64

The prebuilt `tl` binary for Linux on arm64.

This package exists so that `npm install @taskloop/tl` downloads one
binary rather than all four. Install [`@taskloop/tl`](https://www.npmjs.com/package/@taskloop/tl)
instead; npm selects this package through `os`/`cpu` constraints and the
launcher in that package execs the binary below.

The binary here is byte-identical to this platform's asset on the matching
[GitHub Release](https://github.com/DmitryKorolev/tl/releases), which carries a
Sigstore signature you can verify independently — see
[VERIFYING.md](https://github.com/DmitryKorolev/tl/blob/main/VERIFYING.md).
