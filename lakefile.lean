/-
Lake config (migrated from `lakefile.toml` when the ADR-0019 native shim
landed — custom targets are Lean-DSL-only).

`lake build` (no target) must verify the proofs (AGENTS.md / CI gate), so the
default set is the verified kernel lib `Tl`, the `Tests` sources, and both
exes — NOT just the `tl` binary. Proof/test discipline: batteries (std4) by
default; Mathlib adopted under the ADR-0009 escape hatch, scoped to the
reachability/cardinality proof modules. Pins are immutable commits, not
branches/tags (ADR-0009).
-/
import Lake
open Lake DSL

package tl where
  version := v!"0.1.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @
  -- v4.32.0, matching the pinned lean-toolchain (leanprover/lean4:v4.32.0)
  "023ce7d62a0531e22a5331e20b587817a80d49ff"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  -- v4.32.0 (matching the toolchain); ADR-0009 escape hatch, scoped to the
  -- finite-graph lemmas for thms 5/6/10 + rollup fuel-adequacy
  "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target] lean_lib Tl

/-- The tested-shell test sources (ADR-0009); built by the `tltest` exe. -/
@[default_target] lean_lib Tests

/-- The ADR-0019 native shim, statically linked into both exes via
    `moreLinkObjs` (the pinned Lake deprecates `extern_lib` in favor of
    exactly this). Compiled with the host `cc`: the toolchain's bundled
    clang ships no system-header sysroot on macOS (`stdio.h` unresolvable
    even via `leanc`/`SDKROOT`), and a host C toolchain is already a
    build-from-source prerequisite for linking. -/
target tlsys.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "ffi" / "tlsys.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / "tlsys.c"
  let leanInclude := (← getLeanIncludeDir).toString
  buildO oFile srcJob #["-I", leanInclude] #["-fPIC", "-O2"]

@[default_target] lean_exe tl where
  root := `Main
  moreLinkObjs := #[`@/tlsys.o]

/-- In-repo test runner for the tested I/O shell (ADR-0009): `lake exe tltest`. -/
@[default_target] lean_exe tltest where
  root := `Tests.Main
  moreLinkObjs := #[`@/tlsys.o]
