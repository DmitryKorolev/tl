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
  -- v4.33.0, the rev mathlib's own v4.33.0 manifest pins
  "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  -- v4.33.0 (matching the toolchain); ADR-0009 escape hatch, scoped to the
  -- finite-graph lemmas for thms 5/6/10 + rollup fuel-adequacy
  "db584cd6d46c92f209a44c0f1c829460d327499d"

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

/-- A hostile initializer fixture. It is compiled but only ever imported by
    the verifier worker with extension loading disabled. -/
lean_lib VerifyFixtures where
  roots := #[`VerifyFixture.EarlyExit]

/-- In-repo test worker for the tested I/O shell. The public `tltest` target is
    a minimal supervisor so an initializer cannot exit zero before the harness. -/
lean_exe tltestWorker where
  root := `Tests.Main
  moreLinkObjs := #[`@/tlsys.o]

/-- Lean-native trust-boundary verifier. The audited roots are dynamic imports
    because separately compiled roots can share declaration names. `needs`
    makes every audited olean part of the build graph before the verifier runs.
    Run the gate with `lake exe tlverify`; it reads source inventory on every
    invocation and independently replays stored declarations through Lean's
    kernel. -/
lean_lib VerifyCore where
  roots := #[`Verify.Report, `Verify.Policy, `Verify.Environment, `Verify.Supervise,
    `Verify.Proofs]

/-- Executable Lean build tooling is semantically audited as a separate root. -/
lean_lib Tooling where
  roots := #[`scripts.GenLicenses]

/-- The release decision layer.

    It is deliberately *not* reachable from `Tl`: release administration must
    not become part of the shipped product, so nothing here is in the binary
    users run, and nothing here may import `Tl.*` — the trust gate's `release`
    scope reports such an import as a module outside the declared scope.
    Batteries only, which also keeps it independent of the ADR-0009 Mathlib
    escape hatch. -/
lean_lib ReleaseCore where
  roots := #[`release.Check, `release.Command, `release.Json, `release.Model,
    `release.Boundary, `release.Write, `release.Sys,
    `release.Certificate, `release.Consistency, `release.Identity, `release.Plan, `release.Sbom, `release.Process,
    `release.Digest, `release.Metadata, `release.Prerequisites, `release.Manifest,
    `release.Homebrew, `release.Npm, `release.Platform, `release.Policy, `release.Stamp,
    `release.TaskId,
    `release.Cli]

/-- A default target so `lake build --wfail` holds the release tool to the same
    warning-free standard as everything else. `release.Main` is a three-line
    root defining `main`, kept separate so tests can import the decisions. -/
@[default_target] lean_exe tlrelease where
  root := `release.Main
  needs := #[ReleaseCore]
  moreLinkObjs := #[`@/tlsys.o]

/-- Minimal test supervisor: status zero is insufficient unless the worker
    reaches the assertion harness's final completion marker. -/
@[default_target] lean_exe tltest where
  root := `Verify.TestLauncher
  needs := #[tltestWorker]

lean_exe tlverifyWorker where
  root := `Verify.Main
  needs := #[Tl, Tests, VerifyCore, VerifyFixtures, Tooling, ReleaseCore, tl, tltest, tlrelease]

/-- Minimal supervisor: status zero is insufficient unless the audited worker
    reaches and emits its final structured completion marker. -/
lean_exe tlverify where
  root := `Verify.Launcher
  needs := #[tlverifyWorker]
