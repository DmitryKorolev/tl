# ADR-0019 — Native primitives shim, and the FFI policy

- Status: Accepted
- Date: 2026-06-10

## Context

ADR-0015 pins behaviors the pinned toolchain (Lean 4 v4.30.0) cannot express:

- **fsync after append** (§2). `IO.FS.Handle.flush` drains the userspace
  buffer into the kernel, not the kernel to disk — so an acknowledged op can
  sit in the page cache and vanish on power loss, and the clock file can
  regress relative to the durable log (the HLC-monotonicity hazard the §1
  critical-section ordering exists to prevent). No fsync is exposed anywhere
  in core.
- **No-follow opens** (§6, the ADR-0014 T4 symlink defense). `Handle.mk`
  maps its closed `Mode` enum onto fixed `open(2)` flag sets (`writeNew` =
  `O_CREAT|O_TRUNC|O_EXCL`, `append` = `O_CREAT|O_APPEND`, `O_CLOEXEC` always) — so
  plain exclusive creation *is* expressible, but no mode adds `O_NOFOLLOW`,
  none combines EXCL/APPEND without truncation, and there are no
  dirfd-relative opens. The workaround — `lstat`, then open — is exactly the
  TOCTOU race the open *flag* exists to close.

Two near-misses sharpen the gap. `Handle.lock`/`tryLock`/`unlock` exist
(`flock`/`LockFileEx` underneath) — but they operate on a `Handle` from the
path-based `Handle.mk`, which cannot honor §6 for `.tl/local/lock` itself
(a `Mode.write`/`append` open would create or truncate *through* a planted
symlink — the very T4 write being defended against). And `IO.getRandomBytes`
exists — but its own docstring says it "is not guaranteed to be
cryptographically secure," so it cannot silently discharge ADR-0007's CSPRNG
mandate for replica-id and nonce entropy (tier-3 forbids exactly that silent
reliance; today's `Replica.mint` is worse still — it uses the plain-PRNG
`IO.rand`, a defect fixed alongside this wiring). What core *does* cover:
`IO.FS.rename` (the §3 atomic replace) and `createTempDir`/`withTempDir`
(test fixtures).

Filling the gap means C in the build — a decision about build and dependency
architecture (ADR-0006: cross-compilation, reproducible signed releases), and
a precedent that needs a stated boundary before it exists.

## Decision

### A minimal, self-contained C shim

A small C file vendored in-repo (`ffi/tlsys.c`), exposed to Lean as
`Tl/Store/Sys.lean`. It owns its file descriptors end-to-end and touches
**no Lean runtime internals** (no peeking into `Handle`'s external object),
so toolchain bumps cannot break it. Functions — *mechanism only*, each
existing because a specific ADR-pinned behavior requires it:

- `openNoFollow` — open with `O_NOFOLLOW | O_CLOEXEC` and caller-selected
  `O_APPEND` / `O_CREAT|O_EXCL`, returning an fd. `O_NOFOLLOW` guards only
  the final path component, and §6 refuses a symlink at *any* `.tl`
  component — so the directory chain is walked component-by-component via
  `openat(…, O_NOFOLLOW)`, hardened where available by
  `openat2(RESOLVE_NO_SYMLINKS)` on Linux and `O_NOFOLLOW_ANY` on Darwin
  (reparse-point refusal is the Win32 analog).
- `readAll fd` / `writeAll fd bytes` — segment and clock I/O on the shim's
  own fds (§5 reads are `.tl` opens too, so they ride the same discipline).
- `sync fd` — `fsync`; `F_FULLFSYNC` on Darwin (where plain `fsync` stops at
  the drive's cache — data is not guaranteed durable at return);
  `FlushFileBuffers` as the Win32 equivalent (§2).
- `lock fd exclusive blocking` — `flock` on the shim fd (`LockFileEx` on
  Win32), giving §1's mutation lock on a §6-compliant open of
  `.tl/local/lock`; core's `Handle.lock` stays the right tool for any
  non-`.tl` locking need.
- `entropy n` — n bytes from the OS CSPRNG (`getentropy`/`getrandom`;
  `BCryptGenRandom` on Win32), discharging ADR-0007's replica/nonce
  requirement with a contract core does not promise.
- `ownedByCaller fd` — the §6 ownership check, computed in C (owner uid vs
  caller euid; the Win32 owner-SID analog is Tier-2 best-effort per §7).
- `close fd`.

The §6 *policy* — the `.tl` path discipline, what to refuse, the error codes
(`lock-busy`, the T4 refusals) — stays in tested Lean above the shim. The
shim ships with per-branch tests like any shell code (AGENTS.md DoD: tests in
the same change): symlink refusal at final and intermediate components,
`O_EXCL` collision, append+sync round-trips, lock contention, plus
hostile-fixture tests at the Store layer.

### Build wiring (and its one-time cost)

The C file is compiled by the toolchain's bundled compiler via a custom Lake
target linked through `moreLinkObjs` (the pinned Lake deprecates `extern_lib`
in favor of exactly this). Custom targets are Lean-DSL-only and Lake's TOML
loader supports none of them — so landing the shim **migrates the root
`lakefile.toml` to `lakefile.lean`**, a one-time mechanical change recorded
here. (The alternative — a path-`require`d subpackage holding the C target —
was rejected: two build configs for one small repo.)

### The FFI policy (the precedent this sets)

**FFI is admissible only for OS primitives the pinned toolchain cannot
express or does not contractually guarantee — never for library-shaped
problems.** Crypto, compression, JSON, hashing: those get pure-Lean
implementations or explicit ADRs rejecting them (ADR-0018 is the worked
example — it rejects libsodium under this policy). Mechanism lives in C;
policy, error mapping, and every branch the tests must cover live in Lean. A
shim addition cites the ADR that pins the behavior requiring it.

### What the shim is deliberately not

Not rename (`IO.FS.rename` covers §3), not temp-dir plumbing (core
`withTempDir`), not a general POSIX binding layer. Platform scope follows
ADR-0015 §7: the POSIX implementation is the gating, fully-tested path
(Linux, macOS, Windows-via-WSL — ADR-0006); the native-Win32 column is
designed there and remains Tier-2 best-effort.

### Upstreaming intent

The fsync half is a natural Lean-core addition (`Handle.sync`): it fits the
existing `Handle` API precedent (`lock` was added when Lake needed it), the
platform mapping is settled knowledge, and the runtime's libuv migration
already bundles `uv_fs_fsync`. We propose it upstream as a separate small
patch; a strengthened contract for `IO.getRandomBytes` (or a core
`getentropy`) is a second candidate. When a pinned toolchain ships either,
the corresponding shim function is deleted. The no-follow open machinery is
*not* expected to upstream (it needs an open-options API redesign plus a
Win32 reparse-semantics debate) and stays vendored. Because call sites reach
the shim only through `Tl/Store/Sys`, swapping mechanism for a core API never
touches the Store.

## Consequences

- ADR-0015's pinned contract is implementable **as written** — no fsync
  degraded to flush, no racy stat-then-open standing in for §6, and the lock,
  reads, and writes all ride §6-compliant opens.
- Durability is honest: `F_FULLFSYNC` on Darwin trades a slower append for
  the actual guarantee. Durability remains best-effort by design (ADR-0015
  §2: the durable publish is `git push`) — the shim narrows the
  acknowledged-op loss window to the pinned mechanism's, and preserves the
  fsync-before-clock-persist ordering §1 requires.
- The build gains one in-repo C file compiled by the toolchain's own
  compiler — no external library, version pin, or supply-chain root; the
  ADR-0006 signing/reproducibility story adds only our own source. The
  lakefile migrates to the Lean DSL once, recorded above.
- The policy line is on record before the first exception is tempted:
  library-shaped problems do not get C-library answers.
- Tier-2 like the rest of the shell: the shim *relies on* carried
  assumptions already recorded (working `O_APPEND` atomicity and advisory
  locks, overview.md Trusted) and adds no new ones — it narrows how much
  behavior rests on them.

## Alternatives considered

- **Ship degraded, pure-Lean only** (`flush` for durability, `lstat`-then-
  open for symlinks, `IO.getRandomBytes` as-is for entropy). Rejected: it
  silently weakens the pinned contract — `flush` keeps the acknowledged-op
  loss window and the clock-ordering hazard, the stat-then-open race defeats
  T4 precisely when attacked, and the entropy contract is explicitly
  disclaimed by its own docstring. Shipping that would require an explicit
  ADR-0015/0007 amendment recording the weaker truth; the shim is less work
  than writing the deferral honestly.
- **Core `Handle.lock` + `Handle.mk` for the lock file.** Rejected: no
  `Handle.mk` mode opens without following symlinks, and the writable modes
  create or truncate through one — the lock file is a `.tl` file and gets no
  exemption from §6.
- **Wait for upstream** (`Handle.sync`, a guaranteed-CSPRNG
  `getRandomBytes`, or the libuv-based IO). Months of latency gated on a
  toolchain bump *and* a matching Mathlib release; Stage 1 needs the
  primitives now. Upstreaming proceeds in parallel instead.
- **Adopt a native library** (libsodium et al.) since "we have FFI anyway."
  Rejected: it is the policy violation this ADR exists to name; see
  ADR-0018's alternatives for the worked case.
- **Implement `Handle.sync` against Lean's own handles** by extracting the
  `FILE*` from the external object (`lean_get_external_data` → `fileno`).
  Rejected: couples to undocumented runtime layout across toolchain bumps;
  the self-contained fd design owns its resources and survives upgrades.
- **A WAL/SQLite for local state**, sidestepping fsync-on-append. Already
  rejected in ADR-0015 ("the log *is* the WAL").
