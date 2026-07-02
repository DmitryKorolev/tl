# ADR-0015 — Local concurrency and filesystem safety

- Status: Accepted
- Date: 2026-06-05

## Context

`tl` has no daemon: every command is a fresh process, and several may run at
once against the same working copy — an agent's `ready` read while another
command's `create` writes, two parallel agents, or a `sync` refreshing fetched data while
a mutation appends. State lives in per-replica append-only segments
`.tl/log/<replica-id>.jsonl` plus two mutable local files, `.tl/local/clock`
(HLC) and `.tl/local/replica` (ADR-0001/0007). This is all I/O-shell code
(tested, not proved — AGENTS.md tier 2), but it is load-bearing: a lost or
torn write, a regressed clock, or a redirected path corrupts the very log the
verified kernel folds. This ADR pins the local concurrency and filesystem
contract; cross-replica reconciliation is `sync` (ADR-0001) and the on-disk
record shape is ADR-0008.

Note the CRDT keeps *convergence* total even without any of this — the per-op
nonce makes LWW a function regardless of interleaving (ADR-0007). So the
mechanisms here protect monotonicity, durability, ownership, and
availability, not convergence.

## Decision

### 1. One writer at a time per working copy — a mutation lock
A single advisory exclusive lock on `.tl/local/lock` is held for the whole
mutating critical section of an invocation: *acquire → read+advance the HLC
(`.tl/local/clock`) → append the record(s) → fsync → persist the clock →
release*. This serializes mutators within one working copy, so HLC minting
is a clean read-modify-write (no two ops racing the same `(physical, logical)`),
a multi-record command (`create --blocked-by` = `create` + `depAdd`) appends its
lines without another writer interleaving, and the clock never regresses from a
lost update. Acquisition is a bounded blocking wait: a contending writer
blocks for a short bounded timeout (a few seconds), then fails with the
`lock-busy` error (ADR-0008) rather than blocking forever — agents fire many short
commands, so a brief wait usually wins while a hung holder surfaces instead of
stalling the tracker. No stale-lock reclaim is needed: the advisory lock
(`flock`/`fcntl`, `LockFileEx`) is released by the OS when the holding process
exits, so a crashed holder leaves nothing to clean up. The lock is per-working-copy only — it does not coordinate
across machines (that is `sync`) and is not required for convergence (a
missed lock degrades to the nonce tie-break), so a filesystem without working
locks falls back to best-effort with the nonce as the guarantee.

### 2. Appends are atomic, one record per write
Each record is one `O_APPEND` write of a single LF-terminated line; the writer
never `seek`s. On a local POSIX filesystem `O_APPEND` makes the offset-update +
write atomic, so even a lock-bypassing or cross-tool writer cannot interleave
bytes within a record. Crash hygiene: on open a writer first ensures the
segment ends in `\n` (appending one if a crashed fragment left a newline-less
tail) so a later append never fuses onto a partial record (ADR-0008). The writer
fsyncs after appending — durability is best-effort; the durable publish is `git
push` (ADR-0001).

### 3. `sync` never rewrites its own segment
The replica's own segment is append-only authority; `sync` only *reads* it.
(The one pinned, not-yet-built exception is the explicit destructive
`tl compact`, which trims the own segment last via the same atomic
temp-file + `rename` under the mutation lock — ADR-0008's pinned design; a
routine `sync` never rewrites it.)
`sync` = fetch `refs/tl/log` → union all segments → push a candidate ref. Locally
it writes back only the other replicas' segments (read-only caches for
folding), and does so atomically — write a temp file in `.tl/local/`, then
`rename` over the target (atomic replace; an open reader keeps its old inode).
Because the own segment is never rewritten, the "sync rewrite races a local
append" hazard simply does not exist for the authoritative data.

### 4. Mid-sync ops are not lost
A mutation may append to the own segment *during* a fetch→union→push round.
The local-first leg (ADR-0016 §1) publishes the own segment into `refs/tl/log`
under CAS before the remote leg runs, and the remote leg re-reads the local ref
(`readRef`) at the start of each attempt — so on a non-fast-forward rejection it
re-fetches, re-unions against the now-larger local ref, and retries. Ops
appended mid-round are picked up by the next attempt, never dropped. The remote
leg works at the ref level and holds no mutation lock.

### 5. Readers are lock-free and see a consistent-enough snapshot
`ready`/`show`/`list`/… take no lock. Atomic appends (§2) and atomic
renames (§3) mean each segment reads as a coherent snapshot: a concurrent append
is fully present or absent (never torn), and a concurrent foreign-segment refresh
leaves the reader on its opened inode. A reader folds each segment to its last
LF; a non-LF-terminated trailing fragment is an uncommitted write, skipped
silently (not corruption). A *complete* (LF-terminated) line that fails to
parse, or an unknown `op`/version, is the segment-scoped fail-closed case
(ADR-0008 §corruption): refuse that one segment, fold the rest, disclose it
(command-level outcome — foreign segment: the read succeeds; own/every
segment: it fails — ADR-0008 §corruption).
Cross-segment skew is harmless — the fold is order/dup-insensitive (ADR-0004), so
a reader always sees *some* valid converged state, at worst a moment stale.

Read-time refresh (ADR-0016). Before folding, a reader compares the shared
`refs/tl/log` OID against the last-materialized OID in `.tl/local/` (an O(1)
check). If the ref moved — a sibling worktree synced — it materializes the changed
foreign segments via the §3 atomic rename, so a *read* may perform the same
foreign-cache writeback as `sync` (no mutation lock). On a read-only filesystem it
skips the refresh and folds what it has (a moment stale), never failing the read;
concurrent refreshers are safe (the content is a pure function of the ref OID, and
atomic rename makes last-writer-wins harmless).

### 6. Path and symlink hardening
All `.tl/` files are opened without following symlinks (POSIX `O_NOFOLLOW`,
or `openat` from a validated `.tl` directory fd; `O_EXCL` on first create),
refusing to operate if any `.tl` path component is a symlink or is not owned by
the current user. `--dir` / `TL_DIR` targets get the same validation. This stops
a hostile local process (a dependency's postinstall, a shared CI tmp) from
redirecting a `tl` write to an attacker-chosen path (ADR-0014 threat T4).

### 7. One platform abstraction (POSIX ↔ Windows), binary I/O
The primitives above are a thin filesystem-abstraction layer, bound per
platform. On the Supported targets — Linux, macOS, and Windows-via-WSL
(ADR-0006) — the POSIX bindings are the gating, fully-tested path. The Windows
column below is the design for *native* Windows, which is best-effort (our
Tier 2): shipped and smoke-tested, but its Win32 paths are not in the
gating matrix, so a native-Windows FS edge is a best-effort fix, not a release
blocker.

| Primitive | POSIX | Windows |
|---|---|---|
| mutation lock (§1) | `flock` / `fcntl` on `.tl/local/lock` | `LockFileEx` (exclusive) on the lock file |
| atomic append (§2) | `O_APPEND` write | `FILE_APPEND_DATA` open (+ the §1 lock) |
| atomic replace (§3) | `rename(2)` | `MoveFileEx(REPLACE_EXISTING\|WRITE_THROUGH)` / `ReplaceFile` |
| no-symlink open (§6) | `O_NOFOLLOW` / `openat` | reject `FILE_ATTRIBUTE_REPARSE_POINT` |

All log and local-file I/O is binary mode (no CRLF translation) on every
platform, so the byte stream — and thus the round-trip and the HLC/id encodings
(ADR-0008/0007) — is identical cross-platform.

## Consequences

- No lost or torn writes, no clock regression, and lock-free fast reads — the
  hot `ready`/`show`/`list` path never blocks on a writer.
- Availability is bounded: a damaged or hostile segment costs only that one
  replica's view, never a tracker-wide stall (ADR-0008 §corruption / ADR-0014
  T2).
- Carried assumptions (overview.md Trusted): `O_APPEND`/`FILE_APPEND_DATA`
  write-atomicity and working advisory locks on the local filesystem.
  Network filesystems (NFS/SMB) may guarantee neither, so a `.tl/` shared over a
  network FS is documented-unsupported (convergence still holds via the
  nonce; ownership/monotonicity do not). Tier-3: tested where testable, trusted
  at the boundary.
- Tier-2 shell, tested comprehensively: every branch — lock contention,
  crash-fragment close, torn-trailing-line skip, atomic-rename-under-read,
  push-window re-snapshot, symlink refusal — ships with per-platform tests
  (AGENTS.md DoD).

## Alternatives considered

- A global lock around reads too. Rejected: needlessly serializes the hot
  read path; atomic append + atomic rename already give readers a consistent
  snapshot.
- `sync` rewrites all segments (incl. its own) under a lock. Rejected: makes
  the own segment a read-modify-write target that races appends; append-only own
  segment + atomic rename of *foreign* caches is simpler and race-free.
- A WAL / SQLite for local state. Rejected: a second on-disk format and a
  heavy dependency for what append-only files + one lock already give — the log
  *is* the WAL.
- A segment file per mutation (lock-free). Rejected: explodes file count and
  complicates `sync`'s union; one append-only segment per replica is the
  ADR-0001 model.
