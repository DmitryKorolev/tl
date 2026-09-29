# tl

A git-native task tracker for coding agents, with a formally verified core.

An agent's plan does not survive its own session: task state kept in
context is gone at the next compaction or clear, and task state kept in a
shared TODO file turns into merge conflicts as soon as two agents write it.
`tl` ("task list") keeps the tracker in the repo itself — an append-only
operation log on a dedicated git ref — and answers the questions an agent
asks at the start of a session:

> *Which tasks are ready now? What is blocking the task I want to start?*

The task state survives a context clear and follows the repo to every agent
and machine through ordinary git syncs. A core proved correct in Lean 4
computes ready work and reports dependency cycles, and stays correct on the
cyclic or dangling graphs that concurrent edits can produce. There is no
server, daemon, or database: git moves the bytes, and a CRDT makes concurrent
writes merge without git conflicts or lost updates.

## The work loop

A session with the current binary (only `init`'s one-time setup hints are
elided). `tl init` creates a gitignored `.tl/` and wires up sharing;
`create` takes dependencies inline:

```console
$ tl init
Initialized tl in /work/payments/.tl (replica 127baztf7p790)

$ tl create "Design the payments schema" -p 1
Created tl-dyc4x8ztgfsnc2j7  Design the payments schema

$ tl create "Write the schema migration" --blocked-by tl-dyc4
Created tl-r835zbdeyht18zt5  Write the schema migration

$ tl create "Update the deploy runbook" --blocked-by tl-r835
Created tl-50mtq61x37sgtrf6  Update the deploy runbook
```

Only the schema task is unblocked, so it is the whole ready queue — and
`why` explains the remaining work as a tree:

```console
$ tl ready
○ tl-dyc4 P1 Design the payments schema
──
Ready: 1 issue(s) with no active blockers
  ○ open   ◐ in_progress   ● blocked   ❄ deferred   ✓ done   ✗ cancelled

$ tl why tl-50mt
tl-50mtq61x37sgtrf6 is blocked.
Remaining work and prerequisites:
└── ● tl-r835 P2 Write the schema migration [blocked]
    └── ○ tl-dyc4 P1 Design the payments schema [open]
```

For an epic, `why` also expands unfinished children and their dependencies,
including nested epics. A task appears once under each parent; shared work is
marked rather than expanded again. Completed and cancelled work stops expansion.

An agent claims the ready item (claiming a blocked, deferred, or
already-claimed one is refused with structured reasons), does the work, and
closes it; the close reports what it just freed:

```console
$ tl claim tl-dyc4 --actor agent-a
Claimed tl-dyc4x8ztgfsnc2j7 as agent-a

$ tl close tl-dyc4 --as done
Closed tl-dyc4x8ztgfsnc2j7 as done (unblocked 1)
```

Agents drive the same loop machine-readably: every command takes `--json`
and returns a stable envelope (fields elided here):

```console
$ tl ready --json
{"schemaVersion":3,"ok":true,"data":{"count":1,"items":[{"blocked":false,…,"id":"tl-r835zbdeyht18zt5",…,"priority":2,"ready":true,"status":"open","title":"Write the schema migration",…}],"staleness":null}}
```

Failures return `"ok": false` with a stable `error.code` to branch on, and
`tl help --json` dumps the whole grammar, so an agent can introspect the
surface instead of guessing it
([ADR-0011](docs/adr/ADR-0011-agent-consumption.md)). The rest of the
surface — epics and `defer`, labels and metadata, `dep cycles`/`path`/
`critical`, `unblocks`, `log --since` (a resumable change feed), `stats`,
`doctor` — is inventoried in [docs/vision.md](docs/vision.md).

Coming from another tracker: transform its export into `tl`'s documented
JSONL import format and run `tl import` once — after that, `tl` owns its
own state; a migration, not an ongoing integration
([ADR-0005](docs/adr/ADR-0005-bulk-import.md)).

## Why tl

- **Verified core.** The state merge, the ready-work computation, cycle
  detection, and epic rollup are proved correct in Lean 4 — theorems, not
  tests (see [What "verified" means](#what-verified-means)).
- **Git-native and serverless.** State lives in the repo, moves between
  clones through your existing git remotes (`tl sync`), and merges without
  conflicts by construction. No daemon, no account, nothing to host;
  everything works offline (a remote sync needs the remote, nothing else
  does), and `git` is the only runtime prerequisite.
- **Small on purpose.** The surface is an agent's work loop plus dependency
  and visibility verbs; what is deliberately out of scope is recorded as a
  contract in [docs/vision.md](docs/vision.md), not left as a backlog.

| Instead of… | The pain it leaves | What `tl` does |
|---|---|---|
| a markdown TODO | no dependency graph, no "what's ready"; concurrent edits conflict in git | dependency-aware `ready`; a CRDT merge with no conflicts or lost updates |
| GitHub Issues / a hosted tracker | a server, auth, rate limits; state lives outside the repo and the agent's git workflow | local, serverless, in-repo; works offline |
| the agent's own context | task state is lost on compaction; nothing crosses sessions or agents | durable shared state; `tl ready` re-grounds an agent on waking |

`tl` is most useful when you need the dependency-aware *"what can I work
on"* loop across sessions, agents, or machines. For a handful of independent
tasks, a TODO file is enough.

## What "verified" means

| Tier | What lives there | Covered by |
|---|---|---|
| Proved | the kernel: CRDT convergence (same ops in any order, any duplication, same state), `ready` soundness + completeness, cycle diagnostics, epic rollup, liveness — all total, even on cyclic or dangling graphs | Lean 4 theorems, re-checked by every `lake build` |
| Tested | the I/O shell: JSONL serialization, the git ref transport and sync, the clock, the importer, the CLI contract, caching, performance scaling | the test suite (`lake exe tltest`) — branch-level coverage is the mandate, and the remaining gaps are themselves recorded in [docs/overview.md](docs/overview.md) |
| Trusted | the boundary — for example replica-id and per-op stamp uniqueness, monotonic clock persistence, git moving bytes faithfully, the system clock | carried assumptions, each recorded explicitly; the full inventory is in [docs/overview.md](docs/overview.md) |

So "verified" means the core logic is mathematically proved correct. It
does not mean the whole binary is bug-free, and it does not mean
distributed locking — see [Limitations](#limitations). The claim-by-claim
table, theorem names included, is [docs/overview.md](docs/overview.md).

## How state moves

The log is the only authority: state is a fold over an append-only log of
operations, and the proved kernel is that fold. (Reads may resume from a
local, content-keyed cache of the fold — discardable, rebuilt whenever
stale, never shared.) Each working copy is a replica appending to its own
log segment; the segments ride `refs/tl/log`, a dedicated git ref, so task
state never touches your branches or commits. `tl sync` publishes your
segment and absorbs everyone else's — and since the fold is insensitive to
operation order and duplication, the union of two logs *is* the merge:
no conflicts to resolve, no ops lost, and concurrent writes to the same
field settled deterministically (last writer wins).

```
  agent writes                              agent reads
  tl create / claim / close                 tl ready / show / why
       │ append one op                           │ fold all ops
       ▼                                         │ (the proved kernel)
  .tl/log/<own-replica>.jsonl ───────────────────┘
       │
       │  tl sync — publish + absorb
       ▼
  refs/tl/log  ◀── fetch · union · push ──▶  the same ref on your remote,
  (a dedicated git ref)                      and on every other clone
```

Worktrees of one repo share the local ref automatically — a read absorbs a
sibling's published ops without an explicit sync; syncing with a remote is
an explicit `tl sync`.

The ref transport is
[ADR-0001](docs/adr/ADR-0001-op-log-on-dedicated-ref.md), the CRDT
construction (OR-Sets plus last-writer-wins registers) is
[ADR-0002](docs/adr/ADR-0002-minimal-crdt.md), the log format is
[ADR-0008](docs/adr/ADR-0008-log-format-versioning-compaction.md), and the
fold cache is
[ADR-0022](docs/adr/ADR-0022-materialization-fold-cache.md);
[docs/vision.md](docs/vision.md) ties them together.

### What sync publishes

`tl sync` publishes task descriptions, notes, actor identities, and their
operation history through `refs/tl/log`, even though `.tl/` is gitignored.
Anyone with access to that ref can inspect them; removing a note from the
current view does not erase its logged operation, so review task data before
making a repository public.

### Local-only modes

Two quieter modes cover projects that are not sharing yet. State
initialized outside any git repository (`tl init` before `git init`) is
simply local-only: once the directory becomes a git repository with a
remote, the next `tl sync` starts sharing it — same log, same ids, no
conversion. `tl init --stealth` deliberately keeps task state local, with no
repo-visible trace; `tl sync` refuses to share it. To start sharing later,
remove `.tl/local/stealth` and run `tl sync` (ADR-0001 §7).

## Build from source

No release has shipped yet; build from source for now. Prebuilt binaries and
the verified installer are planned for v0.1.0; npm and Homebrew are deferred
to v0.2.0. See [VERIFYING.md](VERIFYING.md) for the planned download and
verification paths. Current commands are listed in the
[shipped CLI surface](docs/vision.md#shipped-cli-surface).

Prerequisites: [elan](https://github.com/leanprover/elan) (installs the
pinned Lean toolchain automatically), a C compiler, and `git` (needed at
build time and at runtime).

```sh
git clone https://github.com/DmitryKorolev/tl && cd tl
lake exe cache get   # prefetch the Mathlib proof cache (used by a few proof modules)
lake build --wfail   # builds the binary and checks every stated theorem warning-free
lake build tlverify --wfail
lake exe tlverify    # checks the compiled trust boundary and source inventory
lake exe tltest      # exercises the outside-TCB shell
.lake/build/bin/tl help
```

`lake build --wfail` verifies the stated theorems; `tlverify` additionally
rejects new axioms, forbidden transitive dependencies, incomplete source
scopes, and failed independent kernel replay. Both are required evidence.
`tl` builds
where the Lean toolchain runs (macOS, Linux, WSL2 on Windows); the intended
distribution matrix is
[ADR-0006](docs/adr/ADR-0006-distribution-and-platforms.md).

## Limitations

- **A claim is not a lock.** `tl` is serverless, so two agents on different
  clones can each claim the same locally-ready item until a sync reconciles
  them. Last-writer-wins picks one; the other is told its claim was
  superseded. Disconnected agents can briefly duplicate work — they can
  never corrupt state.
- **Sharing is sync-bounded.** A teammate on another clone sees your tasks
  after you sync and they sync (same-machine worktrees are absorbed on
  read, without an explicit sync).
- **`.tl/` belongs on a local disk.** The write path needs working advisory
  locks and atomic appends, and needs to be the only thing touching those
  files. A network share (NFS/SMB, or a Windows drive from WSL), a FUSE mount,
  or a folder driven by Dropbox/iCloud/OneDrive gives up one or both — you can
  lose a recent write or duplicate a replica identity. `tl` does not check for
  this; share by pushing to a remote instead, or point `--dir`/`TL_DIR` at a
  local path.
- **Acyclicity is reported, not enforced.** A CRDT merge cannot reject a
  write, so two locally-legal edits can form a dependency cycle. `ready`
  stays total and correct on cyclic graphs, and `tl dep cycles` reports the
  cycles to break.
- **It is a repo's task list, not a reporting platform.** Designed for
  thousands of issues per repo; no rich queries, no web UI, no free-text
  search (use `--json` and grep).

## Documentation

- [docs/vision.md](docs/vision.md) — what `tl` is: scope, the full command
  surface, architecture
- [docs/overview.md](docs/overview.md) — the claim table: proved vs tested
  vs trusted, theorem by theorem
- [docs/adr/](docs/adr/) — the design decisions and their rationale
- [AGENTS.md](AGENTS.md) — the guide for building `tl` itself
- [.agents/skills/tl/SKILL.md](.agents/skills/tl/SKILL.md) — the usage guide
  for agents tracking work with `tl`

## License

Apache-2.0 ([LICENSE](LICENSE)). The compiled binary statically links the
Lean runtime and GMP (LGPLv3); the notices that travel with a distribution
artifact are in [THIRD-PARTY-LICENSES](THIRD-PARTY-LICENSES), and
`tl licenses` prints them. Boundary details:
[ADR-0006](docs/adr/ADR-0006-distribution-and-platforms.md#licensing-boundary-gmp--lgpl).
