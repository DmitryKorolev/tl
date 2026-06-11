# tl

A small, git-native task tracker for AI agents, with a formally-verified core.

`tl` ("task list") answers the one question a tracker owes an agent — *"what
can I work on right now, and is the dependency graph sane?"* — and proves
that answer correct. It is deliberately small: the commands that drive an
agent's work loop, and nothing else.

> Status: Stages 0 and 1 are built — the verified kernel (the CRDT join laws
> and the `ready`/cycles/rollup theorems) and the MVP work loop: the
> record↔Op codec, the store (discovery, segments, the locked write path),
> clock/id wiring, and the stage-1 CLI verbs (`init`, `create`, `ready`,
> `claim`, `close`, `update`, `dep add/remove`, `why`, `dep cycles`, `show`,
> `list`, `doctor`, `version`, plus `help`) with `--json` everywhere. Stage 2 (ergonomics)
> and Stage 3 (import + the `refs/tl/log` sync transport) are next; see
> [docs/vision.md](docs/vision.md) §Staged implementation. Install
> instructions below describe the full intended tool and are marked
> *planned*; build from source with `lake build` meanwhile.

## Why

- Verified core. The dependency graph, the ready-work computation, cycle
  detection, and epic rollup are proved correct in Lean 4 — not just tested
  (the honest claim table — proved vs tested vs trusted, including the tracked
  residuals — is [docs/overview.md](docs/overview.md)).
- Git-native, conflict-free. State is an append-only op-log; git
  transports it and a CRDT fold reconciles it, so concurrent agents merge
  without conflicts or lost updates — no server, no database daemon.
- Small where it counts. The *verified kernel* is tiny — seven op-deltas and
  a handful of theorems; on top sits a conventional tracker CLI (a work-loop core
  plus dependency and visibility commands). "Small" describes the proved core, not
  a thin feature set.

## Why not just …

| Instead of… | The pain it leaves | What `tl` does |
|---|---|---|
| a markdown TODO | no dependency graph, no "what's ready," and two agents editing it conflict in git | dependency-aware `ready`, and a CRDT that merges concurrent edits without conflicts or lost ops |
| GitHub Issues | a server/API, auth, rate limits, network round-trips; lives outside the repo and the agent's git workflow | local, serverless, git-native — state travels with the repo on its own ref, no daemon |
| beads | the closest peer, but a dolt/SQL server underneath and no verified core | import your beads data one-shot, then a serverless file format with a proved kernel ([how](docs/adr/ADR-0005-import-from-beads.md)) |
| the agent's own context | task state evaporates on compaction/clear; no cross-session or cross-agent sharing | durable, shared task state with a stable `tl ready` an agent re-reads on waking |

Honestly: `tl` earns its keep only if you need the dependency-aware *"what can I
work on"* loop across sessions or agents. For a handful of independent tasks, a
TODO file is genuinely fine.

## What "verified" covers — and what it doesn't

The word does a lot of work, so here is the boundary up front:

- Proved (the kernel). Concurrent edits always converge to the same state
  with no lost ops (the CRDT fold is order- and duplicate-insensitive), and the
  answers an agent relies on — `ready`, cycle detection, epic rollup — are correct
  *and total*, even on the cyclic or dangling graphs a merge can produce. These
  are Lean theorems, not tests.
- Not proved — tested or trusted (everything else). The CLI, JSON/parsing,
  git transport, and clock are *tested*, not proved. And because `tl` is
  serverless, a claim is not a lock: two agents on different clones can claim
  the same locally-ready item until they sync — last-writer-wins picks the winner
  and the loser is told *"superseded"* (you can do brief duplicate work, but never
  corrupt state). It also rests on a few carried assumptions (unique replica ids, a
  monotonic clock, git moving bytes faithfully).

So "verified" means the core logic is mathematically proved correct — not
that the whole program is bug-proof, and not that it provides distributed
locking. The full claim-by-claim breakdown (proved / tested / trusted) is
[docs/overview.md](docs/overview.md).

## How it works (one breath)

State is never stored directly — it is a fold over an append-only log of
operations. Each replica appends to its own log segment, kept on a dedicated git ref
(`refs/tl/log`) that `tl sync` fetches, unions, and pushes — so task state has
its own publish path and never rides (or pollutes) your code commits. A
CRDT (OR-Sets for issues/edges/labels, an LWW-register per scalar field,
and a per-key-LWW metadata map) makes the fold
insensitive to order and duplication. The kernel that folds and answers
queries is the part that's proved.

## Quick start *(planned)*

```sh
tl init               # initialize task state for this repo
tl import .beads      # one-shot migration from an existing beads repo
tl create "Write the parser" --blocked-by tl-a1b2
tl ready --json       # unblocked, ranked candidates — the agent picks one
tl claim tl-9f3c      # take a ready item (LWW; contention is reported)
tl close tl-9f3c --as done
tl why tl-77a1        # why isn't this ready? (transitive unclosed blockers)
tl dep cycles         # report any dependency cycles
```

## Install *(planned)*

Prebuilt binaries via GitHub Releases, a `curl | sh` installer, npm
(`npm i -g`), and a Homebrew tap. Supported: Linux x86-64/aarch64, macOS aarch64
(Apple Silicon), and Windows via WSL2 (the Linux binary — the recommended
Windows path). Best-effort: macOS x86-64 and native Windows x86-64 (shipped
via npm/Release, not in the gating test matrix); FreeBSD via a community port.
`git` is a runtime prerequisite.
See [ADR-0006](docs/adr/ADR-0006-distribution-and-platforms.md).

## Migrating existing data

`tl` can do a one-shot import from an existing
[beads](https://github.com/gastownhall/beads) `.beads` repository and then
owns its own format — a migration, not an ongoing integration. See
[ADR-0005](docs/adr/ADR-0005-import-from-beads.md).

## Documentation

- [docs/vision.md](docs/vision.md) — what tl is, scope, command surface
- [docs/overview.md](docs/overview.md) — proved vs tested vs trusted (claim table)
- [docs/adr/](docs/adr/) — the design decisions and their rationale
- [AGENTS.md](AGENTS.md) — guide for building tl
- [docs/design-backlog.md](docs/design-backlog.md) — design backlog (stage-gated): gaps & decisions to settle, stage by stage

## License

Apache-2.0. The shipped binary links GMP under LGPLv3 (via the Lean runtime).
Details and compliance in
[ADR-0006](docs/adr/ADR-0006-distribution-and-platforms.md#licensing-boundary-gmp--lgpl).
