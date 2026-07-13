# ADR-0001 — Append-only op-log on a dedicated git ref

- Status: Accepted
- Date: 2026-06-04

## Context

`tl` must support concurrent edits from multiple agents/replicas and merge
them without conflicts or lost updates (the CRDT requirement). It must sync
through an ordinary git repository — agents already work in git checkouts —
and it must not require a database daemon (a server is out of scope,
vision). And because the primary audience is autonomous agents coordinating
*through* the tracker, publishing a change must be decoupled from committing
code: an agent that claims a task and then works for minutes before
committing must not leave its claim invisible to others.

The naive design stores materialized state in a file and merges files on
conflict — making every concurrent edit a git merge conflict, and making the
stored artifact the thing we must prove correct. We reject that. The question
this ADR answers is where task state lives and how it is transported.

## Decision

### 1. Append-only op-log; state is a pure fold

- Each operation (`create`, `dep add`, `update`, `close`, …) is one immutable,
  timestamped log entry (the on-disk record schema is ADR-0008).
- Each replica appends only to its own segment (`.tl/log/<replica-id>.jsonl`).
  No replica rewrites another's segment or rewrites history — with one pinned,
  not-yet-built exception: an explicit destructive `tl compact` publishes
  trimmed segment blobs and trims its own segment under the mutation lock
  (ADR-0008's pinned compaction design).
- Materialized state is `fold apply ∅ allOps`, where `allOps` is the multiset
  of entries across all segments. The fold is what the verified kernel reasons
  about (ADR-0004); the only correctness obligation transport imposes is that
  the fold not depend on the order or multiplicity of operations — exactly the
  permutation/duplicate-insensitivity proved in ADR-0004.
- Materialization is `snapshot ⊕ fold(tails)` on each command — the shipped
  content-keyed fold cache (ADR-0022) folds only each segment's appended
  suffix, rebuilding from the segments on any other divergence.
- Clocks and ids are data. Each op's HLC, replica-id, and nonce (ADR-0007)
  are minted by the tested I/O shell at write time and frozen into the entry;
  the fold reads no clock or RNG, so the kernel stays a deterministic pure
  function (which is what keeps the convergence proof clean — ADR-0004).
  (Serialization itself is also outside the proof, covered by round-trip tests
  in the tested shell — ADR-0004/0008.)

### 2. Task state lives on a dedicated git ref (`refs/tl/log`)

Task state is stored on a dedicated ref, `refs/tl/log` — never the working
branch. `tl` updates it via git *plumbing* (`hash-object`/`mktree`/
`commit-tree`/`update-ref`); it never touches the user's index, working branch,
or `HEAD`, and authors no commit on any user-visible branch. Publishing
task state is thus fully decoupled from code commits, and is branch-independent
(switching or merging code branches does not change task state — the behavior a
tracker wants).

In-ref encoding (decided, built in `Tl/Sync/Ref`): the ref commit's tree
holds one blob per replica named `<replica-id>.jsonl` at the root — the
segment blobs *are* the `.tl/log/` contents, no prefix. The tree may also
carry reserved non-replica-named entries (the compaction snapshot,
ADR-0008), under the pinned transport rule: a sync carries any tree entry it
does not recognize into the next commit verbatim, never materializing it
locally — transport-level preserve-unknown (built in `Tl/Sync/Ref`;
semantics pinned in ADR-0008).
Commits are **parent-chained** (each
push's commit parents the prior tip), so a non-fast-forward push is
detectable (§5) and the ref carries history. The author/committer is a
**fixed neutral `tl <tl@localhost>`** set via `GIT_*` env, never the user's
git identity: the acting actor already rides each op's envelope as provenance
(ADR-0013), so the ref's commit metadata needs none and leaks none. The
message is a fixed `tl log`. `update-ref` is compare-and-set against the tip
the merge was based on, so a concurrent writer is never clobbered (§5's
push-rejection retry builds on this).

### 3. The `.tl/` layout (entirely gitignored)

```
.tl/
  log/<replica-id>.jsonl   this replica's append-only segment (authoritative);
                           plus read-only copies of other replicas' segments,
                           refreshed on sync
  local/                   replica-id, HLC clock, caches (ADR-0007)
  README.md                generated agent/human primer — local only (ADR-0011)
  .gitignore               contains `*` — self-ignores the whole `.tl/`
```

`tl init` writes `.tl/.gitignore = *`, so the whole directory is self-ignored
— `tl` never modifies the repo's own root `.gitignore` or `.gitattributes`. The
only thing `tl` ever commits is, optionally, a one-line discovery pointer in a
root agent file (ADR-0011). The replica-id and clock are per-working-copy and
must never be shared (sharing a replica-id breaks the LWW total order and
segment ownership, ADR-0007), which the `*` self-ignore enforces.

### 4. `tl init`

`tl init` creates `.tl/`, writes the `*` self-ignore, mints the replica-id and
seeds the clock (ADR-0007), and generates the local `.tl/README.md`. When a git
repo is present, it offers (opt-in, each removable — all suppressed under
`--stealth`, §7): the discovery pointer (ADR-0011) and auto-sync (below).
`tl sync` fetches `refs/tl/log` explicitly each run — no persistent fetch
refspec is configured. There are no git
lifecycle hooks — task state
never rides the user's commits. `init` is idempotent and does not require a
git repo; outside one it warns that state is local-only until used under a git
repo with a remote (sharing the ref needs git). Placement: inside a git repo,
`init` creates `.tl/` at the enclosing repository's toplevel regardless of the
invoking subdirectory — matching the ADR-0012 discovery boundary, so a
subdirectory invocation can never mint the unsupported nested-`.tl` layout;
outside any repo it uses the cwd; `--dir` overrides both (ADR-0012). Toplevel
placement lands with the Stage-1 discovery wiring (ADR-0012); the Stage-0
minimal `init` is cwd-relative.

Staging (vision §Staged implementation). `tl init` grows across stages — it
does not ship whole in Stage 0: the Stage 0 core is local (create `.tl/`,
write the `*` self-ignore, mint the replica-id, seed the clock); the generated
`.tl/README.md` and the discovery-pointer offer are
Stage 2 (the agent surface, ADR-0011); auto-sync is part of the Stage-3 sharing
surface. `init` configures no persistent `+refs/tl/log:refs/tl/log` fetch
refspec — `tl sync` fetches the ref explicitly.

Repo discovery — how a command run in a subdirectory *finds* `.tl/` — is
ADR-0012.

### 5. Sync (the transport)

`tl sync` = `git fetch refs/tl/log` → union-merge → `git push refs/tl/log`.
The merge is the CRDT join: per-replica segments are append-only, so reconciling
two `refs/tl/log` is a per-segment complete-line set union — different
replicas' files are taken whole, and a *same-named* segment (the
duplicate-replica-id corner case — a filesystem copy, ADR-0007) is merged as the
set union of its lines
across both copies, so no op is dropped even if the two diverged. ("Keep the
longer file" is only a valid shortcut when one is a prefix of the other — the
common case — not the general rule.) It is a trivial, total operation `tl`
performs in the tested shell. It is line-granular (never tears a
line); reordered or dropped-byte-identical lines are absorbed by the fold's
order/duplicate-insensitivity (ADR-0004). Under the pinned, not-yet-built
transport rule (§2 above, ADR-0008): a *reserved* non-replica entry a
new-format binary recognizes (the compaction snapshot) rides the same
line-union — two concurrent writers both survive — while an *unknown* entry
passes through verbatim, untouched. This is the *only* merge `tl` does —
the lattice join a CRDT tool is meant to own, not a conflict-resolution driver.

Because a push touches only `refs/tl/log`, it is safe to automate (no
WIP-code leak, no branch litter):
- `tl init` offers opt-in auto-sync — publish the ref after a mutation
  (best-effort, async).
- `tl claim --sync` publishes the ref around the take (fetch→claim→push).
  `claim <id> --verify` is an explicit preflight: after any reachable fetch
  / local leg, it re-checks that `<id>` is still in `ready s now` before writing.
  If the existing item is not ready — already claimed / in progress, blocked,
  deferred, an epic, or closed — the command writes nothing and returns the
  structured `not-claimable` error (ADR-0003/0008/0013) with actionable reasons.
  A nonexistent id remains the ordinary `not-found` error.
  If no upstream exists, there is no remote state to verify against; `--verify`
  does not fail for that reason, but emits a warning that the preflight is
  local-only (and in `--json`, the warning goes to stderr under ADR-0008's stream
  rules). `--sync` itself still owns `no-upstream` / `stealth-mode` behavior.
- The remote is the branch's configured upstream remote if set, else
  `origin`, overridable by a `tl.remote` git config; the push refspec is
  `refs/tl/log:refs/tl/log`. A non-fast-forward push re-fetches, re-merges, and
  retries once, then reports `push-rejected` (ADR-0008); if no such remote
  exists — including local-only state initialized outside a git repo — it
  reports `no-upstream`.
- Local-first (same-machine worktrees). `tl sync` first runs a local leg —
  reconcile against the local `refs/tl/log`, which linked worktrees of one repo
  share via the common `.git` — *before* the remote leg above. `no-upstream` gates
  only the remote leg, so worktrees on one machine share with zero network;
  reads pick up a moved ref via a cheap OID check (§6). Full model and
  alternatives: [ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md).

Cross-clone, a claim is sync-bounded: it reaches other clones only after the
ref is pushed and they fetch. Two agents on different clones can each claim the
same locally-ready item until a sync reconciles them — LWW picks a winner, the
loser is told ("superseded", ADR-0013). This is the honest cost of a server-less design;
instant global visibility would need the excluded daemon. The deterministic
`ready` order and auto-sync minimise wasted duplicate starts.

**Built form (the remote leg).** Implemented as `Tl/Sync/Remote.lean`
(`syncRemote`), run by `tl sync` after the local leg. Resolution: `tl.remote`
git config wins; else the current branch's upstream remote
(`branch.<b>.remote`); else `origin`; a **detached HEAD** (no current branch)
has no branch-upstream and so falls through to `origin` (or `tl.remote` if set)
— and a resolved name without a configured URL is `no-upstream`. The leg
fetches the remote's `refs/tl/log` into a scratch ref (`ls-remote` first, so a
remote with no tl log yet is the empty case), unions it with the local ref, and
builds one merge commit whose parents are **both** the local tip and the
fetched-remote tip — so it descends from the remote tip and the push
fast-forwards. The same commit is CAS-`update-ref`'d locally (so the local ref
gains the remote's content and a future sync agrees) before the push. A
non-fast-forward rejection (another clone pushed between our fetch and push)
re-fetches, re-unions and retries **once**, then surfaces `push-rejected`
(exit 10); a real auth/network failure is distinguished from a rejection and
thrown as-is rather than misreported. `no-upstream` is **reported, not fatal**
for plain `tl sync` — the local leg is the success on a remote-less worktree
(ADR-0016 §1); the exit-11 error is reserved for flows that *require* a remote.
The `--json` `data` is `{ local: {…}, remote: {ran, remote, pushed, pulled,
tip} | {ran:false, reason:"no-upstream"} | null }` (null = not a git repo).

### 6. The local/ref invariant

A mutation appends to this replica's own segment file (`O_APPEND`) and
nothing else — that file is the append-only authority for this replica's ops,
and `tl sync` only ever reads it, never rewrites it. Reads fold the on-disk
segment files, so a just-made local mutation is visible to the next read
immediately, before any sync. A read also does an O(1) check of the shared
`refs/tl/log` OID and, if it moved (e.g. a sibling worktree synced), incrementally
materializes the changed foreign segments before folding — live cross-worktree
visibility without putting git on the steady-state read path
([ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md); ADR-0015 §5). `tl sync` fetches `refs/tl/log`, unions all
segments, and pushes a candidate ref; locally it writes back only the other
replicas' segments — read-only caches for folding — via an atomic temp-file +
`rename`, never its own. Files are the local source of truth; the ref is the
transport. Single-machine write concurrency is serialized by a per-working-copy
mutation lock around the mint-HLC→append critical section, with atomic
`O_APPEND` as the second line of defence (ADR-0015 §1–2).

There is **no push-time re-snapshot**: the remote leg pushes the union of the
*local ref* and the fetched-remote tip without re-reading the own on-disk
segment at push time. Nothing is lost — ops appended to the own segment during
a sync are simply not in *this* push; they are already folded by local reads
and ride the next sync. A push races only with another *clone's* push (handled
by the non-fast-forward re-fetch/retry), never with a local append, so a
push-time re-snapshot under the mutation lock would buy nothing the next-sync
convergence does not already provide.

### 7. Stealth mode (`tl init --stealth`) — opt-in

Sharing is the default; `--stealth` is an explicit opt-in, never automatic. It
is the sole spelling — no `--local` alias (the word "local" already names the
shared local ref and `.tl/local/`), and no environment-variable form, since an
env default would silently create untracked private state (decided 2026-06-21). In the dedicated-ref model normal mode is already
branch-stealthy — `.tl/` is gitignored, nothing is committed to the working
branch, and sync touches only `refs/tl/log` — so `--stealth` no longer means
"avoid dirtying commits." It means local-only task state with zero
repo-visible trace: a single local replica that is never shared. Concretely,
`tl init --stealth`:

- creates `.tl/`, self-ignores it (`.tl/.gitignore = *`), mints the replica-id,
  seeds the clock, and appends/reads the local `.tl/log/<replica-id>.jsonl` — the
  CRDT still works, degenerating to a trivial single-replica fold (the kernel is
  unchanged); but
- does not configure the `refs/tl/log` refspec, not push or fetch, and
  not offer auto-sync; and
- does not offer the committed discovery pointer (ADR-0011) — the one thing
  that would leave a *committed, repo-visible* breadcrumb, and stealth's whole
  point is to leave none.

`tl sync` in a stealth repo fails with the `stealth-mode` error (ADR-0008)
explaining how to un-stealth, rather than silently no-op'ing. Un-stealthing
needs no data migration: configure the `+refs/tl/log:refs/tl/log` refspec,
snapshot the local `.tl/log/*` segments into `refs/tl/log`, and `tl sync` — same
format, same ids, no conversion. Use stealth for a repo you can't or won't share
into (one you don't own, a personal overlay, an isolated test run — pair with
`--dir`, ADR-0012).

## Consequences

- No "forgot to commit," no WIP leak. Publishing is decoupled from code
  commits, so a claim no longer waits on a code commit to become shareable;
  it reaches other clones on `sync` / `--sync` / auto-sync (until then it is
  local — by design, there is no server). And `--sync`/auto-sync push only the
  ref, so they never leak unpushed code or litter history.
- Several requirements are *obviated*, not merely moved. There is no
  `.gitattributes` `merge=union`/`-text` requirement (git never EOL-normalizes
  or 3-way-merges the log — it lives in `refs/tl/log` and gitignored files), no
  pre-commit/post-merge hooks, and the history-rewrite hazard (rebase/force-push
  dropping ops) is moot because the log is not in the user's commits.
- `tl` performs one trivial merge (the segment union on sync) — the lattice
  join, total and tested, covered by the same convergence theorem (ADR-0004).
- The log is not browsable in the working tree. Humans read it via `tl log`
  / `tl show` (or `git log refs/tl/log`). `tl sync` is the *real* transport, not
  "sugar over git."
- Duplicate delivery is harmless (the fold's duplicate-insensitivity), so
  the union may re-deliver a line with no effect.
- The log grows without bound, but read cost does not: the non-destructive
  snapshot — the content-keyed fold cache (ADR-0022), which retains every op — folds
  only appended suffixes. Destructive GC, the only thing that would bound on-disk
  size by discarding settled ops, is deferred to ADR-0008 (which reserves the
  `snapshot` record and version-vector frontier for it).

## Alternatives considered

- Branch-tracked log files + a pre-commit hook (the earlier design).
  Stored the segments as ordinary tracked files on the working branch, committed
  by piggybacking on the user's commits. Rejected: publishing couples to a code
  commit (an agent's claim stays invisible until it commits — "forgot to
  commit"), and the only way to publish sooner (`git push`) pushes the whole
  branch, leaking unpushed WIP and littering history with per-claim commits.
  Branch-tracked files also required a `merge=union`/`-text` `.gitattributes`
  rule (a silent-corruption hazard if a clone predated it) and were
  branch-scoped (task state forked per code branch). The dedicated ref removes
  all of this.
- Materialized state + a custom git merge driver. Rejected: a merge driver
  is unverified code on the critical path and reintroduces the conflict
  semantics we make unrepresentable.
- A daemon / SQL server (e.g. dolt). Rejected (vision): instant global
  visibility is what a server buys and what the project excludes; a daemon
  contradicts "small," and an opaque merge defeats the proof.
- An orphan branch (`refs/heads/tl-state`). Equivalent in substance; a
  non-head `refs/tl/log` is preferred so it never shows in `git branch`, is
  never accidentally checked out, and reads as `tl`-owned plumbing.
- Push on every mutation, synchronously. Rejected as the default: a network
  round-trip per op is slow and needs connectivity. The local segment is
  updated per mutation; `refs/tl/log` is (re)built from the segments at `tl sync`
  / opt-in auto-sync time (§6), never per-mutation.
- Op-log with a single shared segment (global total order). Rejected:
  reintroduces write contention and ordering conflicts; per-replica segments +
  an order-insensitive fold is what makes the union conflict-free.
