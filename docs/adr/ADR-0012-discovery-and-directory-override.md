# ADR-0012 — Repo discovery and the directory override

- Status: Accepted
- Date: 2026-06-04

## Context

A `tl` command run from anywhere under a project must find the project's
`.tl/` reliably, and test/CI harnesses must be able to point `tl` at an explicit
state directory with no walk-up. The `.tl/` layout, what `tl init` writes, sync,
and stealth are ADR-0001; this ADR owns only *how state is located* — a distinct
concern an implementer could change without touching storage.

## Decision

### Directory override (`TL_DIR` / `--dir`)

`TL_DIR=<path>` (env) or `--dir <path>` (flag, which wins) points `tl` at
an explicit `.tl` state directory and skips discovery. It is not the
project root; callers that want a temp isolated state pass the temp `.tl` path
itself. This is what isolated test harnesses and ephemeral/CI runs want — a temp
dir, no repo, no walk-up. It composes with `--stealth` (override *and*
unshared, ADR-0001) or stands alone.

If the override path does not exist, or exists but is not an initialized `.tl`
state directory, ordinary commands fail with `no-project` (exit 3); they do
not auto-init. `tl init --dir <path>` creates that state directory explicitly,
and `tl import --dir <path>` may do its documented implicit init exception
(ADR-0005). An empty directory passed to ordinary commands is therefore not a
fresh project; it is a `no-project` error.

### Discovery (walk-up, bounded by the repo)

If `--dir`/`TL_DIR` is unset, a command walks up from the cwd to the nearest
ancestor containing `.tl/`. The walk-up stops at a git-repository boundary —
it does not ascend past the enclosing repo's root (the directory whose `.git`
the cwd belongs to) and honors `GIT_CEILING_DIRECTORIES`. This is stricter than
git's own `.git` discovery: `tl` must not silently bind a `.tl/` in a
*different, enclosing* repo, because `tl` would then read and publish the
wrong repo's `refs/tl/log` (ADR-0001). If the nearest `.tl/` is outside the
cwd's own repository, `tl` treats it as not found rather than crossing the
boundary. When the cwd is in no git repo at all (init/import are allowed
there), there is no boundary to stop at, so the walk-up stops at the first
`.tl/` found and, finding none up to `GIT_CEILING_DIRECTORIES`/the filesystem
root, hard-errors rather than binding an unrelated ancestor `.tl/`.

- No `.tl` found: commands error ("no tl project here; run `tl init`")
  with a nonzero exit — they do not auto-init. Auto-creating state from a
  mistyped path is the silent surprise the project avoids. `tl import` is the
  one exception — it may implicitly `init`, because the user explicitly asked
  to seed a repo (ADR-0005).
- Replica-id absent but state present (a byte-copied `.tl/` or a damaged
  `local/` — note a fresh *clone* starts with no `.tl/` at all, since the whole
  directory is gitignored and does not travel): the first write auto-mints a
  new replica-id. A copied working tree *is* a new replica and must have its
  own id (ADR-0007).
- One `.tl` per root. Nested `.tl/` directories are not a supported layout;
  discovery stops at the first found.
- Worktrees and submodules. A linked worktree or a submodule is its own
  repository boundary: discovery stops at its root, so it gets its own `.tl/`
  (or a clear not-found) rather than binding the parent's. A fresh worktree
  starts with no `.tl/` (untracked files are not checked out) and gets its own
  via `init`; a byte-copied `.tl/` self-heals its replica-id on first write, as
  above. Linked worktrees *share*
  state through the common `.git`'s `refs/tl/log` plus local-first sync — no remote
  needed on one machine ([ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md)).

## Consequences

- Commands work from any subdirectory, with the same boundary rule git
  itself uses for repositories — and never bind state in the wrong repo.
- `--dir`/`TL_DIR` give the test suite cheap, isolated, side-effect-free
  state — a temp dir, no repo, no walk-up — composing with `--stealth`.
- No-`.tl` is a hard error, not an auto-init, so commands never fabricate
  state in the wrong place; `import` is the single, explicit exception.

## Alternatives considered

- Auto-init on first command. Rejected: silently creates a project from a
  wrong cwd; explicit `init` is safer and a one-time cost.
- git's exact `.git` discovery (climb to filesystem root). Rejected: it
  would bind an enclosing repo's `.tl/` and publish to the wrong `refs/tl/log`;
  the repo-boundary stop is the fix.
- A global (home-dir) registry of projects. Rejected: state belongs with the
  repo it describes and travels with git; no machine-global registry needed.
