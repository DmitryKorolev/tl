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
- Bare repositories. A directory that is itself a git repository directory —
  a bare repo, or the inside of a `.git` dir, recognized the way git's own
  setup check does (`objects/` and `refs/` directories plus a `HEAD` file
  whose *content* is a symref or detached hash, so a committed fixture
  directory holding an ordinary file named `HEAD` does not qualify) — bounds
  the walk exactly like a worktree root: ascending past it could bind an
  unrelated enclosing `.tl/`. There is no working tree there to hold state, so
  `tl init` (and `import`'s implicit init) refuses it with a teaching `usage`
  error; a bare repository still serves as a sync *remote* (ADR-0001 §5), and
  `--dir` remains the explicit, never-refused escape hatch. Init's placement
  walk honors the same canonicalized `GIT_CEILING_DIRECTORIES` list as
  discovery; a ceiling that hides the enclosing repo makes init place at the
  cwd, with a note saying the ceiling stopped the repository search. (A linked
  worktree's private gitdir has no `objects/`, so it does not match the
  signature; its boundary stays the `.git` file at the worktree root.)

### Sanitized git subprocess environment

Discovery is *filesystem* discovery: the walk above selects the repository,
and every git subprocess is addressed at it explicitly (`git -C <root>`).
git, however, honors ambient routing variables that would override that
addressing — an inherited `GIT_DIR` from a shell, IDE, or automation wrapper
(git itself exports `GIT_DIR` into hooks) would silently point every
subprocess at a *different* repository, making `tl sync` publish one repo's
task data into another, absorb the other way, or report misleading health.
That is the same wrong-repo failure the discovery boundary exists to prevent,
so the subprocess boundary enforces it too:

**Invariant (scoped — read the scope, it is load-bearing).** Once discovery
(or `--dir`/`TL_DIR`) selects a repository, no variable *in the scrub set
below* can redirect a `tl`-spawned git process to another repository,
worktree, object database, index, namespace, or remote configuration.

The invariant is deliberately **not** the absolute "no inherited environment
may redirect `tl`". That stronger claim is false and cannot be made true: git
resolves credentials, transports, and its own configuration through
variables (`HOME` above all) that `tl` cannot unset without breaking every
authenticated remote. The honest statement is the scoped one, plus the
carried residual recorded in Consequences below. An earlier draft of this
ADR asserted the absolute form while preserving `XDG_CONFIG_HOME`; a crafted
`$XDG_CONFIG_HOME/git/config` then redirected a `tl sync` push to another
repository while the command reported success — the exact failure the
invariant claimed to exclude.

**Mechanism.** Every subprocess spawn goes through one runner
(`runBounded`, `Tl/Sync/Ref.lean`), which unsets the scrub set
(`scrubbedGitVars` — the code is the normative list, pinned by tests) on
every spawn, timeout-configuration reads and the actor `user.email` fallback
included:

- repository/worktree/object-store/index/namespace routing: `GIT_DIR`,
  `GIT_WORK_TREE`, `GIT_COMMON_DIR`, `GIT_OBJECT_DIRECTORY`,
  `GIT_ALTERNATE_OBJECT_DIRECTORIES`, `GIT_INDEX_FILE`, `GIT_NAMESPACE`;
- object-graph / fetch-state routing: `GIT_GRAFT_FILE`, `GIT_SHALLOW_FILE`,
  `GIT_REPLACE_REF_BASE`;
- per-invocation config injection (can rewrite `remote.<n>.url`,
  `url.*.insteadOf`, or `tl.*` keys): `GIT_CONFIG` (the `git config`
  builtin's file redirect — every `tl` config read is that builtin),
  `GIT_CONFIG_COUNT` (unsetting it makes git ignore the unbounded
  `GIT_CONFIG_KEY_*`/`GIT_CONFIG_VALUE_*` families, which git consults only
  under a valid count — the one family a name-list cannot enumerate),
  `GIT_CONFIG_PARAMETERS` (the `git -c` internal channel),
  `GIT_CONFIG_SYSTEM`, `GIT_CONFIG_GLOBAL`;
- config *relocation*: `XDG_CONFIG_HOME`, whose `git/config` is one of git's
  global config files. Scrubbing `GIT_CONFIG_GLOBAL` but not this one closes
  nothing — the same `url.*.insteadOf` redirect arrives by the other
  spelling. Unsetting it falls back to `$HOME/.config`, so `~/.gitconfig`,
  `~/.git-credentials`, and `~/.ssh` (all `HOME`-relative) keep working.

**The scrub set is bounded by cost, and the guarantee is bounded with it.** A
variable is scrubbed when unsetting it restores git's default,
credential-preserving behavior. It is preserved when unsetting it would strip
the invoking user's own credentials or transport: `HOME`, credential and
transport variables (`GIT_SSH*`, `GIT_ASKPASS`, `GIT_TERMINAL_PROMPT`,
`SSH_AUTH_SOCK`, proxies), and which-git-runs (`PATH`, `GIT_EXEC_PATH` — the
git binary is already trusted byte-transport, ADR-0006/ADR-0014). Preserved
does **not** mean harmless: see the `HOME` residual in Consequences.
`GIT_CEILING_DIRECTORIES` is preserved *and* non-redirecting — it can stop a
walk, never redirect one, and `tl`'s own walks honor it, applying it like git
to proper ancestors only (with state at the repo toplevel the gitdir is
immediately present and a ceiling is inert; with a subdir state root — the
`--dir` shape — an ancestor ceiling can make git classify the location as
repo-less, a fail-stop to `no-upstream`/degraded behavior, never a redirect).
Per-call additions (the fixed ref-commit identity, ADR-0001) compose after
the scrub, and may deliberately re-set a scrubbed variable.

`tl doctor` reports what this policy does not prevent, rather than hiding it.
The `gitRouting` check (a) lists any inherited scrub-set variables — present
but ignored by `tl`, though plain `git` in the same shell binds elsewhere;
(b) compares filesystem discovery with git's own classification, warning when
the state directory is not at the toplevel of the repository it shares
through; (c) compares each remote's raw push target (`remote.<n>.pushurl`,
else `.url` — so a deliberately configured distinct push URL is not flagged)
with the URL git will actually push to (`remote get-url --push`, which applies
both `url.*.insteadOf` and the push-only `url.*.pushInsteadOf` without
contacting the remote), reporting when a rewrite is in force; and (d) reports
each push-*destination* key — `tl.remote`, and the resolved remote's `url` /
`pushurl` — whose effective value is supplied by the global scope
(`~/.gitconfig`) rather than repo-local config, catching the case where the
remote *selection or its URL* is injected wholesale with no rewrite at all (a
rewrite-only check reports `ok` while the push follows the injected remote).
(c) and (d) are the two faces of the `HOME` residual — the difference between
a silent misdirected push and a reported one. All warn and teach; none fails
health.

## Consequences

- Commands work from any subdirectory, with the same boundary rule git
  itself uses for repositories — and never bind state in the wrong repo.
- `--dir`/`TL_DIR` give the test suite cheap, isolated, side-effect-free
  state — a temp dir, no repo, no walk-up — composing with `--stealth`.
- No-`.tl` is a hard error, not an auto-init, so commands never fabricate
  state in the wrong place; `import` is the single, explicit exception.
- The selected repository is immune to the *scrubbed* part of the caller's git
  environment: hooks, IDE terminals, and wrapper scripts can run `tl` without
  their `GIT_DIR`-style routing leaking into it, and a `GIT_CONFIG_*` /
  `XDG_CONFIG_HOME` injection cannot rewrite where `tl` pushes. The cost is
  that a deliberate `GIT_DIR`-driven workflow (a detached-gitdir setup) is not
  honored — `--dir`/`TL_DIR` are `tl`'s explicit spellings for "state lives
  elsewhere."

- **Carried residual: `HOME` can still redirect a push.** `tl` preserves
  `HOME` because it locates `~/.gitconfig`, `~/.git-credentials`, and
  `~/.ssh`; unsetting it would break every authenticated remote. A `HOME`
  pointed at a directory the user does not control — by an IDE, a task
  runner, a CI image, or an attacker — can carry
  `url.<decoy>.insteadOf = <origin>` in its `.gitconfig`, and `tl sync` will
  push the task log to the decoy. This needs **no** control of `PATH` and no
  substitution of the git binary; it is not the already-lost tier, and it is
  not claimed to be. `tl` does not prevent it. Two things bound it: `tl
  doctor`'s `gitRouting` row reports when a remote's effective URL differs
  from its configured URL (so the redirect is disclosed rather than silent),
  and the same mechanism means the log is *misplaced*, never lost — the local
  segments are intact and a later sync under a clean environment publishes
  them correctly. Closing it fully would mean scrubbing `HOME` (breaking
  authenticated remotes) or reimplementing git's config resolution inside
  `tl`; neither is warranted. Mirrored in `docs/overview.md` (Trusted) and
  ADR-0014 T7.

- A second recorded cost, the flip side of the same scrub: a config *relocated*
  via `GIT_CONFIG_GLOBAL`/`GIT_CONFIG_SYSTEM`/`XDG_CONFIG_HOME` is invisible to
  `tl`'s git subprocesses — including a `credential.helper` or token-bearing
  `url.*.insteadOf` that lives only there — so `tl sync` can fail or prompt
  against an authenticated remote where plain `git push` in the same shell
  succeeds. The same invisibility applies to the actor fallback: a `user.email`
  that lives only in an `XDG_CONFIG_HOME`-relocated config is not read, so the
  actor provenance chain (`--actor` → `TL_ACTOR` → git `user.email` →
  `<user>@<host>`, ADR-0013) falls through to `<user>@<host>` — a label change,
  not a data-integrity issue, and `TL_ACTOR` or `--actor` is the explicit fix.
  Those variables cannot be preserved: they are exactly the config-injection
  redirect the scrub exists to stop. The supported spellings are the default
  locations (`$HOME/.gitconfig`, `$HOME/.config/git/config`) or repo-local
  config. `tl doctor`'s `gitRouting` row names the inherited variable when the
  push-redirect shape is present.

## Alternatives considered

- Auto-init on first command. Rejected: silently creates a project from a
  wrong cwd; explicit `init` is safer and a one-time cost.
- git's exact `.git` discovery (climb to filesystem root). Rejected: it
  would bind an enclosing repo's `.tl/` and publish to the wrong `refs/tl/log`;
  the repo-boundary stop is the fix.
- A global (home-dir) registry of projects. Rejected: state belongs with the
  repo it describes and travels with git; no machine-global registry needed.
- Honoring `GIT_DIR`/`GIT_WORK_TREE` the way git itself does. Rejected: `tl`
  selects state by filesystem discovery, so honoring the routing environment
  on top creates two sources of truth that can silently disagree — reads from
  one repository, publishes into another. The detached-gitdir use case those
  variables serve is covered by the explicit `--dir`/`TL_DIR` override.
- Spawning git with a fully cleared environment (`inheritEnv := false`).
  Rejected: it would strip credentials, SSH agents, proxies, and `PATH`
  itself — breaking every authenticated remote — to close a hole the
  targeted scrub closes precisely.
- Scrubbing `HOME` too (closing the residual above). Rejected: `HOME` is where
  git finds `~/.gitconfig`, `~/.git-credentials`, and `~/.ssh`, so unsetting it
  breaks authenticated push/fetch for ordinary users — a certain, universal
  cost paid against a conditional, environment-specific redirect. Disclosure
  (`doctor`'s `gitRouting` rewrite check) is the proportionate answer; if a
  deployment needs the stronger guarantee, it can run `tl` under a `HOME` it
  controls.
- Resolving the remote URL ourselves and pushing the literal URL to bypass
  `insteadOf`. Rejected: git applies `url.*.insteadOf` to command-line URLs
  too, so this does not bypass the rewrite; neutralizing it would mean
  injecting config on every call (the very channel the scrub removes) and
  enumerating an unbounded key family.
