# Advanced `tl` workflows

Read this when the core [skill](../SKILL.md) points to a workflow here.
Use `tl help --json` for the exact grammar supported by the installed binary.
Pass `--json` to commands below.

## Claims and dependencies

- `tl ready` ranks open, unblocked, non-epic, non-deferred tasks. Its default
  result is capped at 50; `--limit 0` shows all. Re-run it after a context
  reset rather than relying on remembered task IDs. Use `--label` to narrow a
  lane; `tl list --assignee <name>` finds live claims.
- `tl claim <id>` accepts only a still-ready item. On `not-claimable`, inspect
  `error.reasons` and move to another ready item or use `tl why <id>` for
  transitive blockers. On success, check `claim.outcome`: `won` permits work;
  `superseded` does not.
- To take over someone else's stale claim, use
  `tl claim <id> --steal --stale <duration>` (for example, `1h`). There is no
  default stale window. A concurrent steal can still supersede your claim.
  For directed work already in progress, inspect `tl show <id>` and its
  assignee before claiming or continuing; do not take another actor's live
  claim.
- `tl why <id>` explains dependencies and unfinished epic children;
  `tl unblocks <id>` previews what closing would free. `tl dep critical` ranks
  open issues by the number they transitively block. `tl dep cycles` reports
  cycles that a merge may introduce; inspect `tl dep path <from> <to>` before
  removing an edge.

## Creating and shaping work

Use `tl create "<title>" --description "<what, why, and relevant files>"`.
Priorities are `0` through `4` (`0` is highest, default `2`). Find the relevant
epic before creating work and use `--parent <epic>` where one owns the area.
Use `--related <current-id>` for new scope discovered while doing another task.

Useful verbs:

```text
tl update <id> [--title T] [-p N] [--description D] [--slug S]
tl note add <id> "<text>"
tl label add <id> <label>          # label remove/list also exist
tl dep add <A> <B>                 # A becomes blocked by B
tl dep remove <A> <B>
tl dep relate <A> <B>              # informational link; dep unrelate removes it
tl parent set <id> <epic>          # replaces the current parent
tl parent remove <id> <parent>
tl defer <id> --until <date>       # or --for <duration>; undefer resumes now
```

`tl update <id> --description -` reads a replacement body from stdin; without
that flag the description is unchanged. `tl note add <id> -` reads a note from
stdin. Notes are immutable. An epic derives `done` from its children; do not
manually close it `--as done`. `tl defer` postpones the same task; create a
linked task for separate work you are leaving behind. When closing a duplicate,
pass `--of <canonical-id>`.

## Sharing and claim races

Each working copy keeps its own `.tl/` replica. The shared Git ref is
`refs/tl/log`. A read absorbs changes already published to that *local* ref
by linked worktrees. When `tl.autosync` is enabled (normally for linked
worktrees), writes best-effort publish to the local ref. Failure is reported
in top-level `notes`, and the write itself remains durable.

`tl sync` publishes to the local ref, then, if a remote is configured, fetches,
unions, and pushes the task ref. A command's `--sync` option uses that same
remote reconciliation before the command and degrades to a `notes` disclosure
if the remote is unavailable. `tl claim --verify` also reconciles remotely;
it refuses with `verify-failed` if a configured remote cannot be reached. Its
preflight can publish pending state, but the new claim is not guaranteed to be
shared without `--sync` or a later authorized sync.
**All three can publish to a remote**, so use them only when remote task-log
publication is authorized. A `notes` prompt to run `tl sync` reports local
state; it is not authorization. Before an authorized sync, inspect every
effective push URL with `git remote get-url --push --all <remote>`; Git URL
rewrites can change the destination.

`tl sync --json` reports the local and remote legs separately. Cross-clone
visibility is sync-bounded: two agents can claim the same item before their
logs reconcile. After reconciliation, last-writer-wins selects one claim. On
`tl show`, `claim.outcome` may also be `ended`, meaning your own later close or
reopen ended the claim; `superseded` still means another writer now holds it.

An ID resolves by an unambiguous `tl-`-prefixed prefix; a bare token is a
slug. On writes, `--actor` or `TL_ACTOR` sets provenance; otherwise `tl` uses
Git `user.email` and then `user@host`.
