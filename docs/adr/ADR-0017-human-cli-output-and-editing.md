# ADR-0017 — Human-facing CLI: output format and editing

- Status: Accepted
- Date: 2026-06-05

## Context

`tl`'s machine path is `--json` (ADR-0011), a versioned, stable contract
(ADR-0008). Its human-readable output and its interactive editing flow
were pinned only in `vision.md` prose. This ADR promotes them to their owning
record, so the contract has one home and `vision.md` shrinks to a summary +
pointer (as it already does for `ready` ordering and the JSON projection). It
governs the default (non-`--json`) presentation and the `$EDITOR` path only; the
machine envelope, error codes, and exit statuses are ADR-0008.

## Decision

### 1. One-line issue format

Used by `ready` and flat `list` output:

```
<glyph> <id> <prio> [epic] <title>
```

- `<id>` is the **short** display id: `tl-` + the shortest id prefix unambiguous
  over the present issue set (git-short-hash style; floor 4 chars, extending on
  collision). It is directly usable as a command argument — input resolution
  matches any unambiguous `tl-` prefix over the same set (ADR-0007). Human
  display only: `--json` always carries the full 16-char id (the ADR-0008/0020
  contract), and the prefix length grows as issues are added, so scripts and
  agents must never depend on it. `show` / `why` keep the full id at least once.
- Status glyph: `○ open`  `◐ in_progress`  `● blocked`  `✓ done`
  `✗ cancelled`  `❄ deferred`. `blocked` / `deferred` are the derived views
  (ADR-0003/0010) — the glyph reflects effective state, not just stored status.
- `<prio>` renders as `P0`–`P4`.
- `[epic]` is the only inline kind-marker, shown only for an issue with
  `parent`-children (derived, ADR-0003 — not a stored type). Epics are rare
  and structurally special (excluded from `ready`, they roll up), so they earn the
  slot; most lines carry no marker, so `[epic]` stands out — and its title shifts
  right, a free highlight with no column reserved on the common case. `type:*`
  labels (e.g. `type:bug`) are not rendered inline: they drive nothing and are
  common, so inlining them would drown the signal. See them via `show`, `--json`
  (`labels`), or `list --label type:bug`.
- `<title>` is the only variable-width field; it truncates to the terminal
  width with `…` (untruncated-to-width via `show` / `--json`; field-level
  render bounds per ADR-0014).
- No parent suffix. `ready` is a flat ranked queue (priority →
  critical-path → createdAt → id, ADR-0004) and excludes epics, so a child's epic
  is never adjacent and can't be tree-indented here; the parent is in `--json`
  (the `parent` scalar) and `show`. Hierarchy is the tree view (§2), not an inline
  suffix on the ranked line.

### 2. Tree rendering (hierarchy, incl. nested epics)

Structure — including nested epics (epic → sub-epic → … → task, to arbitrary
depth) — is rendered as an indented tree, never inline on the one-line format.
Used by `list` — the tree is the **default** whole-project browse (amended
2026-06-11: it was the `--tree` opt-in; `--flat` now opts into the one-line
rows instead) — the dependency views `why <id>` (upward blockers) and
`unblocks <id>` (downward dependents), each single-rooted over `blocks` edges
(decided 2026-06-11: these subsume the separate `dep tree` verb, ADR-0003),
and the children block of `show <epic>`:

```
○ tl-ep01 P1 [epic] Parser rewrite
├── ◐ tl-ab12 P1 Lexer
│   └── ○ tl-cd34 P2 Unicode escapes
└── ○ tl-ef56 P2 [epic] Grammar
    └── ● tl-gh78 P1 Pratt parser
```

- Nesting recurses down the `parent` graph; each level is indented with
  `├──` / `└──` / `│` connectors (unicode; `+--` / `\--` / `|` under
  `--glyphs=ascii`). A sub-epic still shows `[epic]` and contains its own subtree.
- Each node uses the one-line format (§1); the title truncates to the width
  remaining after its indent.
- Placement uses the canonical parent (ADR-0003 §4): a multi-parent issue
  appears once, under its deterministically-derived canonical parent; the extra
  parent edge is reported by `doctor` / `dep cycles`, not duplicated in the tree.
- Total on cyclic / dangling `parent` graphs — both merge-reachable. A
  visited-set bounds recursion: a parent cycle renders each node once and marks the
  loop (`↺`) rather than recursing forever; an issue whose canonical parent is a
  nonexistent id renders at top level. (Same totality discipline as the kernel's
  `effectiveStatus`, ADR-0004.)
- `ready` is never a tree — it is the flat ranked queue (§1); a global
  priority order can't also be a hierarchy.

### 3. Footer

A separator rule, then a one-line summary (`Ready: N issues with no active
blockers` / `Total: N issues (X open, Y in progress)`), the glyph legend, and a
truncation note when a limit applied (`Showing 10 of 18 — use --limit 0 for
all`). Truncation is always disclosed, never silent.

### 4. `show <id>` detail view

A header line (`<glyph> <id> · <title>   [<prio> · <STATUS>]`), then provenance
(assignee, the derived epic marker, created/updated, close reason) and the issue's
`labels` (including any `type:*`), then `DESCRIPTION` and `NOTES` blocks, then the
relationships inline (blockers, dependents, parent, related) — with children
rendered as a tree (§2). The `DESCRIPTION`/`NOTES` blocks are where ADR-0014's
untrusted-content fence appears in human output; one-line list/ready rows rely
on byte-sanitization plus width truncation rather than a per-row fence.

### 5. `stats`

A small labelled summary block (totals by state + ready count).

### 6. Color and glyphs are independent surfaces

Don't conflate them:

- Color — `--color=auto|always|never`; `auto` (default) emits ANSI only to a
  TTY, and `NO_COLOR` / piped / CI force `never`. `--json` never colors.
- Glyphs — `--glyphs=auto|unicode|ascii`; `auto` (default) detects terminal
  capability, and `--plain` is shorthand for `--color=never --glyphs=ascii`.

So a color-capable terminal that can't render the glyphs still gets color, and a
plain pipe gets neither — the two never move together. (This `--color`/`--glyphs`
surface is a CLI contract as stable as `--json` — additive-only from 1.0,
ADR-0008 §Stability horizon; `NO_COLOR` per ADR-0013.)

### 7. Color semantics (what is colored)

Color is a redundant channel for what the glyph already conveys — never the
sole signal (a `--glyphs=ascii` or `NO_COLOR` reader loses nothing) — applied
sparingly at the token level, not to whole lines. Use the named ANSI 8/16
colors (plus bold/dim) so it survives light and dark themes; honor
`--color=never` / `NO_COLOR`; `--json` is never colored.

Status → color (on the glyph, and the `STATUS` word in `show`), reflecting
effective state:

| State | Glyph | Color |
|---|---|---|
| ready (open, workable) | `○` | green |
| in_progress | `◐` | yellow |
| blocked | `●` | red |
| deferred | `❄` | blue / cyan |
| done | `✓` | dim green |
| cancelled | `✗` | dim / gray |

Priority → color (on the `P0`–`P4` token): `P0` red (bold), `P1` yellow, `P2`
default, `P3` / `P4` dim — only the urgent end is emphasized.

Per-token on a one-line / tree node:

- glyph → status color (above), the primary signal;
- id → dim (a secondary handle);
- prio → priority color;
- `[epic]` → a highlight (bold / a distinct accent) — the rare, meaningful
  marker;
- title → default, dimmed when closed (done/cancelled) so finished work
  recedes;
- tree connectors → dim.

`stats` shows each state's count in that state's status color; the footer
legend renders each glyph in its color, so the mapping is self-documenting.

(Exact hues are taste and need a real terminal pass; this pins the *semantics* —
what is colored, the status→hue mapping, redundancy-with-glyph — and leaves shade
tuning to implementation.)

### 8. Editing long text via `$EDITOR`

Flags are fine for short fields, but a multi-line `description` is
painful as `--description "…"`. So (the notes journal is not an editable
document — a journal entry is composed once and submitted with
`note add … -` reading stdin, ADR-0027; the editor surface is for the
mutable `title`/`description` only):

- `tl create` opens `$EDITOR` only when explicitly requested — `tl create`
  with *no title* (interactive compose), or `tl create … --edit`. Given a title,
  `tl create "<title>"` is always non-interactive (no surprise editor in a
  TTY — important for quick-start and agents); pass `--description "…"` (or `-`
  to read stdin) for the body, or `--edit` to open the editor.
- Description input precedence for `create`:
  `--description <text>` is the body; stdin is read to EOF as the body **only on
  the explicit `-` sentinel** — `--description -`, or a trailing `-` positional
  (`tl create "<title>" -`). With no `--description` and no `-`, the body is
  absent unless `--edit` is explicit; `tl create` **never reads an unrequested
  stdin**. A missing title is a `usage` error in non-TTY mode and whenever
  `--json` is requested; it never blocks waiting for interactive input.
  The sentinel is deliberate, not a convenience gap: an auto-read of any
  non-TTY stdin silently hung the tool's primary caller — an agent that
  spawns `tl create "<title>"` with an inherited, held-open pipe as stdin
  (not closed, not `/dev/null`, never reaching EOF) blocked indefinitely in
  `readToEnd`, and a non-blocking peek cannot distinguish that from a slow
  legitimate writer. Trade-off, accepted: bare `echo body | tl create "t"`
  does not feed the body — add `-` (`echo body | tl create "t" -`).
- `tl update <id> --description -` reads the replacement body from stdin in
  both human and JSON modes. The reader shared with `create` and `note add`
  removes exactly one final LF. Updates preserve other whitespace and Unicode
  content.
  Empty input deliberately sets an empty description; unlike creation, it is
  not interpreted as an absent assignment. Omitting `--description` leaves the
  description unchanged. Literal arguments and updates without the sentinel
  never read stdin. To store a literal dash, pipe `printf '%s' '-'` into
  `tl update <id> --description -`.
  A failed read returns `internal` with a remedy before any update operation
  is written, including other fields supplied in the same command. Invalid
  syntax and retired note flags are rejected before requesting stdin.
- `tl edit <id>` opens the issue's editable fields (title, description) in
  `$EDITOR` and applies the diff on save. Notes are not editable — an entry is
  immutable; append a new one with `note add` (ADR-0027).
- Resolution order `$VISUAL` → `$EDITOR` → a sensible fallback; aborting the
  editor (no change / non-zero exit) cancels the operation. Always overridable by
  passing the field as a flag, so automation never blocks on an editor.
- Commands that would spawn an editor (`edit`, `create --edit`, or interactive
  `create` without a title) are refused as `usage` under `--json`; the machine
  path is flags/stdin, then a normal JSON envelope. The fallback editor is `vi` on
  POSIX and `notepad` on Windows; if the fallback cannot be executed, the command
  fails with `usage` and a human-readable hint.

## Consequences

- The one-line stays predictable — one variable field (the title, truncated to
  width). Hierarchy lives in the tree view (§2), so long titles never fight a
  parent suffix, and the rare `[epic]` marker carries the structural signal.
- Tree vs queue is a clean split. `ready` is the flat ranked work
  queue; `list` (tree by default) / `why` / `unblocks` / `show` are the
  structural views — and the
  tree is total on the cyclic/dangling/multi-parent graphs a merge can produce.
- Color is accessible. It is redundant with the glyph and theme-portable, so
  `--plain` / `NO_COLOR` / a colorblind reader loses no information.
- The machine path is never ambiguous. `--json` is always uncolored, never
  spawns an editor, and emits one envelope (ADR-0008); the human path is this ADR.

## Alternatives considered

- Append `← <parent-title>` to ranked lines. Rejected: a second variable-width
  field that wraps on long titles, and `ready` excludes epics so there is no
  adjacent parent to reference meaningfully — hierarchy belongs in the tree view
  and the parent in `--json`.
- Render `type:*` labels inline (`[bug]`, `[feature]`). Rejected: type labels
  drive nothing and are common, so inlining them clutters every line and drowns
  the rare, meaningful `[epic]`; surface them in `show` / `--json` / `--label`
  filtering instead.
- Tree-group the `ready` queue. Rejected: `ready` is a global ranked queue and
  excludes epics — tree-grouping would destroy the priority/critical-path order
  that is its whole purpose.
- Couple color and glyphs into one flag. Rejected: a color-capable terminal
  that can't render Unicode glyphs (or vice versa) is common; one flag forces an
  all-or-nothing choice the independent `--color`/`--glyphs` surfaces avoid.
- Color whole lines by status. Rejected: a screen of all-red blocked lines is
  less readable, not more; color is token-level and redundant with the glyph.
- Open `$EDITOR` by default on `tl create "<title>"`. Rejected: a surprise
  editor in a TTY breaks quick-start and agents; the editor is opt-in
  (`--edit` / no title), and the machine path is flags/stdin.
- Leave it in `vision.md` prose. Rejected: it is a presentation contract
  pinned for 1.0 stability (ADR-0008 §Stability horizon) that deserves an
  owning ADR, keeping vision navigable.
