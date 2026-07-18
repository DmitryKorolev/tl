# ADR-0027 — Notes as an append-only journal (`note add` / `note list` / `note remove`)

- Status: Accepted
- Date: 2026-07-17

## Context

Today `notes` is a single whole-string LWW register
(`IssueData.notes : Reg (Option String)`, ADR-0002's scalar construction), and
`update --append-notes` is a CLI read-modify-write over it: read the current
value, concatenate a line, write the whole string back. Under concurrent
writers the racing loser is dropped wholesale — disclosed only in the flag's
help text. That loss case is not an edge case here: tl's primary documented
use of notes is *multiple agents appending incremental progress notes to the
same issue*, which is exactly the concurrent-append workload a whole-field
LWW register cannot retain.

The field split was intentional from the start and is worth preserving: the
vision field table defines `description` as the task *input* (the issue's
current specification/context) and `notes` as task *output* (evidence,
decisions, progress), both explicitly "whole-field, not threaded" — threaded
comments were consciously excluded, and imported comments go to the opaque
`meta` map (ADR-0005). `--notes` arrived only as one of `update`'s generic
scalar flags; `--append-notes` was later loop ergonomics whose
read-modify-write race was known and accepted for *serial* loops. The journal
below completes the original task-output intent — an evidence/decision
journal, not a conversation — while fixing the concurrency defect. That is
also why the field keeps the name `notes`, not `comments`.

tl is pre-public and pre-release (ADR-0008's stability horizon: the forever
promises bind from 1.0), so the first release can ship the sound design
outright; there is no installed base whose `update --notes` vocabulary needs
preserving.

## Decision

Notes become an **append-only journal of immutable entries** with per-entry
removal. `description` remains the issue's single mutable LWW document. There
is no replace and no reset on notes: a correction is a new note; cleanup is
removal of a specific entry. Both scalar interfaces are retired — `update
--notes` and `update --append-notes` are removed, and using them is a `usage`
error whose message teaches the replacement (`tl note add`). `create --notes`
is retired with them: the journal is task *output*, and at creation time
there is none — creation-time content belongs in `--description`.

### Surface

- `tl note add <id> <text>` — appends an immutable entry; `-` as `<text>`
  reads it from stdin (the `create` body convention). Echoes the new entry.
- `tl note list <id>` — the visible entries, oldest first; `--all`
  additionally shows removed-entry placeholders (provenance visible, text
  hidden).
- `tl note remove <id> <note-id>` — tombstones that one entry. Visible =
  entry exists and is not tombstoned. The output carries the honesty
  disclosure below.

The verb is `remove`, matching `dep remove` / `parent remove` /
`label remove`. ("Retract" would be a second removal vocabulary for the same
concept.) None of these are write-time guards in the ADR-0008 inventory
sense: the retired flags fail at argument parsing (`usage`, exit `2`), and
`note add`/`note remove` refuse nothing a merge could contradict.

### Note identity and the note id

An entry's *identity* is its add op's existing `(hlc, replica, nonce)`
envelope triple — the same OR-Set add-tag machinery as every collection
(ADR-0002/0008), no new identity scheme. Duplicate delivery of the same op is
therefore one entry; equal text written by separate ops is separate entries.

The user-facing *handle* (the note id) is minted like an issue id
(ADR-0007/0018): the leftmost 80 bits of SHA-256 over the domain-separated
preimage `"note:" ++ replica-id(13) ++ hlc(16 hex) ++ nonce(26)`, Crockford
base32, 16 lowercase chars — the same fixed-width component concatenation
ADR-0007 pins for issue ids, behind a domain prefix so the two id spaces can
never share a preimage (ADR-0007's preimage inventory gains this row with the
implementation). It is minted at write time, carried as data on
the record, and never re-derived on read (ADR-0008). It has no display affix:
the `tl-` prefix exists to keep ids and slugs disjoint in the *positional
issue grammar* (ADR-0007), and a note id only ever appears in the dedicated
`<note-id>` argument position, so there is nothing to disambiguate. Reference
rules mirror issue ids: any unambiguous prefix within that issue's journal,
ASCII-case-folded and Crockford symbol-aliased on input; display lengthens
the shown prefix only as far as needed to disambiguate within the journal.

The canonical tag string (`"<hlc>.<replica>.<nonce>"`) is rejected as the
handle: it is 57 characters, and its hlc-major layout means all of a
project's tags share a long common prefix (the epoch-millisecond high bits),
so "unambiguous prefix" would rarely be shorter than ~15 characters. The
hash id gives git-short-hash ergonomics instead. Note-id uniqueness under
truncation is carried exactly like issue-id uniqueness (ADR-0007's collision
policy); the blast radius is smaller still, since resolution is scoped to one
issue's journal and `note remove` resolves the id to its underlying tag
through the local fold before writing.

### Wire records

Two new record op kinds (ADR-0008's closed enum grows; the kernel delta enum
grows by two alongside — the shell verb→delta map stays one-to-one here):

| wire `op` | kernel delta | payload (beyond the envelope) |
|---|---|---|
| `noteAdd` | noteAdd | `id` (issue), `note` (the minted note id), `text` |
| `noteRemove` | noteRemove | `id` (issue), `note`, `observed` — the entry's canonical add-tag(s) |

`noteRemove` carries an explicit `observed` array like every OR-Set remove.
It is a singleton *by construction* — naming the note means having observed
its one add — and carrying the tag on the record is what makes removal
delivery-order independent: a replica that folds the remove before the add
takes the tombstone from the record itself (by tag value, not a presence
check) and hides the entry when it arrives.

Records carrying the new kinds are stamped `v: 2`. This follows ADR-0008's
versioning rule (a new op kind is exactly what an old reader could not fold)
and its `compacted`-marker precedent: the bump rides the records an old
reader actually meets, so a pre-journal binary fail-closes on a segment
containing note ops with an upgrade message, while its ability to read
note-free segments is unaffected. All other records are unchanged and stay
`v: 1`. `create` and `update` lose their `notes` payload key (see the legacy
section below for how a new reader treats old records that carry it).

Like every issue-local write, a `noteAdd`/`noteRemove` folded before its
issue's `create` is retained, not ignored — the journal lives in the same
per-id-keyed structure discipline as the field registers and `labels`
(ADR-0002), which is what keeps the fold permutation-insensitive. The
projections are pinned too: note ops do not bump `updatedAt` (they follow the
edge/label/meta rule, not the scalar rule — the journal is a collection, and
an evidence append is not an edit of the issue's fields), and they appear in
`tl log` / the `--since` feed like any op.

### Kernel machinery: reuse the OR-Set, no parallel structure

Each note is an element of an OR-Set whose single add-tag *is* its identity;
entry payloads (text, plus the actor/time provenance projected from the
envelope) live in a per-note map keyed by the note id. `noteRemove`
tombstones that one tag. The observed-remove join laws
(commutative/associative/idempotent, both legs) therefore come from the
existing `OrSet` lemmas rather than a new structure, and removal-exactness is
element-scoped — a tombstone keyed at one note cannot disturb a sibling —
rather than resting on the stamp-uniqueness carried assumption. (The
implementation lands on the element-scoped tombstone shape; if the two
changes are in flight together, the journal reuses that shape directly.)

One coincidence to state plainly so nobody "fixes" it later: the OR-Set is
add-wins, but for notes the add-wins/remove-wins distinction collapses. Ids
are unique and never re-added — there is no operation that could re-add a
removed note's tag — so the journal behaves as a 2P-set (tombstoned forever)
even though it is built on add-wins machinery. Add-wins governs *re-addable*
elements (edges, labels); notes have no re-add, so tombstoned-forever is the
correct and intended reading, not a bug.

### The contract, clause by clause

Each clause is a theorem obligation on the implementation or an explicit
non-guarantee:

- **Convergence** — union merge of two journals is commutative, associative,
  idempotent on both legs (adds and tombstones). *Theorem (OrSet reuse).*
- **Delivery- and duplication-independence** — folding the same op multiset
  in any order, with duplicates, yields the same journal; duplicate delivery
  of one op yields one entry. *Theorem.*
- **Concurrent adds all retained** — no append is ever lost to a concurrent
  append. Equal text from separate ops stays separate entries. *Theorem.*
- **Removal is delivery-order independent** — a remove folded before its add
  still hides the entry when the add arrives (tombstone by tag value).
  *Theorem.*
- **Remove-exactness** — a remove affects exactly the named note, for any
  payload bytes (element-scoped tombstones make cross-entry interference
  unrepresentable). *Theorem.*
- **No resurrection** — a removed note never becomes visible again; a
  removed id is never reused (ids are minted from fresh op stamps).
  *Theorem, plus the id-uniqueness carried assumption for the reuse half.*
- **Deterministic order** — the visible journal is ordered by the complete
  stamp `(hlc, replica, nonce)` ascending, with the note id and then the
  remaining payload as unconditional final tie-breaks. The order is total
  with *no* distinct-stamps hypothesis and no traversal-order dependence —
  the same realization discipline as the LWW value tie-break (ADR-0002) and
  the canonical-parent selection (ADR-0003 §4). Under honest writers the
  stamp alone already decides; the tail levels only ever fire on
  (assumed-away) stamp collisions or adversarial records, where determinism
  — not any particular winner — is the guarantee. *Theorem: rendering is
  invariant under fold permutation, duplication, and replica merge.*
- **Immutability** — there is no note edit in the first release (excluded
  below);
  corrections are new notes. *Holds by absence of any mutating op.*
- **Frame-safety** — notes drive nothing: `ready`, epic rollup, cycle
  detection, and every graph behavior never read the journal, like `labels`
  and `meta` (ADR-0002/0003). *By construction; stated in the overview, with
  frame lemmas only if near-free.*
- **Provenance, not authentication** — an entry's actor and time are carried
  provenance (ADR-0013), not authenticated facts, and any repository writer
  may remove any note: actor is not an authorization layer (ADR-0014).
  *Explicit non-guarantee.*
- **No secure deletion** — the honesty disclosure below. *Explicit
  non-guarantee.*

### Honesty disclosure on removal

Removal hides an entry from materialized views only. The op log is
append-only and replicated: the entry's bytes remain in log history, and
already-synced clones retain them — exactly as removed labels and edges
remain historically represented. tl makes no secure-deletion claim; true
erasure would require destructive history rewriting and cannot reach synced
replicas. The `note remove` output states this ("hidden from views; the text
remains in the replicated log history"), and `note list --all` keeps removed
entries visible as placeholders — provenance shown, text hidden by default
(the log itself is the escape hatch, deliberately manual).

### `--json` shapes and `show`

An entry renders as `{ "id": <note-id>, "time": <ISO-8601 UTC>, "actor":
<string|null>, "text": <string> }`; a placeholder (under `--all`) is the same
object with `"removed": true` and no `text`. `time` is the add op's HLC
physical time projected like every other timestamp; `actor` is the envelope
actor. Note ids render bare (16 chars, no affix — there is no display form to
diverge from). Human and `--json` output show the same entries in the same
order (parity).

`show` renders the full visible journal, oldest first, and `show --json`
carries the same array under the issue's `notes` key. `show` means one issue
*in full*, and a default truncation would be a cap on the primary
evidence-reading surface; if real journals ever outgrow this, an explicit
limit flag can be added additively. The issue object's `notes` field thereby
changes type (string → array of entries): a re-typed field is a breaking
`--json` change, so it bumps `schemaVersion` to 2 under ADR-0008's 0.x rule —
disclosed, never silent. Consumers of any other field are unaffected.

### Import, and the legacy scalar

The bulk-import format (ADR-0005) keeps its `notes` field — source trackers
have notes, and dropping them would lose data. The importer lowers it to
**one** synthetic `noteAdd` per record: deterministic stamp under ADR-0005's
scheme (a `note` op-role in the nonce preimage; the hlc from the record's
`createdAt`, like the other non-lifecycle seed ops), note id minted from that
stamp as usual. One value in, one entry out — the import format's `notes` is a single
string, so there is nothing else it could mean.

For live logs written before this change, the rule is:

- **Reading (the compatibility window).** `notes` is no longer a recognized
  `create`/`update` payload key, so on a legacy record it routes to the
  ADR-0008 preserve-unknown bag: preserved verbatim on any rewrite, never
  materialized. A journal-capable binary therefore reads a pre-journal log
  completely and correctly *except* that legacy scalar notes are not
  displayed — the text stays intact in the log bytes, recoverable by the
  migration. This is the honest middle ground: folding legacy writes into a
  compatibility register would keep the retired structure alive in the
  kernel, and lowering each historical write to an entry on the fly would
  contradict the migration rule below (overwritten values are history, not
  entries).
- **Migration (one-off, this repository).** tl's own tracker log is migrated
  once, promptly after the implementation lands: each issue's *winning*
  legacy scalar value (LWW over the old register semantics) becomes exactly
  one synthetic immutable entry carrying the winning write's hlc, replica,
  and actor — so time/actor provenance is preserved, `note list` shows it in
  its true chronological position, and the record lands in the winning
  replica's own segment (segments stay per-replica authored, ADR-0008). Its
  nonce is *fresh* and deterministically derived (a domain-separated hash of
  the winning stamp), not the original write's: the legacy record stays in
  the log, so reusing its complete triple would put two records on one
  envelope identity and break the add-tag/nonce-uniqueness posture
  (ADR-0007) for no provenance gain — same-`(hlc, replica)` op pairs are
  exactly what the nonce level exists to keep distinct. Historically
  overwritten values do **not** each become entries. Only the tracker ref is rewritten; the repository's commit
  history is untouched. tl is pre-public, so this flag-day (including the
  forced update of the shared tracker ref) is a one-time owner operation, not
  a product migration path.
- **Stragglers.** During the window, a stale pre-journal binary that meets
  `v: 2` note records fail-closes on that segment with an upgrade message
  (ADR-0008) — it cannot silently mis-fold or quietly fight the new format.
  Its own legacy `notes` writes fold inert (unknown bag) on new readers. Both
  effects end when the last working copy updates and re-syncs; accepted and
  recorded here rather than engineered around, because the window is one
  repository for one flag-day.

Nothing in this section is a released compatibility surface: no release has
shipped the scalar, and the first release ships the journal (ADR-0008
stability horizon).

### Explicitly excluded

- **No note edit.** Entries are immutable in the first release; corrections
  are new notes.
  Immutability is what keeps identity trivial (no per-entry LWW, no
  edit-vs-remove races) and the merge story free.
- **No threads, replies, reactions, or notifications.** The journal is an
  evidence/decision record, not a conversation — the original not-threaded
  exclusion stands, and the name stays `notes` for exactly that reason.
- **No `$EDITOR` pathway for notes.** The editor surface is for re-editing
  mutable documents (title, description); a journal entry is composed once
  and submitted (`-` reads stdin for long text). The vision `edit` surface
  narrows accordingly when implemented.
- **No secure deletion** (disclosure above).

## Consequences

- The multi-agent loss case is gone: concurrent appends are all retained, as
  a proved property rather than a serial-use convention. The
  `--append-notes` read-modify-write race disappears with the interface.
- Agents and humans get stable per-entry handles: a note can be cited,
  listed, and removed exactly, with provenance attached.
- The log grows by one record per entry and tombstones accumulate, like
  every OR-Set collection (ADR-0002); the growth story is unchanged
  (ADR-0001/0008).
- One-time surface bumps, both disclosed: record `v: 2` on the two new op
  kinds; `--json` `schemaVersion` 2 for the re-typed `notes` field.
- Entry order is stamp order, not causal order: a skewed clock places its
  entries by its own timestamps (within the ADR-0007 skew window's
  admission). That is the same LWW-family posture as every timestamp in tl —
  provenance is honest, and the order is deterministic and identical on
  every replica.
- The kernel proof surface grows by two deltas and the journal theorems; the
  join laws are inherited from `OrSet`, not re-proved.

## Alternatives considered

- **Keep the LWW scalar and document the race.** Rejected: it silently loses
  concurrent appends in exactly tl's primary multi-agent workload; a
  documented data-loss default is still a data-loss default.
- **Observed-reset append log** (append entries; a `replace` verb resets the
  *observed* set and writes a new base value). Rejected: convergent and
  provable, but its replace verb surfaces observed-tombstone semantics to
  users ("replace removed only what you had seen"), and its base register
  keeps notes half-document — `description` already fills the document role.
- **HLC-cutoff replacement schemes** (a replacement drops entries below its
  stamp). Rejected: the total stamp order is not causality — a concurrent
  append can sort below a replacement and vanish — the same silent loss
  through an extra mechanism.
- **`comments` naming.** Rejected: implies a conversation surface (threads,
  replies, editing, notifications) that tl deliberately excludes.
- **`retract` verb.** Rejected: the removal vocabulary is `remove`
  (dep/parent/label); a synonym would suggest a semantic difference that
  does not exist.
- **`--message`/`-m` text flag.** Rejected: the grammar has no message-flag
  precedent — payloads are positional with `-` for stdin (`create`); git
  familiarity does not outweigh internal consistency.
- **The canonical stamp string as the note id.** Rejected above: 57 chars
  with a shared hlc-major prefix defeats prefix ergonomics; the hash handle
  matches issue-id conventions.
- **Lowering every historical scalar write to an entry** (in import or
  migration). Rejected: the journal's meaning is "entries someone chose to
  append," not "every LWW state the register passed through"; overwritten
  values remain visible as log history.
