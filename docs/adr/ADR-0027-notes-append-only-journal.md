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
error whose message teaches the replacement (`tl note add`). The `create`
and `update` wire records lose their `notes` payload key with them (the
CLI's `create` never exposed a notes flag; the key existed only on the
record): the journal is task *output*, and at creation time there is none —
creation-time content belongs in `--description`.

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
never share a preimage (ADR-0007's preimage rules gain this form with the
implementation). The prefix makes the preimage 60 bytes — two SHA-256
blocks, where the 55-byte issue-id preimage is one — so the implementing
change also updates ADR-0018's mint-preimages-are-single-block remark; the
transcription hashes arbitrary lengths, and its padding-edge vectors already
cover multi-block messages. The id is minted at write time, carried as data
on the record, and never re-derived on read (ADR-0008). It has no display affix:
the `tl-` prefix exists to keep ids and slugs disjoint in the *positional
issue grammar* (ADR-0007), and a note id only ever appears in the dedicated
`<note-id>` argument position, so there is nothing to disambiguate. Reference
rules mirror issue ids: any unambiguous prefix within that issue's journal,
ASCII-case-folded and Crockford symbol-aliased on input; display always
shows the full 16-character handle (short enough to render bare).

The canonical tag string (`"<hlc>.<replica>.<nonce>"`) is rejected as the
*minted display handle* — not as an input form: it is 57 characters, and its
hlc-major layout means all of a project's tags share a long common prefix
(the epoch-millisecond high bits), so "unambiguous prefix" would rarely be
shorter than ~15 characters. The hash id gives git-short-hash ergonomics
instead, while the `<note-id>` argument position still *accepts* a full
canonical tag string on input, parsed by shape — that is the always-unique
fallback the collision paragraph below relies on. Handle uniqueness matters
only for reference ergonomics — never for kernel correctness, which is
tag-keyed throughout (the machinery note below): a collision is refused at
resolution with the canonical tags offered, resolution is scoped to one
issue's journal, and `note remove` resolves the handle to its underlying tag
through the local fold before writing.

### Wire records

Two new record op kinds (ADR-0008's closed enum grows; the kernel delta enum
grows by two alongside — the shell verb→delta map stays one-to-one here):

| wire `op` | kernel delta | payload (beyond the envelope) |
|---|---|---|
| `noteAdd` | noteAdd | `id` (issue), `note` (the minted note id), `text` |
| `noteRemove` | noteRemove | `id` (issue), `note`, `observed` — the entry's canonical add-tag(s) |

`noteRemove` carries an explicit `observed` array like every OR-Set remove.
Carrying the tag on the record is what makes removal delivery-order
independent: a replica that folds the remove before the add takes the
tombstone from the record itself (by tag value, not a presence check) and
hides the entry when it arrives.

`observed` is a singleton — the note's *own* add-tag — and the **decoder
enforces it** (it is not merely a CLI convention): a `noteRemove` record is
accepted only when `observed` is exactly one tag `T` **and** the record's
`note` handle equals the note id minted from `T` (`mintNoteId T` — the handle
is the SHA-256 of `T`'s `"note:"`-prefixed preimage, re-derivable at decode).
An empty, multi-tag, or mismatched-`observed` record fails closed as
malformed (ADR-0008). This is what makes cross-entry interference
*unrepresentable* through the wire: a kernel `noteRemove` tombstones every
stamp it carries at that stamp's own element, so without the decoder check a
crafted record could name one entry while tombstoning another (or many). The
check is purely structural (handle = hash of tag), independent of whether the
add has been folded, so remove-before-add still works.

Records carrying the new kinds are stamped `v: 2`. This follows ADR-0008's
versioning rule (a new op kind is exactly what an old reader could not fold)
and its `compacted`-marker precedent: the bump rides the records an old
reader actually meets, so a pre-journal binary fail-closes with an upgrade
message on any segment containing note ops. Stated honestly, that is
segment-wide, not note-local: segments are per-replica and append-only, so
the first note op an upgraded replica writes makes stale binaries refuse
that replica's *entire* active segment — every op in it — until the reader
upgrades; note-free segments remain readable. For this pre-public
repository's one flag-day window the blast radius is accepted. All other
records are unchanged and stay `v: 1`. `create` and `update` lose their `notes` payload key (see the legacy
section below for how a new reader treats old records that carry it).

Like every issue-local write, a `noteAdd`/`noteRemove` folded before its
issue's `create` is retained, not ignored — the journal lives in the same
per-id-keyed structure discipline as the field registers and `labels`
(ADR-0002), which is what keeps the fold permutation-insensitive. The
projections are pinned too: `noteAdd` bumps `updatedAt` — the journal is
issue-local *content*, appending progress is exactly the activity
`updatedAt` exists to reflect, and today's scalar notes writes already bump
it. The projection stays a pure fold of materialized state: `updatedAt` is
the max over the scalar-register stamps and the journal's add-tags.
`noteRemove` does *not* bump it: a tombstone materializes the *observed
add-tags*, never the remove op's own stamp, so a pure state projection
cannot see the removal — and removal is cleanup, not content. The asymmetry
is deliberate and disclosed here. Note ops appear in `tl log` / the
`--since` feed like any op.

### Kernel machinery: reuse the OR-Set, no parallel structure

Each note is an element of an OR-Set *keyed by its add-tag* — the element is
the tag, so an entry has exactly one add-tag by construction. Entry payloads
(the minted handle, the text, and the actor/time provenance projected from
the envelope) live in a map keyed by the same tag. Nothing kernel-side is
keyed by the 16-char handle: it is carried payload, so two records carrying
equal handle bytes from distinct stamps are two independent entries, and a
tombstone — keyed by tag — cannot reach a sibling under any payload bytes.
`noteRemove` tombstones that one tag. The observed-remove join laws
(commutative/associative/idempotent, both legs) therefore come from the
existing `OrSet` lemmas rather than a new structure, and removal-exactness
is element-scoped and unconditional over tags — not conditional on handle
uniqueness, and not resting on the stamp-uniqueness carried assumption. (The
implementation lands on the element-scoped tombstone shape; if the two
changes are in flight together, the journal reuses that shape directly.)

Handle collisions confine themselves to the CLI reference grammar:
`note remove` resolves `<note-id>` through the local fold, and if the handle
names more than one live entry it refuses with a teaching error listing the
colliding entries' canonical tag strings — and the canonical tag
(`"<hlc>.<replica>.<nonce>"`) is itself accepted in the `<note-id>` position
as the always-unique fallback, parsed by shape exactly as ids are told from
slugs (ADR-0007). Records sharing one *complete* triple fold to one entry;
their payloads join by the unconditional rule pinned with the ordering
clause below.

One coincidence to state plainly so nobody "fixes" it later: the OR-Set is
add-wins, but for notes the add-wins/remove-wins distinction collapses. Tags
are unique and never re-added — there is no operation that could re-add a
removed note's tag — so the journal behaves as a 2P-set (tombstoned forever)
even though it is built on add-wins machinery. Add-wins governs *re-addable*
elements (edges, labels); notes have no re-add, so tombstoned-forever is the
correct and intended reading, not a bug.

### The contract, clause by clause

Each clause is a theorem obligation on the implementation or an explicit
non-guarantee:

- **Convergence** — union merge of two journals is commutative, associative,
  idempotent on both legs (adds and tombstones). *Theorem* (`Journal.merge_comm`
  / `_assoc` / `_idem`, `Tl/Crdt/Journal.lean` — OrSet reuse on the entries leg,
  the payload semilattice `NotePayload.join_comm`/`_assoc`/`_idem` on the other).
- **Delivery- and duplication-independence** — folding the same op multiset
  in any order, with duplicates, yields the same journal; duplicate delivery
  of one op yields one entry. *Theorem* (`Journal.merge_right_comm`,
  `Journal.merge_addDelta_duplicate`; the state-level fold rides the proved
  `fold_perm`/`fold_eq_of_mem_iff` through the re-discharged join laws).
- **Concurrent adds all retained** — no append is ever lost to a concurrent
  append. Equal text from separate ops stays separate entries. *Theorem*
  (`Journal.visible_both_concurrent_adds`;
  `Journal.visibleEntries_distinct_rows` for the two-rows-per-two-stamps
  rendering).
- **Removal is delivery-order independent** — a remove folded before its add
  still hides the entry when the add arrives (tombstone by tag value).
  *Theorem* (`Journal.not_visible_removeDelta_then_addDelta`).
- **Remove-exactness** — a remove affects exactly the tags it observes, for
  any payload bytes: tombstones are tag-keyed and the handle is not a kernel
  key. *Theorem, unconditional* (`Journal.visible_merge_removeDelta_iff_of_not_mem`,
  plus `Journal.payloads_merge_removeDelta` for the payload half). The kernel
  op tombstones *every* stamp in `observed`, so "affects exactly the entry it
  names" is a joint guarantee of this theorem **and** the decoder's own-tag
  enforcement above (singleton `observed` minting to the `note` handle): the
  theorem bounds the effect to the observed tags, and the decoder bounds the
  observed tags to the record's own single entry — a crafted cross-entry or
  mass remove is rejected as malformed, not folded.
- **No resurrection** — a removed entry never becomes visible again:
  tombstoned tags stay tombstoned, and no op can re-add a tag. *Theorem*
  (`Journal.not_visible_merge_of_tombstoned`, merge-general over the whole
  future; `Journal.tombstone_mono`). Tag freshness across ops is the same
  nonce-uniqueness carried assumption every OR-Set add already leans on — no
  separate handle-uniqueness assumption is introduced.
- **Deterministic order and payload** — the visible journal is ordered by
  the complete stamp `(hlc, replica, nonce)` ascending. Between distinct
  entries this is total outright — an entry's identity *is* its stamp — so
  there are no tie-break levels and no distinct-stamps hypothesis. What can
  collide is payload: records sharing one complete triple fold to a single
  entry, and that entry's payload joins by the unconditional lexicographic
  maximum over the *decoded* `(text, handle, actor)` tuple, compared
  componentwise: the two strings by canonical UTF-8 bytes (equivalently, by
  code point — the order the kernel's `String` order realizes), and the
  optional actor with an absent actor (`none`) ordered below every present
  one. This is a semilattice max, the same realization discipline as the LWW
  value tie-break (ADR-0002) and the canonical-parent selection (ADR-0003 §4).
  Under honest writers the rule never fires (one op, one payload); on
  adversarial or duplicated records determinism — not any particular winner
  — is the guarantee. *Theorem* (`Journal.visibleEntries_pairwise_lt` for the
  stamp-ascending order; `Journal.mem_visibleEntries` +
  `Journal.visibleEntries_merge_comm` + the payload join laws for the
  permutation/duplication/merge invariance; `Journal.PayloadTotal` — discharged
  for every folded state by `payloadTotal_fold` — makes the rendering's skip
  case unreachable, so retention *is* rendering).
- **Immutability** — there is no note edit in the first release (excluded
  below);
  corrections are new notes. *Holds by absence of any mutating op.*
- **Frame-safety** — notes drive no scheduling or graph behavior: `ready`,
  epic rollup, cycle detection, and every graph behavior never read the
  journal (ADR-0002/0003), *proved* — `ready_noteAdd`/`ready_noteRemove`,
  `effectiveStatus_noteAdd`/`effectiveStatus_noteRemove` (`Tl/Kernel/Frame.lean`).
  Unlike `labels` and `meta`, the journal *does*
  feed one projection — `updatedAt`, exactly as pinned above — and nothing
  else. *By construction; stated in the overview, with frame lemmas only if
  near-free.*
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

An entry renders as `{ "id": <note-id>, "tag": <canonical add-tag string>,
"time": <ISO-8601 UTC>, "actor": <string|null>, "text": <string> }` — `tag`
is the always-unique reference form, the escape hatch when handles collide;
a placeholder (under `--all`) is the same object with `"removed": true` and
no `text`. `time` is the add op's HLC
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
`--json` change, so it bumps `schemaVersion` to 3 under ADR-0008's 0.x rule
(the claim-outcome enum took 2, ADR-0013) — disclosed, never silent.
Consumers of any other field are unaffected.

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
  completely and correctly *except* on two disclosed counts: legacy scalar
  notes are not displayed (the text stays intact in the log bytes,
  recoverable by the migration), and — until the migration runs —
  `updatedAt` no longer counts a notes-only legacy write (the shipped rule
  bumps on any `update` op's envelope; the pinned rule counts register
  stamps and journal add-tags), so an issue whose latest activity was a
  notes write reads older than the pre-journal binary reported. The
  migration restores it exactly: the synthetic entry's add-tag carries the
  winning write's hlc. This is the honest middle ground: folding legacy writes into a
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
  exactly what the nonce level exists to keep distinct. This deliberately
  refines the ratified shorthand "stamped with the winning write's stamp":
  hlc, replica, and actor — the provenance the ratification protects — are
  preserved verbatim; the nonce is identity, not provenance. The migration
  task defers to this rule. Historically
  overwritten values do **not** each become entries. Only the tracker ref is rewritten; the repository's commit
  history is untouched. tl is pre-public, so this flag-day (including the
  forced update of the shared tracker ref) is a one-time owner operation, not
  a product migration path.
- **Stragglers.** During the window, a stale pre-journal binary that meets
  `v: 2` note records fail-closes on that segment with an upgrade message
  (ADR-0008) — it cannot silently mis-fold or quietly fight the new format.
  Its own legacy `notes` writes fold inert (unknown bag) on new readers, and
  the one-off migration will already have run — an inert straggler write is
  therefore *permanently* invisible to materialized views unless re-entered.
  The text survives in the log bytes; recovery is manual (`note add` it
  again) — the migration is not re-run. The fail-closed effect ends when the
  last working copy updates; the flag-day protocol is therefore to update
  every working copy before resuming writes, and the migration's
  verification includes a check for scalar-notes records stamped after the
  migration cut. Accepted and recorded here rather than engineered around,
  because the window is one repository for one flag-day.

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
  is narrowed to title/description accordingly.
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
  kinds; `--json` `schemaVersion` 3 for the re-typed `notes` field (the
  claim-outcome enum took 2, ADR-0013).
- Doc-corpus staging: vision.md's prose surface (field table, command
  tables, editor prose, exclusions) moves to the journal with this ADR; the
  corpus lines that inventory the *current* scalar code stay accurate until
  the implementing change lands and are updated by it in the same change —
  vision's generated grammar block, ADR-0002's scalar-register list,
  ADR-0003's scalar-verb line and JSON-projection field list, ADR-0008's op
  inventory, `updatedAt` projection rule, and actor-envelope remark ("never
  affects … the kernel" — actor becomes tag-keyed payload and a join-tuple
  component here, while convergence and identity stay actor-free),
  ADR-0017's editor-pathway lines, and ADR-0018's single-block remark.
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
- **`--message`/`-m` text flag** (the preference relayed into the ratifying
  task). Rejected, with the precedent stated honestly: the grammar already
  carries text-payload value flags (`create --description`,
  `update --title`/`--description`), so a message flag would not be
  unprecedented; but those carry *secondary* fields, and the grammar's one
  free-text primary payload — `create`'s title — is positional. An entry's
  text is `note add`'s sole primary payload, so it is positional like
  `create`'s title, with `-` reading stdin (the `create` body convention).
  Overriding the relayed preference on grammar-consistency grounds is
  recorded deliberately; before first release the reversal cost is one
  grammar row.
- **The canonical stamp string as the note id.** Rejected above: 57 chars
  with a shared hlc-major prefix defeats prefix ergonomics; the hash handle
  matches issue-id conventions.
- **Lowering every historical scalar write to an entry** (in import or
  migration). Rejected: the journal's meaning is "entries someone chose to
  append," not "every LWW state the register passed through"; overwritten
  values remain visible as log history.
