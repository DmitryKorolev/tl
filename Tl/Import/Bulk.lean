/-
`Tl.Import.Bulk` — the one-shot bulk importer (ADR-0005): parse tl's portable
import format (a JSONL of issue records) into a deterministic seed op-log.

This is tested I/O shell, not kernel. Determinism is the load-bearing property
(re-importing a source byte-stably reproduces the log): every id, replica id,
and nonce derives from the source data via SHA-256, and every fallback
timestamp from a fixed base plus a per-record ordinal (causality-clamped) —
never from `now()` or entropy. The seed ops are written under a deterministic *import
replica* (a single-writer segment), so the live replica is untouched and a
later `tl create` is an ordinary second replica.

The kernel is unchanged: the import degenerates to a trivial single-replica
fold. Edge endpoints reference other records' source ids; a dangling endpoint
is skipped and disclosed (no placeholder issue is fabricated, ADR-0005).
-/
import Tl.Format.Codec
import Tl.Format.Ids
import Tl.Format.Time
import Tl.Hash.Sha256

namespace Tl.Import

open Tl.Format
open Tl.Kernel
open Tl.Crdt
open Tl.Hash
open Lean (Json)

/-- A parsed import record (ADR-0005 §the import format). Only `sourceId`/`title`
    are required; the rest carry the documented defaults. `meta` already folds in
    unknown keys (`import:<k>`) and the source ref (`ext:<tag>`). -/
structure ImportRecord where
  sourceId : String
  title : String
  status : Status := .Open
  priority : Fin 5 := ⟨2, by decide⟩
  assignee : Option String := none
  description : Option String := none
  notes : Option String := none
  labels : List String := []
  deferUntil : Option Nat := none
  closeRes : Option CloseResolution := none
  duplicateOf : Option String := none
  blockedBy : List String := []
  parent : Option String := none
  related : List String := []
  metaKv : List (String × String) := []
  createdAt : Option Nat := none
  closedAt : Option Nat := none
  claimedAt : Option Nat := none
  /-- The raw source line, hashed into the source fingerprint. -/
  raw : String := ""

/-- Import controls (ADR-0005 §two distinct safety gates). -/
structure ImportOptions where
  sourceTag : String := "import"
  force : Bool := false
  allowLarge : Bool := false
  maxBytes : Nat := 5000000

/-! ### Deterministic derivation (ADR-0005/0007/0018) -/

/-- The leftmost `nBytes` of SHA-256(preimage) as a big-endian `Nat` (the NIST
    truncation convention, ADR-0018). Total: `get?` floors a (never-taken,
    `nBytes ≤ 16 < 32`) out-of-range index to `0`. -/
private def leftBitsNat (preimage : String) (nBytes : Nat) : Nat :=
  let d := Sha256.digest preimage.toUTF8
  (List.range nBytes).foldl (fun acc i => acc * 256 + (d.data.getD i 0).toNat) 0

/-- The deterministic seed id: `crockford32(SHA-256("import:" ++ tag ++ ":" ++
    srcId))[0..80 bits]`, 16 chars (ADR-0005). The one documented exception to
    the random-triple id derivation. -/
def importIssueId (tag srcId : String) : String :=
  toCrockford (leftBitsNat s!"import:{tag}:{srcId}" 10) 16

/-- The deterministic import replica id: 64 bits over `tag` + the source
    fingerprint, the same 13-char form as a live replica (ADR-0005). -/
def importReplicaId (tag fingerprint : String) : String :=
  toCrockford (leftBitsNat s!"import-replica:{tag}:{fingerprint}" 8) 13

/-- The deterministic per-op nonce (128 bits) — keyed on the op role + target so
    every seed op's `(replica, hlc, nonce)` is distinct and byte-stable across
    re-imports (ADR-0005). -/
def importNonce (tag srcId role target : String) : Nat :=
  leftBitsNat s!"import-nonce:{tag}:{srcId}:{role}:{target}" 16

/-- `2000-01-01T00:00:00Z` in epoch ms — the fixed fallback base for a
    missing/invalid timestamp, plus one ms per stable ordinal (ADR-0005). -/
def fallbackBaseMs : Nat := 946684800000

/-- Pack a physical-ms instant and a logical counter into the 64-bit HLC the
    stamp carries (ADR-0007): `physical * 2^16 + logical`. The logical bump
    orders a record's `create < claim < close` even at equal/absent timestamps,
    so the status LWW always resolves to the lifecycle op. -/
private def packHlc (physMs logical : Nat) : Nat := physMs * 2 ^ 16 + logical

/-! ### Parsing one record -/

private def malformed (msg : String) : Tl.Error := .mk' .malformedLine msg

private def knownKeys : List String :=
  ["id", "title", "status", "priority", "assignee", "description", "notes",
   "labels", "deferUntil", "closeResolution", "duplicateOf", "blockedBy",
   "parent", "related", "meta", "createdAt", "closedAt", "claimedAt"]

/-- A JSON value rendered as a flat string for the opaque `meta` channel. -/
private def jsonToMetaStr : Json → String
  | Json.str s => s
  | other => other.compress

/-- An optional string field: absent ⇒ `none`; a non-string present value is a
    malformed record (fail-closed, ADR-0005 §priority and status). -/
private def optStrField (j : Json) (sid k : String) : Except Tl.Error (Option String) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok Json.null => .ok none
  | .ok (Json.str s) => .ok (some s)
  | .ok _ => .error (malformed s!"import record {sid}: \"{k}\" must be a string")

/-- An optional ISO-8601 UTC instant field. A canonical instant ⇒ `some ms`,
    silently at *this* layer — that is the only input that carries a value
    forward, and `buildSeed` discloses separately if the causality clamp then
    moves it, or the record's status admits no projection that would surface it.
    Absent or
    `null` ⇒ `none`, also silently, because most records carry no provenance
    at all and disclosing that would bury the disclosures that matter. Anything
    else *present* ⇒ `none` with a disclosure (the caller assigns the fallback).

    A present, ill-typed value discloses rather than throwing, unlike the other
    optional fields: provenance is advisory metadata, so a bad one degrades to
    the fallback instead of refusing the record. It must not degrade *silently* —
    that is the one case where the importer would otherwise drop a value the
    record actually carried without saying so. -/
private def optInstantField (j : Json) (sid k : String) : Option Nat × List String :=
  match j.getObjVal? k with
  | .error _ | .ok Json.null => (none, [])
  | .ok (Json.str s) =>
    match Time.epochMsOfIso? s with
    | some ms => (some ms, [])
    | none => (none, [s!"import record {sid}: \"{k}\" ('{s}') is not a canonical ISO-8601 UTC instant — assigned a deterministic fallback time"])
  | .ok _ => (none, [s!"import record {sid}: \"{k}\" is not a string — assigned a deterministic fallback time"])

/-- A `List String` field (labels / blockedBy / related): absent ⇒ `[]`; a
    non-array, or a non-string element, is malformed. -/
private def strListField (j : Json) (sid k : String) : Except Tl.Error (List String) :=
  match j.getObjVal? k with
  | .error _ => .ok []
  | .ok Json.null => .ok []
  | .ok (Json.arr a) =>
    a.toList.mapM (fun
      | Json.str s => .ok s
      | _ => .error (malformed s!"import record {sid}: every \"{k}\" element must be a string"))
  | .ok _ => .error (malformed s!"import record {sid}: \"{k}\" must be an array of strings")

/-- Parse one JSONL line to a record plus its disclosures (priority clamps,
    timestamp fallbacks). Fail-closed on invalid JSON, a missing/ill-typed
    required field, or an undefined status/closeResolution value (ADR-0005). -/
def parseRecord (line : String) : Except Tl.Error (ImportRecord × List String) := do
  let j ← match Json.parse line with
    | .ok j => pure j
    | .error e => throw (malformed s!"import line is not valid JSON ({e})")
  let some (Json.str sid) := (j.getObjVal? "id").toOption
    | throw (malformed "import record needs a string \"id\" (the source id)")
  let some (Json.str title) := (j.getObjVal? "title").toOption
    | throw (malformed s!"import record {sid}: needs a string \"title\"")
  let mut disc : List String := []
  -- status
  let status ← match (j.getObjVal? "status").toOption with
    | none | some Json.null => pure Status.Open
    | some (Json.str "open") => pure Status.Open
    | some (Json.str "in_progress") => pure Status.InProgress
    | some (Json.str "done") => pure Status.Done
    | some (Json.str "cancelled") => pure Status.Cancelled
    | some (Json.str other) => throw (malformed s!"import record {sid}: unknown status '{other}' — use open | in_progress | done | cancelled")
    | some _ => throw (malformed s!"import record {sid}: \"status\" must be a string")
  -- priority: clamp 0–4 with a disclosure (ADR-0002)
  let priority : Fin 5 ← match (j.getObjVal? "priority").toOption with
    | none | some Json.null => pure ⟨2, by decide⟩
    | some (Json.num _) =>
      match ((j.getObjVal? "priority").bind (·.getNat?)).toOption with
      | some p =>
        if h : p ≤ 4 then pure ⟨p, Nat.lt_succ_of_le h⟩
        else do
          disc := disc ++ [s!"import record {sid}: priority {p} clamped to 4"]
          pure ⟨4, by decide⟩
      | none => throw (malformed s!"import record {sid}: \"priority\" must be a whole number 0–4")
    | some _ => throw (malformed s!"import record {sid}: \"priority\" must be a whole number 0–4")
  -- closeResolution
  let closeRes ← match (j.getObjVal? "closeResolution").toOption with
    | none | some Json.null => pure (none : Option CloseResolution)
    | some (Json.str "done") => pure (some .Done)
    | some (Json.str "cancelled") => pure (some .Cancelled)
    | some (Json.str "duplicate") => pure (some .Duplicate)
    | some (Json.str other) => throw (malformed s!"import record {sid}: unknown closeResolution '{other}' — use done | cancelled | duplicate")
    | some _ => throw (malformed s!"import record {sid}: \"closeResolution\" must be a string")
  let assignee ← optStrField j sid "assignee"
  let description ← optStrField j sid "description"
  let notes ← optStrField j sid "notes"
  let duplicateOf ← optStrField j sid "duplicateOf"
  let parent ← optStrField j sid "parent"
  let labels ← strListField j sid "labels"
  let blockedBy ← strListField j sid "blockedBy"
  let related ← strListField j sid "related"
  -- deferUntil: a present-but-unparseable value is malformed (unlike provenance)
  let deferUntil ← match (j.getObjVal? "deferUntil").toOption with
    | none | some Json.null => pure none
    | some (Json.str s) => match Time.epochMsOfIso? s with
      | some ms => pure (some ms)
      | none => throw (malformed s!"import record {sid}: \"deferUntil\" ('{s}') is not a canonical ISO-8601 UTC instant")
    | some _ => throw (malformed s!"import record {sid}: \"deferUntil\" must be a string")
  -- a closeResolution is "only when closed" (ADR-0005): require a matching closed
  -- status, fail-closed on a contradiction (e.g. status done + closeResolution
  -- cancelled, or a closeResolution on an open issue) — never silently coerce
  match closeRes with
  | some res =>
    if !decide (status = statusOfResolution res) then
      throw (malformed s!"import record {sid}: closeResolution is inconsistent with status — a closeResolution requires the matching closed status (done, or cancelled for cancelled/duplicate)")
  | none => pure ()
  -- provenance timestamps: lenient (fallback + disclose)
  let (createdAt, d1) := optInstantField j sid "createdAt"
  let (closedAt, d2) := optInstantField j sid "closedAt"
  let (claimedAt, d3) := optInstantField j sid "claimedAt"
  disc := disc ++ d1 ++ d2 ++ d3
  -- meta: the explicit object (fail-closed on a non-object), plus every unknown
  -- key under `import:<k>`
  let metaExplicit : List (String × String) ← match (j.getObjVal? "meta").toOption with
    | none | some Json.null => pure []
    | some mj => match mj.getObj?.toOption with
      | some o => pure (o.toArray.toList.map (fun (k, v) => (k, jsonToMetaStr v)))
      | none => throw (malformed s!"import record {sid}: \"meta\" must be an object")
  let unknownMeta : List (String × String) :=
    match j.getObj?.toOption with
    | some o => (o.toArray.toList.filter (fun (k, _) => k ∉ knownKeys)).map
        (fun (k, v) => (s!"import:{k}", jsonToMetaStr v))
    | none => []
  let rec0 : ImportRecord :=
    { sourceId := sid, title, status, priority, assignee, description, notes,
      labels, deferUntil, closeRes, duplicateOf, blockedBy, parent, related,
      metaKv := metaExplicit ++ unknownMeta, createdAt, closedAt, claimedAt, raw := line }
  return (rec0, disc)

/-! ### Building the seed op-log -/

private def parsedLine (op : WireOp) (st : Stamp) (actor : Option String) : String :=
  renderLine { v := op.recordVersion, op, stamp := st, actor }

/-- The full result of a build: the import replica's segment lines + a summary. -/
structure ImportResult where
  segmentReplica : String
  lines : List String
  issueCount : Nat
  opCount : Nat
  disclosures : List String

/-- Dedup `(key, value)` pairs by key, keeping the first occurrence (so the
    derived `ext:`/`import:source`/`duplicate-of` keys win over a colliding user
    meta key), then key-sort for a canonical, input-order-independent log. -/
private def dedupByKey (kvs : List (String × Option String)) : List (String × Option String) :=
  (kvs.foldl (fun acc (k, v) => if acc.any (·.1 == k) then acc else acc ++ [(k, v)]) [])
    |>.mergeSort (fun a b => decide (a.1 ≤ b.1))

/-- Build the seed op-log for parsed records (ADR-0005 §seed op-log). Records are
    ordered by source id (the stable ordinal for fallback timestamps); ids,
    replica, nonces, and timestamps are all deterministic, so re-import is
    byte-stable. A blockedBy/parent/related endpoint absent from the import is
    skipped and disclosed. -/
def buildSeed (opts : ImportOptions) (records : List (String × ImportRecord))
    (parseDisc : List String) : ImportResult :=
  let tag := opts.sourceTag
  -- stable order: by source id (deterministic ordinal for fallback times)
  let ordered := records.mergeSort (fun a b =>
    decide (a.1 < b.1 || (a.1 == b.1 && a.2.sourceId ≤ b.2.sourceId)))
  -- source fingerprint over the sorted (id, record-hash) manifest
  let manifest := String.intercalate "\n"
    (ordered.map (fun (f, r) => s!"{f}\t{r.sourceId}\t{Sha256.toHex (Sha256.digestString r.raw)}"))
  let replicaId := importReplicaId tag (Sha256.toHex (Sha256.digestString manifest))
  let replicaNat := (ofCrockford? replicaId).getD 0
  -- a present-source-id set for O(1) edge-endpoint resolution
  let present : Std.HashSet String := ordered.foldl (fun s (_, r) => s.insert r.sourceId) ∅
  let idOf (srcId : String) : String := importIssueId tag srcId
  let actor : Option String := some tag
  -- per record, with its ordinal for the fallback time
  let perRecord := ordered.zipIdx.map (fun (frk : (String × ImportRecord) × Nat) => Id.run do
    let r := frk.1.2
    let k := frk.2
    let id := idOf r.sourceId
    -- lifecycle: claim (assignee/in_progress) then close (terminal). A closed
    -- record with an assignee gets a claim too, so the assignee survives close.
    let wantsClaim := match r.status with
      | .InProgress => true
      | .Open => false
      | _ => r.assignee.isSome
    let createMs := r.createdAt.getD (fallbackBaseMs + k)
    -- close after claim after create (causality): clamp so the +0/+1/+2 logical
    -- bumps never invert under odd source timestamps (a claimedAt with no
    -- closedAt). The clamp can move a *supplied* instant, which is a value the
    -- record carried and the log then does not hold — disclosed below, never
    -- silent (ADR-0005 §deterministic timestamps).
    --
    -- The close follows the *claim* only when there is a claim op for it to
    -- follow. On a record that emits none, chaining it through `claimMs` would
    -- let the fallback assigned to an absent `claimedAt` — an instant no op in
    -- the log carries — push apart a `createdAt ≤ closedAt` pair the source got
    -- right. (Where a claim op *is* emitted its fallback is a real stamp, so it
    -- does order the close, and moving the close is then disclosed.)
    let claimMs := max (r.claimedAt.getD (fallbackBaseMs + k)) createMs
    let closeMs := max (r.closedAt.getD (fallbackBaseMs + k))
      (if wantsClaim then claimMs else createMs)
    let stamp (role : String) (hlc : Nat) : Stamp :=
      ⟨hlc, replicaNat, importNonce tag r.sourceId role id⟩
    -- create carries the scalars (status/assignee come from the lifecycle ops)
    let createWrites : ScalarWrites :=
      { title := some r.title, priority := some r.priority,
        description := r.description.map some,
        deferUntil := r.deferUntil.map some }
    let createOp := parsedLine (.create id createWrites) (stamp "create" (packHlc createMs 0)) actor
    -- meta: source ref + import marker + explicit/unknown meta + duplicate-of
    let metaPairs := dedupByKey
      ([(s!"ext:{tag}", some r.sourceId), ("import:source", some tag)]
       ++ r.metaKv.map (fun (k, v) => (k, some v))
       ++ (match r.duplicateOf with | some d => [("duplicate-of", some (idOf d))] | none => []))
    let metaOps := metaPairs.map (fun (k, v) =>
      parsedLine (.metaSet id k v) (stamp s!"meta:{k}" (packHlc createMs 0)) actor)
    -- disclose the assignee edge cases rather than silently dropping/inventing one
    let mut lifeDisc : List String := []
    match r.status with
    | .Open => if r.assignee.isSome then
        lifeDisc := [s!"import record {r.sourceId}: assignee dropped — an open issue cannot be assigned (assignee is set by a claim → in_progress)"]
    | .InProgress => if r.assignee.isNone then
        lifeDisc := [s!"import record {r.sourceId}: in_progress with no assignee — recorded the source tag '{tag}' as the assignee"]
    | _ => pure ()
    let claimOps := if wantsClaim then
        [parsedLine (.claim id (r.assignee.getD tag)) (stamp "claim" (packHlc claimMs 1)) actor]
      else []
    let closeOps := match r.closeRes, r.status with
      | some res, _ => [parsedLine (.close id res) (stamp "close" (packHlc closeMs 2)) actor]
      | none, .Done => [parsedLine (.close id .Done) (stamp "close" (packHlc closeMs 2)) actor]
      | none, .Cancelled => [parsedLine (.close id .Cancelled) (stamp "close" (packHlc closeMs 2)) actor]
      | none, _ => []
    -- What became of each *supplied* lifecycle instant. Three outcomes, and only
    -- the first is silent: a read surfaces it unchanged; the causality clamp
    -- moved it first; or no read surfaces it at all. The fallback assigned to an
    -- absent value carries nothing and stays silent whatever the clamp does.
    --
    -- The test is what a read *projects*, never merely which op was written.
    -- `claimedAt` is the stamp of a claim that no later `close` supersedes
    -- (ADR-0008), and the seed always orders its `close` after its `claim`, so a
    -- closed record's claim carries the assignee but projects no `claimedAt` —
    -- an op-emitted test would call that a survivor and say nothing about a
    -- value no reader can see. `closedAt` needs only its op, since the seed
    -- emits no `reopen` to supersede one.
    let claimedAtReadable := wantsClaim && closeOps.isEmpty
    -- Being unprojectable and being clamped are independent, so a record can be
    -- both. Reporting only the first would leave the reader a remedy that does
    -- not restore the instant: changing the status makes the field projectable
    -- and the clamp then moves it anyway.
    let instantDisc (field : String) (supplied : Option Nat) (recorded : Nat)
        (readable : Bool) (reads remedy : String) : List String :=
      match supplied with
      | none => []
      | some ms =>
        let moved := ms != recorded
        if !readable && moved then
          [s!"import record {r.sourceId}: {field} '{Time.isoOfEpochMs ms}' is not recorded — \
{field} reads {reads}, and this record's status leaves none; the create → claim → close order \
would also move it to '{Time.isoOfEpochMs recorded}'. {remedy} and supply \
createdAt ≤ claimedAt ≤ closedAt to keep the source instant"]
        else if !readable then
          [s!"import record {r.sourceId}: {field} '{Time.isoOfEpochMs ms}' is not recorded — \
{field} reads {reads}, and this record's status leaves none; {remedy} to keep it"]
        else if moved then
          [s!"import record {r.sourceId}: {field} '{Time.isoOfEpochMs ms}' precedes the instant it \
must follow — recorded as '{Time.isoOfEpochMs recorded}' so the create → claim → close order \
holds; supply createdAt ≤ claimedAt ≤ closedAt to keep the source instant"]
        else []
    -- The instant the *recommended* status would record, which is not always
    -- the one this record's current shape would. Closing an open record that
    -- carries an assignee earns it a claim op it does not have now, and that
    -- claim's stamp then orders the close — so a `closedAt` this record would
    -- keep can still be moved by the very change the remedy asks for. Comparing
    -- against the current shape would promise a preservation that following the
    -- advice does not deliver. `claimedAt` needs no such simulation: its own
    -- remedy is `in_progress`, under which the claim exists and its stamp is
    -- the `claimMs` already computed.
    let closedAtRecorded :=
      if closeOps.isEmpty then
        max (r.closedAt.getD (fallbackBaseMs + k))
          (if r.assignee.isSome then claimMs else createMs)
      else closeMs
    -- `createdAt` needs no arm: the create op is unconditional and nothing
    -- clamps it, so a supplied value always reaches the log as given.
    let timeDisc :=
      instantDisc "claimedAt" r.claimedAt claimMs claimedAtReadable
        "the stamp of a claim no later close supersedes (ADR-0008)"
        "set status to in_progress" ++
      instantDisc "closedAt" r.closedAt closedAtRecorded (!closeOps.isEmpty)
        "the close op's stamp" "set status to done or cancelled"
    -- notes: the JSONL `notes` field lowers to ONE synthetic immutable journal
    -- entry (ADR-0027/0005): a `note` op-role in the nonce preimage, the hlc
    -- from the record's createdAt like the other non-lifecycle seed ops, the
    -- note id minted from that stamp as usual. One value in, one entry out —
    -- the import format's `notes` is a single string.
    let noteOps := match r.notes with
      | some txt =>
        let nst := stamp "note" (packHlc createMs 0)
        [parsedLine (.noteAdd id (mintNoteId nst) txt) nst actor]
      | none => []
    -- labels
    let labelOps := r.labels.map (fun l =>
      parsedLine (.labelAdd id l) (stamp s!"label:{l}" (packHlc createMs 0)) actor)
    -- edges: only when the endpoint is present in the import
    let edgeOf (role : String) (e : Edge) := parsedLine (.depAdd e) (stamp role (packHlc createMs 0)) actor
    let mut edgeOps : List String := []
    let mut edgeDisc : List String := []
    for b in r.blockedBy do
      if present.contains b then edgeOps := edgeOps ++ [edgeOf s!"blocks:{b}" (idOf b, id, EdgeKind.Blocks)]
      else edgeDisc := edgeDisc ++ [s!"import record {r.sourceId}: blockedBy '{b}' is not in the import — edge skipped"]
    match r.parent with
    | some p =>
      if present.contains p then edgeOps := edgeOps ++ [edgeOf s!"parent:{p}" (idOf p, id, EdgeKind.Parent)]
      else edgeDisc := edgeDisc ++ [s!"import record {r.sourceId}: parent '{p}' is not in the import — edge skipped"]
    | none => pure ()
    for rel in r.related do
      if present.contains rel then
        let a := idOf rel
        let e : Edge := if decide (id ≤ a) then (id, a, EdgeKind.Related) else (a, id, EdgeKind.Related)
        edgeOps := edgeOps ++ [parsedLine (.relate e) (stamp s!"related:{rel}" (packHlc createMs 0)) actor]
      else edgeDisc := edgeDisc ++ [s!"import record {r.sourceId}: related '{rel}' is not in the import — edge skipped"]
    (createOp :: (metaOps ++ claimOps ++ closeOps ++ noteOps ++ labelOps ++ edgeOps),
     edgeDisc ++ lifeDisc ++ timeDisc))
  let lines := perRecord.flatMap (·.1)
  let edgeDiscs := perRecord.flatMap (·.2)
  { segmentReplica := replicaId, lines, issueCount := ordered.length,
    opCount := lines.length, disclosures := parseDisc ++ edgeDiscs }

/-! ### Granular resource bounds (ADR-0005 §two distinct safety gates)

A hostile or accidentally-enormous source is bounded field-by-field *before any
op is emitted* — a finer net than the coarse total-input bound the caller
enforces from file metadata. Each granular bound is a fixed constant, never
scaled by `--max` (that knob raises only the byte bounds: total input, and the
derived seed size below); only `--allow-large` disarms the granular net. With the
net armed, exceeding a bound fails closed (`force-required`, ADR-0008) after
collecting *every* violation in one pass: the message names the first few plus
the total, and `context.boundsViolations` carries the machine-readable list. With
`--allow-large`, the record imports *verbatim* — tl stores fields uncapped, only
rendering truncates (`Tl.Cli.Sanitize`) — with one disclosure per violation. The
byte bounds track the render bounds (single-line 1 KiB, multi-line 64 KiB); the
meta value is the one deliberate exception (4 KiB stored / 1 KiB rendered, since
the opaque channel may hold more than it displays). They measure the *raw stored*
bytes a resource bound must cap, so relative to the render sanitizer (which also
strips control bytes before truncating) they over-refuse, never under-refuse. A
parent *cycle* is never a bound violation (the kernel is total on cycles, ADR-0003): it
is disclosed and its edges kept, matching native `dep add`. -/

namespace Bounds

/-- Title and every stored single-line field (assignee, the source id): the
    `sanitizeSingle` render bound. -/
def singleLineBytes : Nat := 1024
/-- Description and notes: the `sanitizeMulti` render bound. -/
def multiLineBytes : Nat := 65536
/-- One label's bytes. -/
def labelBytes : Nat := 1024
/-- One meta key's bytes — checked on the *stored* key, so the derived
    `import:<k>` and `ext:<source>` forms count. -/
def metaKeyBytes : Nat := 1024
/-- One meta value's bytes. -/
def metaValueBytes : Nat := 4096
/-- Labels per record. -/
def labelsCount : Nat := 64
/-- Meta entries per record, counted pre-dedup and including the ≤3 derived keys
    (`ext:<tag>`, `import:source`, and `duplicate-of` when present). -/
def metaCount : Nat := 64
/-- Raw (pre-skip) outgoing edges per record: blockedBy + parent + related. -/
def edgesCount : Nat := 128
/-- Present-parent chain depth (ancestor levels above a record). -/
def parentDepth : Nat := 64
/-- The derived seed op-log's byte size is bounded at this multiple of the
    (possibly `--max`-raised) total-input bound — the importer amplifies the
    input into per-field ops. -/
def seedMultiplier : Nat := 4
/-- One raw input line's bytes, checked *before* JSON parsing so a pathological
    line cannot drive the parser unbounded. Generous over the largest record the
    granular net admits (~0.4 MiB). -/
def rawLineBytes : Nat := 2 * 1024 * 1024

end Bounds

/-- One exceeded granular bound: the offending record's source id, a stable
    machine `field` key, the measured `actual` and its `limit`, plus a
    ready-phrased human `detail`. -/
structure BoundViolation where
  record : String
  field : String
  actual : Nat
  limit : Nat
  detail : String
  deriving Repr

private def jnumB (n : Nat) : Json := Json.num ⟨Int.ofNat n, 0⟩

/-- The `context.boundsViolations` element (ADR-0020 machine-readable list). The
    human `detail` stays in the message/disclosure, not the machine list. -/
def BoundViolation.toJson (v : BoundViolation) : Json :=
  Json.mkObj [("record", Json.str v.record), ("field", Json.str v.field),
              ("actual", jnumB v.actual), ("limit", jnumB v.limit)]

/-- The granular bounds one record violates (empty when clean). Byte sizes are
    UTF-8; the meta count is pre-dedup incl. derived keys, the edge count is
    pre-skip. Offending values are never inlined into a message (they may be the
    very thing that is oversized) — fields are named positionally. -/
private def recordViolations (r : ImportRecord) : List BoundViolation :=
  let sid := r.sourceId
  let bytesV (field noun : String) (limit : Nat) (s : String) : Option BoundViolation :=
    let n := s.utf8ByteSize
    if n > limit then
      some { record := sid, field, actual := n, limit,
             detail := s!"{noun} is {n} bytes (max {limit})" }
    else none
  let countV (field noun : String) (limit actual : Nat) : Option BoundViolation :=
    if actual > limit then
      some { record := sid, field, actual, limit,
             detail := s!"{noun} count is {actual} (max {limit})" }
    else none
  let metaTotal := r.metaKv.length + 2 + (if r.duplicateOf.isSome then 1 else 0)
  let edgesTotal := r.blockedBy.length + r.related.length + (if r.parent.isSome then 1 else 0)
  let scalars : List (Option BoundViolation) :=
    [ bytesV "title" "title" Bounds.singleLineBytes r.title,
      r.assignee.bind (bytesV "assignee" "assignee" Bounds.singleLineBytes),
      bytesV "sourceId" "source id" Bounds.singleLineBytes sid,
      r.description.bind (bytesV "description" "description" Bounds.multiLineBytes),
      r.notes.bind (bytesV "notes" "notes" Bounds.multiLineBytes) ]
  let labelVs := r.labels.zipIdx.map (fun (l, i) =>
    bytesV "label" s!"label #{i + 1}" Bounds.labelBytes l)
  let metaKeyVs := r.metaKv.zipIdx.map (fun ((k, _), i) =>
    bytesV "metaKey" s!"meta key #{i + 1}" Bounds.metaKeyBytes k)
  let metaValVs := r.metaKv.zipIdx.map (fun ((_, v), i) =>
    bytesV "metaValue" s!"meta value #{i + 1}" Bounds.metaValueBytes v)
  let counts : List (Option BoundViolation) :=
    [ countV "labelsCount" "labels" Bounds.labelsCount r.labels.length,
      countV "metaCount" "meta entries" Bounds.metaCount metaTotal,
      countV "edgesCount" "edges" Bounds.edgesCount edgesTotal ]
  (scalars ++ labelVs ++ metaKeyVs ++ metaValVs ++ counts).filterMap id

/-- One BFS level of the parent-depth pass: assign `d` to every record in the
    frontier, then recurse on their present children at `d + 1`. `fuel` bounds the
    level count — a chain longer than the record count must repeat (a cycle), and
    a cycle's records never enter a frontier. Total work is O(n): each record sits
    in exactly one frontier, since it has ≤1 parent. -/
private def bfsDepth (childrenOf : Std.HashMap String (List String)) :
    Nat → List String → Nat → Std.HashMap String Nat → Std.HashMap String Nat
  | 0, _, _, acc => acc
  | _ + 1, [], _, acc => acc
  | fuel + 1, frontier, d, acc =>
    let acc' := frontier.foldl (fun m n => m.insert n d) acc
    let next := frontier.flatMap (fun n => childrenOf.getD n [])
    bfsDepth childrenOf fuel next (d + 1) acc'

/-- Ancestor depth for every record, plus the records on a parent cycle, in one
    O(n) pass over the functional parent graph (each record has ≤1 present
    parent). Roots — no parent, or a dangling one — get depth 0; a child is its
    parent's depth + 1. A record left without a depth is exactly one whose parent
    chain enters a cycle (it never reaches a root), reported separately. -/
private def parentDepths (records : List ImportRecord) :
    Std.HashMap String Nat × List String :=
  let present : Std.HashSet String := records.foldl (fun s r => s.insert r.sourceId) ∅
  let parentOf : Std.HashMap String String := records.foldl (fun m r =>
    match r.parent with
    | some p => if present.contains p then m.insert r.sourceId p else m
    | none => m) ∅
  let childrenOf : Std.HashMap String (List String) := records.foldl (fun m r =>
    match parentOf.get? r.sourceId with
    | some p => m.insert p (r.sourceId :: m.getD p [])
    | none => m) ∅
  let roots := records.filterMap (fun r =>
    if (parentOf.get? r.sourceId).isNone then some r.sourceId else none)
  let depths := bfsDepth childrenOf (records.length + 1) roots 0 ∅
  let cyclic := records.filterMap (fun r =>
    if (depths.get? r.sourceId).isNone then some r.sourceId else none)
  (depths, cyclic)

/-- Collect and adjudicate the granular bounds (ADR-0005). Fail-closed with the
    full violation list when the net is armed; verbatim-with-disclosures under
    `--allow-large`. Parent cycles are always disclosed, never a violation. The
    machine `context` list is capped (the honest `violationCount` is not), so a
    hostile input cannot balloon the error itself. -/
def checkBounds (opts : ImportOptions) (records : List (String × ImportRecord)) :
    Except Tl.Error (List String) :=
  let recs := records.map (·.2)
  let (depths, cyclic) := parentDepths recs
  let depthVs := recs.filterMap (fun r =>
    match depths.get? r.sourceId with
    | some d =>
      if d > Bounds.parentDepth then
        some ({ record := r.sourceId, field := "parentDepth", actual := d,
                limit := Bounds.parentDepth,
                detail := s!"parent chain is {d} levels deep (max {Bounds.parentDepth})" } : BoundViolation)
      else none
    | none => none)
  -- the operator-supplied `--source` tag is byte-invisible to the input/line
  -- bounds (it is a CLI flag, not file content) yet lands on every record as the
  -- derived `ext:<tag>` meta key and the `import:source` meta value — check both
  let tagKey := s!"ext:{opts.sourceTag}"
  let tagVs : List BoundViolation :=
    (if tagKey.utf8ByteSize > Bounds.metaKeyBytes then
       [{ record := "(--source)", field := "sourceTag", actual := tagKey.utf8ByteSize,
          limit := Bounds.metaKeyBytes,
          detail := s!"the derived meta key 'ext:<source>' is {tagKey.utf8ByteSize} bytes (max {Bounds.metaKeyBytes})" }]
     else []) ++
    (if opts.sourceTag.utf8ByteSize > Bounds.metaValueBytes then
       [{ record := "(--source)", field := "sourceTag", actual := opts.sourceTag.utf8ByteSize,
          limit := Bounds.metaValueBytes,
          detail := s!"the --source tag (stored as the 'import:source' value) is {opts.sourceTag.utf8ByteSize} bytes (max {Bounds.metaValueBytes})" }]
     else [])
  let violations := recs.flatMap recordViolations ++ depthVs ++ tagVs
  let cycleDisc : List String :=
    if cyclic.isEmpty then []
    else
      let shown := String.intercalate ", " (cyclic.take 5)
      let more := if cyclic.length > 5 then s!" and {cyclic.length - 5} more" else ""
      [s!"import: {cyclic.length} record(s) have a parent chain that enters a cycle ({shown}{more}) — edges kept; a cycle is reported by `tl dep cycles`, never a size bound"]
  if violations.isEmpty then
    .ok cycleDisc
  else if opts.allowLarge then
    let indiv := (violations.take 200).map (fun v =>
      s!"import record {v.record}: {v.detail} — imported verbatim (--allow-large); tl stores it uncapped, only rendering truncates")
    let tail := if violations.length > 200 then
        [s!"import: and {violations.length - 200} more field(s) over a bound, imported verbatim (--allow-large)"]
      else []
    .ok (cycleDisc ++ indiv ++ tail)
  else
    let shown := (violations.take 3).map (fun v => s!"record {v.record} {v.detail}")
    let more := if violations.length > 3 then s!"; and {violations.length - 3} more" else ""
    .error {
      code := .forceRequired,
      message := s!"import refused: {violations.length} field/resource bound(s) exceeded — {String.intercalate "; " shown}{more}. Pass --allow-large to import verbatim (tl stores fields uncapped; only rendering truncates), or split/trim the source.",
      context := [("violationCount", jnumB violations.length),
                  ("boundsViolations", Json.arr ((violations.take 100).map BoundViolation.toJson).toArray)] }

/-- The derived-seed byte bound (ADR-0005): the seed op-log may amplify the
    input, so its size is bounded at `seedMultiplier ×` the (possibly raised)
    total-input bound — armed unless `--allow-large`. Newlines count (one per
    line), matching what the caller writes. -/
def checkSeedSize (opts : ImportOptions) (result : ImportResult) : Except Tl.Error (List String) :=
  let seedBytes := result.lines.foldl (fun acc l => acc + l.utf8ByteSize + 1) 0
  let limit := Bounds.seedMultiplier * opts.maxBytes
  if seedBytes ≤ limit then .ok []
  else if opts.allowLarge then
    .ok [s!"import: the derived seed op-log is {seedBytes} bytes, over the {limit}-byte bound ({Bounds.seedMultiplier}× the {opts.maxBytes}-byte input bound) — written anyway (--allow-large)"]
  else
    .error {
      code := .forceRequired,
      message := s!"import refused: the derived seed op-log is {seedBytes} bytes, over the {limit}-byte bound ({Bounds.seedMultiplier}× the {opts.maxBytes}-byte input bound — import amplifies the input into per-field ops). Pass --allow-large to write it, or raise --max to lift both byte bounds together.",
      context := [("seedBytes", jnumB seedBytes), ("limit", jnumB limit)] }

end Tl.Import
