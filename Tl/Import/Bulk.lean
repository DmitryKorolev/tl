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

/-- An optional ISO-8601 UTC instant field: absent ⇒ `none`; present-but-
    unparseable ⇒ `none` with a disclosure (the caller assigns the fallback). -/
private def optInstantField (j : Json) (sid k : String) : Option Nat × List String :=
  match j.getObjVal? k with
  | .ok (Json.str s) =>
    match Time.epochMsOfIso? s with
    | some ms => (some ms, [])
    | none => (none, [s!"import record {sid}: \"{k}\" ('{s}') is not a canonical ISO-8601 UTC instant — assigned a deterministic fallback time"])
  | _ => (none, [])

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
  renderLine { v := supportedVersion, op, stamp := st, actor }

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
    let createMs := r.createdAt.getD (fallbackBaseMs + k)
    let claimMs := max (r.claimedAt.getD (fallbackBaseMs + k)) createMs
    -- close after claim after create (causality): clamp so the +0/+1/+2 logical
    -- bumps never invert under odd source timestamps (a claimedAt with no closedAt)
    let closeMs := max (r.closedAt.getD (fallbackBaseMs + k)) claimMs
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
    -- lifecycle: claim (assignee/in_progress) then close (terminal). A closed
    -- record with an assignee gets a claim too, so the assignee survives close.
    let wantsClaim := match r.status with
      | .InProgress => true
      | .Open => false
      | _ => r.assignee.isSome
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
    (createOp :: (metaOps ++ claimOps ++ closeOps ++ labelOps ++ edgeOps), edgeDisc ++ lifeDisc))
  let lines := perRecord.flatMap (·.1)
  let edgeDiscs := perRecord.flatMap (·.2)
  { segmentReplica := replicaId, lines, issueCount := ordered.length,
    opCount := lines.length, disclosures := parseDisc ++ edgeDiscs }

end Tl.Import
