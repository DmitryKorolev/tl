/-
`Tl.Format.Codec` — the record↔Op codec (ADR-0008 §record op kinds).

The decode target is `ParsedOp`, not a bare kernel `Op`: a bare `Op` cannot
round-trip — `edgeRemove`/`labelRemove` carry no stamp, and six wire verbs
collapse onto `setFields`. `ParsedOp` therefore carries the typed wire
operation (`WireOp`, one constructor per ADR-0008 verb with exactly its
payload, so a verb/payload mismatch is unrepresentable), the envelope `Stamp`,
the `actor`, and the preserve-unknown bag; the kernel `Op` is a *projection*
(`WireOp.toOp`), which is the executable form of the ADR-0008 verb→delta
table.

The codec covers the full v1 verb enum, not just the verbs the stage-1 CLI
emits — an unknown-op refusal must mean a genuinely foreign kind, never an
unbuilt stage-2 verb (docs/codebase-map.md). Decode is strict about canonical
encodings (exact widths, lowercase, no Crockford aliasing, in-range values) —
fail-closed `malformed-line`/`unknown-version`, segment-scoped at the Store
layer. Out-of-range `priority` is the pinned exception: it clamps to 0–4 with
a disclosure (vision §fields), carried in `warnings` (never rendered).

Tested I/O shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Tl.Error
import Tl.Format.Record
import Tl.Format.Crockford
import Tl.Format.Time
import Tl.Format.Version
import Tl.Clock.Hlc
import Tl.Kernel.Op

namespace Tl.Format

open Lean (Json)
open Tl.Kernel
open Tl.Crdt

/-! ## Wire enum strings -/

/-- Stored-status wire strings (vision §fields). -/
def statusWire : Status → String
  | .Open => "open"
  | .InProgress => "in_progress"
  | .Done => "done"
  | .Cancelled => "cancelled"

def statusOfWire? : String → Option Status
  | "open" => some .Open
  | "in_progress" => some .InProgress
  | "done" => some .Done
  | "cancelled" => some .Cancelled
  | _ => none

/-- `closeResolution` wire strings (ADR-0008). -/
def resolutionWire : CloseResolution → String
  | .Done => "done"
  | .Cancelled => "cancelled"
  | .Duplicate => "duplicate"

def resolutionOfWire? : String → Option CloseResolution
  | "done" => some .Done
  | "cancelled" => some .Cancelled
  | "duplicate" => some .Duplicate
  | _ => none

/-- Edge-kind wire strings (ADR-0003). -/
def edgeKindWire : EdgeKind → String
  | .Blocks => "blocks"
  | .Parent => "parent"
  | .Related => "related"

def edgeKindOfWire? : String → Option EdgeKind
  | "blocks" => some .Blocks
  | "parent" => some .Parent
  | "related" => some .Related
  | _ => none

/-- The stored status a close resolution sets (`duplicate` ⇒ `cancelled`,
    vision §fields) — derived, so the wire pair can never disagree on render. -/
def statusOfResolution : CloseResolution → Status
  | .Done => .Done
  | .Cancelled => .Cancelled
  | .Duplicate => .Cancelled

/-! ## Canonical identity encodings (ADR-0007/0008) -/

/-- The packed HLC as its 16-lowercase-hex wire form. -/
def hlcHex (n : Nat) : String := Tl.Clock.Hlc.toHex ⟨n / 2 ^ 16, n % 2 ^ 16⟩

/-- A canonical bare issue id: exactly 16 canonical Crockford chars (no
    aliasing, no case-folding — the log stores canonical bytes only). -/
def validId (s : String) : Bool :=
  s.length = 16 && match ofCrockford? s with
    | some v => toCrockford v 16 = s
    | none => false

private def malformed (msg : String) : Tl.Error :=
  .mk' .malformedLine
    (msg ++ " — not a valid v1 record; repair the line or rerun the read with --skip-bad")

/-- Decode the envelope triple, strictly canonical: 16 lowercase hex; 13/26
    canonical Crockford chars; replica < 2⁶⁴ and nonce < 2¹²⁸ (the spare
    high-bit headroom must be zero — first chars `0`-`f` / `0`-`7`, ADR-0007). -/
def decodeStamp (hlc replica nonce : String) : Except Tl.Error Stamp := do
  let some h := Tl.Clock.Hlc.ofHex? hlc
    | throw (malformed s!"'hlc' must be 16 lowercase hex chars (got '{hlc}')")
  let some r := ofCrockford? replica
    | throw (malformed s!"'replica' is not Crockford base32 (got '{replica}')")
  unless replica.length = 13 && toCrockford r 13 = replica do
    throw (malformed s!"'replica' must be 13 canonical Crockford chars (got '{replica}')")
  unless decide (r < 2 ^ 64) do
    throw (malformed s!"'replica' exceeds 64 bits (first char above 'f': '{replica}')")
  let some n := ofCrockford? nonce
    | throw (malformed s!"'nonce' is not Crockford base32 (got '{nonce}')")
  unless nonce.length = 26 && toCrockford n 26 = nonce do
    throw (malformed s!"'nonce' must be 26 canonical Crockford chars (got '{nonce}')")
  unless decide (n < 2 ^ 128) do
    throw (malformed s!"'nonce' exceeds 128 bits (first char above '7': '{nonce}')")
  return ⟨h.pack, r, n⟩

/-- The canonical OR-Set add-tag string `"<hlc>.<replica>.<nonce>"` (ADR-0008). -/
def tagOfStamp (st : Stamp) : String :=
  s!"{hlcHex st.hlc}.{toCrockford st.replica 13}.{toCrockford st.nonce 26}"

/-- Parse an add-tag string (same canonical strictness as the envelope). -/
def stampOfTag (s : String) : Except Tl.Error Stamp :=
  match s.splitOn "." with
  | [h, r, n] => decodeStamp h r n
  | _ => throw (malformed s!"'observed' tag must be '<hlc>.<replica>.<nonce>' (got '{s}')")

/-! ## The typed wire operation -/

/-- One constructor per ADR-0008 wire verb, carrying exactly its payload.
    `close` stores only the resolution — the paired stored-status write is
    derived (`statusOfResolution`), so the two can never disagree; `claim`'s
    `status=in_progress` and `reopen`'s `status=open` + resolution-clear are
    likewise derived in `toOp`. -/
inductive WireOp where
  | create (id : IssueId) (writes : ScalarWrites)
  | update (id : IssueId) (writes : ScalarWrites)
  | claim (id : IssueId) (assignee : String)
  | close (id : IssueId) (resolution : CloseResolution)
  | reopen (id : IssueId)
  | defer (id : IssueId) (untilMs : Instant)
  | undefer (id : IssueId)
  | metaSet (id : IssueId) (key : String) (value : Option String)
  | depAdd (e : Edge)
  | relate (e : Edge)
  | depRemove (e : Edge) (observed : FinSet Stamp)
  | unrelate (e : Edge) (observed : FinSet Stamp)
  | labelAdd (id : IssueId) (label : Label)
  | labelRemove (id : IssueId) (label : Label) (observed : FinSet Stamp)

namespace WireOp

/-- The wire `op` string (the ADR-0008 closed enum). -/
def wire : WireOp → String
  | .create .. => "create"
  | .update .. => "update"
  | .claim .. => "claim"
  | .close .. => "close"
  | .reopen .. => "reopen"
  | .defer .. => "defer"
  | .undefer .. => "undefer"
  | .metaSet .. => "metaSet"
  | .depAdd .. => "depAdd"
  | .relate .. => "relate"
  | .depRemove .. => "depRemove"
  | .unrelate .. => "unrelate"
  | .labelAdd .. => "labelAdd"
  | .labelRemove .. => "labelRemove"

/-- `update` writes only non-lifecycle, non-assignee scalars (ADR-0008: the
    lifecycle status/time fields use the distinguished verbs; assignee is
    claim-only, set by `claim` and cleared by `reopen` — ADR-0013) — enforced
    here as well as at decode, so a hand-built value folds exactly as it renders.
    Changing what this strips bumps `Tl.Store.cacheVersion`. -/
def stripLifecycle (w : ScalarWrites) : ScalarWrites :=
  { w with status := none, deferUntil := none, closeResolution := none, assignee := none }

/-- The ADR-0008 verb→delta table, executable: project the kernel `Op`. A change
    to this projection's classification must bump `Tl.Store.cacheVersion` — the
    fold cache is keyed on these semantics (Tl/Store/Cache.lean header). -/
def toOp (w : WireOp) (st : Stamp) : Op :=
  match w with
  | .create id writes => .create id st writes
  | .update id writes => .setFields id st (stripLifecycle writes)
  | .claim id assignee =>
      .setFields id st { status := some .InProgress, assignee := some (some assignee) }
  | .close id res =>
      .setFields id st { status := some (statusOfResolution res),
                         closeResolution := some (some res) }
  | .reopen id =>
      -- reopen is the inverse of close: it returns to open and clears BOTH the
      -- resolution and the assignee, since the prior owner's claim ended with the
      -- close (ADR-0008 reopen delta + ADR-0013). Changing this projection bumps
      -- `Tl.Store.cacheVersion`.
      .setFields id st { status := some .Open, closeResolution := some none,
                         assignee := some none }
  | .defer id untilMs => .setFields id st { deferUntil := some (some untilMs) }
  | .undefer id => .setFields id st { deferUntil := some none }
  | .metaSet id key value => .metaSet id st key value
  | .depAdd e => .edgeAdd e st
  | .relate e => .edgeAdd e st
  | .depRemove e obs => .edgeRemove e obs
  | .unrelate e obs => .edgeRemove e obs
  | .labelAdd id label => .labelAdd id label st
  | .labelRemove id label obs => .labelRemove id label obs

end WireOp

/-! ## The parsed model -/

/-- The parsed record: typed wire op + envelope identity + provenance +
    preserve-unknown bag. `warnings` carries decode-time disclosures (the
    priority clamp) for the caller's stderr; it is never rendered. -/
structure ParsedOp where
  v : Nat
  op : WireOp
  stamp : Stamp
  actor : Option String
  unknown : List (String × Json) := []
  warnings : List String := []

/-- The kernel delta this record folds as. -/
def ParsedOp.kernelOp (p : ParsedOp) : Op := p.op.toOp p.stamp

/-! ## Decode -/

private def field? (fs : List (String × Json)) (k : String) : Option Json :=
  (fs.find? (·.1 = k)).map (·.2)

private def reqStr (fs : List (String × Json)) (k : String) : Except Tl.Error String := do
  let some j := field? fs k
    | throw (malformed s!"missing required '{k}' field")
  match j.getStr? with
  | .ok s => return s
  | .error _ => throw (malformed s!"'{k}' must be a string")

/-- A nullable string field: `null` is an explicit clear, distinct from
    absent (ADR-0002/0008). -/
private def strOrNull (k : String) (j : Json) : Except Tl.Error (Option String) :=
  match j with
  | Json.null => return none
  | Json.str s => return (some s)
  | _ => throw (malformed s!"'{k}' must be a string or null")

private def reqId (fs : List (String × Json)) (k : String := "id") :
    Except Tl.Error IssueId := do
  let s ← reqStr fs k
  unless validId s do
    throw (malformed s!"'{k}' must be a bare 16-char canonical Crockford id (got '{s}')")
  return s

private def reqEdge (fs : List (String × Json)) : Except Tl.Error Edge := do
  let f ← reqId fs "from"
  let t ← reqId fs "to"
  let ks ← reqStr fs "kind"
  let some k := edgeKindOfWire? ks
    | throw (malformed s!"'kind' must be blocks|parent|related (got '{ks}')")
  return (f, t, k)

private def reqObserved (fs : List (String × Json)) :
    Except Tl.Error (FinSet Stamp) := do
  let some j := field? fs "observed"
    | throw (malformed "missing required 'observed' field")
  let arr ← match j.getArr? with
    | .ok a => pure a
    | .error _ => throw (malformed "'observed' must be an array of add-tag strings")
  arr.foldlM (fun acc tj => do
    let ts ← match tj.getStr? with
      | .ok s => pure s
      | .error _ => throw (malformed "'observed' entries must be strings")
    let st ← stampOfTag ts
    return FinSet.union acc (FinSet.singleton st)) FinSet.empty

/-- Decode a scalar field set (the `create`/`update` payloads). `lifecycle`
    admits the lifecycle fields (`status`/`deferUntil`/`closeResolution`) — true
    only for `create`'s initial seed; `update` leaves them to the distinguished
    verbs. `assignee` is read by neither: it is claim-only (`claim`/`claim --steal`
    set it, `reopen` clears it — ADR-0013), so a `create` or `update` record
    carrying it keeps it in the unknown bag instead (ADR-0008), and it is never
    seeded onto an open issue (which would forge a no-claim assignee). Returns the
    writes plus clamp warnings. -/
def decodeScalars (fs : List (String × Json)) (lifecycle : Bool) :
    Except Tl.Error (ScalarWrites × List String) := do
  let mut w : ScalarWrites := {}
  let mut warns : List String := []
  if let some j := field? fs "title" then
    match j.getStr? with
    | .ok s => w := { w with title := some s }
    | .error _ => throw (malformed "'title' must be a string")
  if let some j := field? fs "priority" then
    match j.getInt? with
    | .ok i =>
      let n : Nat := (max i 0).toNat
      let p : Fin 5 := ⟨min n 4, Nat.lt_succ_of_le (Nat.min_le_right n 4)⟩
      if i < 0 || 4 < i then
        warns := warns ++ [s!"priority {i} out of range; clamped to {p.val} (0-4)"]
      w := { w with priority := some p }
    | .error _ => throw (malformed "'priority' must be an integer")
  -- `assignee` is intentionally not read here (claim-only, ADR-0013) — a create/
  -- update record carrying it preserves it in the unknown bag, never applied.
  if let some j := field? fs "description" then
    w := { w with description := some (← strOrNull "description" j) }
  -- `notes` is no longer a scalar payload key (ADR-0027): on a legacy record
  -- it is not consumed here, so it routes to the preserve-unknown bag —
  -- preserved verbatim on any rewrite, never materialized.
  if let some j := field? fs "slug" then
    w := { w with slug := some (← strOrNull "slug" j) }
  if lifecycle then
    if let some j := field? fs "status" then
      let s ← match j.getStr? with
        | .ok s => pure s
        | .error _ => throw (malformed "'status' must be a string")
      let some st := statusOfWire? s
        | throw (malformed s!"'status' must be open|in_progress|done|cancelled (got '{s}')")
      w := { w with status := some st }
    if let some j := field? fs "deferUntil" then
      match ← strOrNull "deferUntil" j with
      | none => w := { w with deferUntil := some none }
      | some s =>
        let some ms := Time.epochMsOfIso? s
          | throw (malformed s!"'deferUntil' must be a canonical ISO-8601 UTC instant (got '{s}')")
        w := { w with deferUntil := some (some ms) }
    if let some j := field? fs "closeResolution" then
      match ← strOrNull "closeResolution" j with
      | none => w := { w with closeResolution := some none }
      | some s =>
        let some res := resolutionOfWire? s
          | throw (malformed s!"'closeResolution' must be done|cancelled|duplicate (got '{s}')")
        w := { w with closeResolution := some (some res) }
  return (w, warns)

/-- The payload keys each verb consumes; everything else in the record is
    preserved verbatim in the unknown bag (additive evolution, ADR-0008). -/
def consumedKeys : String → List String
  | "create" => ["id", "title", "status", "priority", "description",
                 "slug", "deferUntil", "closeResolution"]
  | "update" => ["id", "title", "priority", "description", "slug"]
  | "claim" => ["id", "assignee"]
  | "close" => ["id", "status", "closeResolution"]
  | "reopen" => ["id"]
  | "defer" | "undefer" => ["id", "deferUntil"]
  | "metaSet" => ["id", "key", "value"]
  | "depAdd" | "relate" => ["from", "to", "kind"]
  | "depRemove" | "unrelate" => ["from", "to", "kind", "observed"]
  | "labelAdd" => ["id", "label"]
  | "labelRemove" => ["id", "label", "observed"]
  | _ => []

/-- Decode a parsed `Record` into the typed model. Fail-closed: an unknown
    `op` kind is malformed (a new kind requires a `v` bump, ADR-0008
    §versioning, so within v1 it can only be damage or a rule violation); a
    newer `v` is `unknown-version`. -/
def decode (r : Record) : Except Tl.Error ParsedOp := do
  checkVersion r.v
  let stamp ← decodeStamp r.hlc r.replica r.nonce
  let fs := r.fields
  let (op, warnings) ← (match r.op with
    | "create" => do
        let id ← reqId fs
        let (w, warns) ← decodeScalars fs (lifecycle := true)
        pure (WireOp.create id w, warns)
    | "update" => do
        let id ← reqId fs
        let (w, warns) ← decodeScalars fs (lifecycle := false)
        pure (WireOp.update id w, warns)
    | "claim" => do
        let id ← reqId fs
        pure (.claim id (← reqStr fs "assignee"), [])
    | "close" => do
        let id ← reqId fs
        let rs ← reqStr fs "closeResolution"
        let some res := resolutionOfWire? rs
          | throw (malformed s!"'closeResolution' must be done|cancelled|duplicate (got '{rs}')")
        let ss ← reqStr fs "status"
        unless ss = statusWire (statusOfResolution res) do
          throw (malformed
            s!"close pairs closeResolution '{rs}' with status '{statusWire (statusOfResolution res)}', got '{ss}'")
        pure (.close id res, [])
    | "reopen" => do
        pure (.reopen (← reqId fs), [])
    | "defer" => do
        let id ← reqId fs
        let s ← reqStr fs "deferUntil"
        let some ms := Time.epochMsOfIso? s
          | throw (malformed s!"'deferUntil' must be a canonical ISO-8601 UTC instant (got '{s}')")
        pure (.defer id ms, [])
    | "undefer" => do
        let id ← reqId fs
        match field? fs "deferUntil" with
        | some Json.null => pure (.undefer id, [])
        | some _ => throw (malformed "undefer's 'deferUntil' must be null (the explicit clear)")
        | none => throw (malformed "undefer must carry the explicit 'deferUntil': null clear")
    | "metaSet" => do
        let id ← reqId fs
        let key ← reqStr fs "key"
        let some j := field? fs "value"
          | throw (malformed "missing required 'value' field (null = clear)")
        pure (.metaSet id key (← strOrNull "value" j), [])
    | "depAdd" => do pure (.depAdd (← reqEdge fs), [])
    | "relate" => do pure (.relate (← reqEdge fs), [])
    | "depRemove" => do pure (.depRemove (← reqEdge fs) (← reqObserved fs), [])
    | "unrelate" => do pure (.unrelate (← reqEdge fs) (← reqObserved fs), [])
    | "labelAdd" => do
        pure (.labelAdd (← reqId fs) (← reqStr fs "label"), [])
    | "labelRemove" => do
        pure (.labelRemove (← reqId fs) (← reqStr fs "label") (← reqObserved fs), [])
    | other =>
        throw (malformed s!"unknown op kind '{other}' (the v1 enum is closed; a new kind requires a v bump)")
    : Except Tl.Error (WireOp × List String))
  let consumed := consumedKeys r.op
  return { v := r.v, op, stamp, actor := r.actor,
           unknown := fs.filter (fun (k, _) => k ∉ consumed), warnings }

/-! ## Render -/

private def jnum (n : Nat) : Json := Json.num ⟨Int.ofNat n, 0⟩

private def jStrOrNull : Option String → Json
  | some s => Json.str s
  | none => Json.null

/-- The scalar payload fields a `create`/`update` carries — exactly the
    explicit writes, never the seeded defaults (those are delta-time,
    `Op.createData`). -/
def scalarFields (w : ScalarWrites) : List (String × Json) :=
  ([w.title.map (fun t => ("title", Json.str t)),
    w.status.map (fun s => ("status", Json.str (statusWire s))),
    w.priority.map (fun p => ("priority", jnum p.val)),
    w.assignee.map (fun a => ("assignee", jStrOrNull a)),
    w.description.map (fun d => ("description", jStrOrNull d)),
    w.slug.map (fun s => ("slug", jStrOrNull s)),
    w.deferUntil.map (fun d =>
      ("deferUntil", jStrOrNull (d.map Time.isoOfEpochMs))),
    w.closeResolution.map (fun r =>
      ("closeResolution", jStrOrNull (r.map resolutionWire)))]).filterMap id

private def edgeFields (e : Edge) : List (String × Json) :=
  let (f, t, k) := e
  [("from", Json.str f), ("to", Json.str t), ("kind", Json.str (edgeKindWire k))]

private def observedField (obs : FinSet Stamp) : String × Json :=
  ("observed", Json.arr (AMap.keys obs |>.map (fun st => Json.str (tagOfStamp st))).toArray)

/-- The verb-specific payload fields (before merging the unknown bag). -/
def payloadFields : WireOp → List (String × Json)
  | .create id w => ("id", Json.str id) :: scalarFields w
  | .update id w => ("id", Json.str id) :: scalarFields (WireOp.stripLifecycle w)
  | .claim id a => [("id", Json.str id), ("assignee", Json.str a)]
  | .close id res =>
      [("id", Json.str id),
       ("status", Json.str (statusWire (statusOfResolution res))),
       ("closeResolution", Json.str (resolutionWire res))]
  | .reopen id => [("id", Json.str id)]
  | .defer id ms => [("id", Json.str id), ("deferUntil", Json.str (Time.isoOfEpochMs ms))]
  | .undefer id => [("id", Json.str id), ("deferUntil", Json.null)]
  | .metaSet id k v => [("id", Json.str id), ("key", Json.str k), ("value", jStrOrNull v)]
  | .depAdd e => edgeFields e
  | .relate e => edgeFields e
  | .depRemove e obs => edgeFields e ++ [observedField obs]
  | .unrelate e obs => edgeFields e ++ [observedField obs]
  | .labelAdd id l => [("id", Json.str id), ("label", Json.str l)]
  | .labelRemove id l obs =>
      [("id", Json.str id), ("label", Json.str l), observedField obs]

/-- Render back to the wire `Record`: envelope re-encoded from the stamp
    (canonical encodings are deterministic), payload + unknown merged in one
    lexicographic key order (ADR-0008 §canonical form). -/
def render (p : ParsedOp) : Record :=
  let fields := payloadFields p.op ++ p.unknown
  { v := p.v
    op := p.op.wire
    hlc := hlcHex p.stamp.hlc
    replica := toCrockford p.stamp.replica 13
    nonce := toCrockford p.stamp.nonce 26
    actor := p.actor
    fields := fields.mergeSort (fun a b => decide (a.1 ≤ b.1)) }

/-- Decode one JSONL line (parse failure ⇒ `malformed-line`). A change to how a
    line is classified into a `ParsedOp` must bump `Tl.Store.cacheVersion`
    (Cache.lean header). -/
def decodeLine (line : String) : Except Tl.Error ParsedOp :=
  match Record.parse line with
  | .ok r => decode r
  | .error e => throw (malformed s!"unparseable record: {e}")

/-- Render one canonical JSONL line (no trailing newline). -/
def renderLine (p : ParsedOp) : String := (render p).render

end Tl.Format
