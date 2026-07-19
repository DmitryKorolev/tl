/-
`Tests.CodecTests` — the record↔Op codec round-trip corpus (ADR-0008).

Three layers of coverage:
- canonical lines pinned as exact bytes for every wire verb, checked
  `renderLine (decodeLine l) = l` (the on-disk forever surface);
- the pinned string-escaping classes (ADR-0008 §canonical form): `\"`, `\\`,
  `\n`, `\r`, tab (as `\\u0009` — not `\\t`), other control chars as lowercase
  `\\u00xx`, with U+007F, non-ASCII, emoji and `/` raw;
- fail-closed rows: one discrete assertion per malformed/unknown-version
  branch the decoder can take, each checking the stable error `code`.
-/
import Tl.Format.Codec
import Tl.Kernel.Apply
import Tests.Harness

namespace Tl.Tests

open Tl.Format
open Tl.Kernel
open Tl.Crdt
open Lean (Json)

/-- The shared test stamp/envelope (the SHA-256 mint-vector triple). -/
def tStamp : Stamp :=
  ⟨0x0000018d07f4c812, (ofCrockford? "0123456789abc").getD 0,
   (ofCrockford? "0123456789abcdefghjkmnpqrs").getD 0⟩

def tStampEarlier : Stamp := { tStamp with hlc := 0x0000018d07f4c811 }

/-- The canonical envelope prefix every test line shares. -/
def env (op : String) : String :=
  s!"\{\"v\":1,\"op\":\"{op}\",\"hlc\":\"0000018d07f4c812\"," ++
  "\"replica\":\"0123456789abc\",\"nonce\":\"0123456789abcdefghjkmnpqrs\"," ++
  "\"actor\":\"carol\","

def idA : String := "mefp30jkcmfvxa0e"
def idB : String := "0123456789abcdef"

def tagEarlier : String := "0000018d07f4c811.0123456789abc.0123456789abcdefghjkmnpqrs"
def tagLater : String := "0000018d07f4c812.0123456789abc.0123456789abcdefghjkmnpqrs"

/-- The note id minted from `tStamp` (= `tagLater`'s stamp): the handle a valid
    `noteRemove` observing `tagLater` must carry (ADR-0027, the decoder's own-tag
    check). -/
def noteHandleLater : String := mintNoteId tStamp

/-- One pinned canonical line per wire verb (payload keys in lexicographic
    order, observed arrays in stamp order — the canonical render). -/
def canonicalLines : List (String × String) :=
  [("create (title, priority)",
    env "create" ++ s!"\"id\":\"{idA}\",\"priority\":1,\"title\":\"Write the parser\"}"),
   ("create (full scalar seed; the legacy notes key rides the unknown bag)",
    env "create" ++ s!"\"assignee\":null,\"closeResolution\":null,\"deferUntil\":\"2026-06-15T09:00:00Z\",\"description\":\"body\",\"id\":\"{idA}\",\"notes\":null,\"priority\":0,\"slug\":\"write-parser\",\"status\":\"open\",\"title\":\"t\"}"),
   ("update (non-lifecycle scalars; the legacy notes key rides the unknown bag)",
    env "update" ++ s!"\"assignee\":\"dana\",\"id\":\"{idA}\",\"notes\":\"done part 1\",\"title\":\"Write the parser v2\"}"),
   ("claim",
    env "claim" ++ s!"\"assignee\":\"carol\",\"id\":\"{idA}\"}"),
   ("close (done)",
    env "close" ++ s!"\"closeResolution\":\"done\",\"id\":\"{idA}\",\"status\":\"done\"}"),
   ("close (duplicate ⇒ cancelled)",
    env "close" ++ s!"\"closeResolution\":\"duplicate\",\"id\":\"{idA}\",\"status\":\"cancelled\"}"),
   ("reopen",
    env "reopen" ++ s!"\"id\":\"{idA}\"}"),
   ("defer (with ms fraction)",
    env "defer" ++ s!"\"deferUntil\":\"2026-06-10T16:58:55.296Z\",\"id\":\"{idA}\"}"),
   ("undefer (explicit null clear)",
    env "undefer" ++ s!"\"deferUntil\":null,\"id\":\"{idA}\"}"),
   ("metaSet (value)",
    env "metaSet" ++ s!"\"id\":\"{idA}\",\"key\":\"duplicate-of\",\"value\":\"{idB}\"}"),
   ("metaSet (null clear)",
    env "metaSet" ++ s!"\"id\":\"{idA}\",\"key\":\"ext:beads\",\"value\":null}"),
   ("depAdd (blocks)",
    env "depAdd" ++ s!"\"from\":\"{idB}\",\"kind\":\"blocks\",\"to\":\"{idA}\"}"),
   ("relate",
    env "relate" ++ s!"\"from\":\"{idB}\",\"kind\":\"related\",\"to\":\"{idA}\"}"),
   ("depRemove (two observed tags, stamp order)",
    env "depRemove" ++ s!"\"from\":\"{idB}\",\"kind\":\"blocks\",\"observed\":[\"{tagEarlier}\",\"{tagLater}\"],\"to\":\"{idA}\"}"),
   ("unrelate",
    env "unrelate" ++ s!"\"from\":\"{idB}\",\"kind\":\"related\",\"observed\":[\"{tagEarlier}\"],\"to\":\"{idA}\"}"),
   ("labelAdd",
    env "labelAdd" ++ s!"\"id\":\"{idA}\",\"label\":\"type:bug\"}"),
   ("labelRemove",
    env "labelRemove" ++ s!"\"id\":\"{idA}\",\"label\":\"type:bug\",\"observed\":[\"{tagLater}\"]}"),
   ("unknown fields preserved in place (claim + future keys)",
    env "claim" ++ s!"\"assignee\":\"carol\",\"futureFlag\":\{\"nested\":[1,2]},\"id\":\"{idA}\",\"zzz\":true}"),
   ("noteAdd (v:2, handle minted from its own stamp)",
    (env "noteAdd").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"text\":\"progress: lexer done\"}"),
   ("noteRemove (v:2, own-tag observed)",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":[\"{tagLater}\"]}"),
   ("actor null is the canonical absent-actor form",
    "{\"v\":1,\"op\":\"reopen\",\"hlc\":\"0000018d07f4c812\"," ++
    "\"replica\":\"0123456789abc\",\"nonce\":\"0123456789abcdefghjkmnpqrs\"," ++
    s!"\"actor\":null,\"id\":\"{idA}\"}")]

def canonicalRoundTripTests : List Outcome :=
  canonicalLines.map (fun (name, line) =>
    match decodeLine line with
    | .ok p => checkEq name (renderLine p) line
    | .error e => { name, passed := false, msg := s!"decode failed: {e.message}" })

/-- The ADR-0008 escape classes, pinned as exact bytes through a full
    render→decode→render cycle. The title exercises every class: quote,
    backslash, LF, tab (renders `\\u0009`, not `\\t`), U+0001 (other
    control, lowercase `\\u00xx`), with é, 😀 and `/` raw. -/
def escapeTests : List Outcome :=
  let title := "a\"b\\c\nd\te" ++ String.singleton (Char.ofNat 1) ++ "fg é😀/h"
  let expectedLine := env "create" ++ s!"\"id\":\"{idA}\"," ++
    "\"title\":\"a\\\"b\\\\c\\nd\\u0009e\\u0001fg é😀/h\"}"
  let p : ParsedOp :=
    { v := 1, op := .create idA { title := some title }, stamp := tStamp,
      actor := some "carol" }
  let rendered := renderLine p
  [checkEq "escape classes render to the pinned bytes" rendered expectedLine,
   (match decodeLine rendered with
    | .ok q =>
      (match q.op with
       | .create _ w => checkEq "escaped title decodes back to the original" w.title (some title)
       | _ => { name := "escaped title decodes back", passed := false, msg := "wrong verb" })
    | .error e => { name := "escaped title decodes back", passed := false, msg := e.message }),
   (match decodeLine rendered with
    | .ok q => checkEq "escape round-trip is byte-stable" (renderLine q) rendered
    | .error e => { name := "escape round-trip", passed := false, msg := e.message })]

/-- CR must render as the short form `\r` (ADR-0008 pins `\n`/`\r` short,
    everything else below U+0020 as `\u00xx`), and U+007F passes through as a
    raw byte, never escaped. -/
def crEscapeTest : List Outcome :=
  let p : ParsedOp :=
    { v := 1, op := .create idA { title := some "x\ry" }, stamp := tStamp, actor := none }
  let del := Char.ofNat 127
  let pDel : ParsedOp :=
    { v := 1, op := .create idA { title := some (String.ofList ['x', del, 'y']) },
      stamp := tStamp, actor := none }
  [checkEq "CR renders as \\r"
    (renderLine p)
    (("{\"v\":1,\"op\":\"create\",\"hlc\":\"0000018d07f4c812\"," ++
      "\"replica\":\"0123456789abc\",\"nonce\":\"0123456789abcdefghjkmnpqrs\"," ++
      s!"\"actor\":null,\"id\":\"{idA}\",") ++ "\"title\":\"x\\ry\"}"),
   check "U+007F stays a raw byte (not \\u007f)"
     ((renderLine pDel).contains del
       && ((renderLine pDel).splitOn "\\u007f").length == 1
       && (match decodeLine (renderLine pDel) with
           | .ok q => renderLine q == renderLine pDel
           | .error _ => false))
     (renderLine pDel)]

/-- Decode-side fail-closed rows: `(name, line, expected code)`. -/
def failClosedRows : List (String × String × Tl.ErrorCode) :=
  [("v=3 is fail-closed newer", (env "create").replace "\"v\":1" "\"v\":3" ++ s!"\"id\":\"{idA}\"}",
    .unknownVersion),
   ("v=0 is malformed, not older", (env "create").replace "\"v\":1" "\"v\":0" ++ s!"\"id\":\"{idA}\"}",
    .malformedLine),
   ("unknown op kind", env "frobnicate" ++ s!"\"id\":\"{idA}\"}", .malformedLine),
   ("noteAdd at v:1 is malformed (no tl writer stamps it)",
    env "noteAdd" ++ s!"\"id\":\"{idA}\",\"note\":\"{idB}\",\"text\":\"x\"}", .malformedLine),
   ("noteRemove at v:1 is malformed",
    env "noteRemove" ++ s!"\"id\":\"{idA}\",\"note\":\"{idB}\",\"observed\":[\"{tagLater}\"]}",
    .malformedLine),
   ("noteAdd missing text is malformed",
    (env "noteAdd").replace "\"v\":1" "\"v\":2" ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\"}",
    .malformedLine),
   ("noteAdd with a malformed note handle is malformed",
    (env "noteAdd").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"NOT-A-HANDLE\",\"text\":\"x\"}", .malformedLine),
   -- finding 1: the handle must be the note id minted from the add's own stamp,
   -- else a foreign/hand-edited note could fold visible yet be un-removable
   ("noteAdd whose handle does not mint from its own stamp is malformed",
    (env "noteAdd").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{idB}\",\"text\":\"x\"}", .malformedLine),
   ("noteRemove missing observed is malformed",
    (env "noteRemove").replace "\"v\":1" "\"v\":2" ++ s!"\"id\":\"{idA}\",\"note\":\"{idB}\"}",
    .malformedLine),
   ("noteRemove with a malformed note handle is malformed",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"NOT-A-HANDLE\",\"observed\":[\"{tagLater}\"]}",
    .malformedLine),
   -- finding 2: the removal must observe exactly its own add-tag, or a crafted
   -- record could remove another entry / mass-remove. Empty, multi-tag, and
   -- own-tag-mismatch all fail closed.
   ("noteRemove empty observed is malformed (must name one tag)",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":[]}",
    .malformedLine),
   ("noteRemove multi-tag observed is malformed (no mass-remove)",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":[\"{tagEarlier}\",\"{tagLater}\"]}",
    .malformedLine),
   ("noteRemove observed tag not minting to the note handle is malformed (no cross-entry remove)",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":[\"{tagEarlier}\"]}",
    .malformedLine),
   -- finding 4: the observed-field decode branches (non-array, non-string
   -- entry, malformed tag string)
   ("noteRemove non-array observed is malformed",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":\"x\"}",
    .malformedLine),
   ("noteRemove non-string observed entry is malformed",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":[123]}",
    .malformedLine),
   ("noteRemove malformed observed tag is malformed",
    (env "noteRemove").replace "\"v\":1" "\"v\":2"
      ++ s!"\"id\":\"{idA}\",\"note\":\"{noteHandleLater}\",\"observed\":[\"junk\"]}",
    .malformedLine),
   ("unparseable JSON", "{\"v\":1,", .malformedLine),
   ("hlc too short", (env "create").replace "0000018d07f4c812" "0000018d07f4c81" ++ s!"\"id\":\"{idA}\"}",
    .malformedLine),
   ("hlc uppercase", (env "create").replace "0000018d07f4c812" "0000018D07F4C812" ++ s!"\"id\":\"{idA}\"}",
    .malformedLine),
   ("replica alias chars are non-canonical",
    (env "create").replace "0123456789abc" "0l23456789abc" ++ s!"\"id\":\"{idA}\"}", .malformedLine),
   ("replica first char above f (65th bit)",
    (env "create").replace "0123456789abc" "g123456789abc" ++ s!"\"id\":\"{idA}\"}", .malformedLine),
   ("nonce first char above 7 (129th bit)",
    (env "create").replace "0123456789abcdefghjkmnpqrs" "8123456789abcdefghjkmnpqrs" ++ s!"\"id\":\"{idA}\"}",
    .malformedLine),
   ("id wrong width", env "create" ++ "\"id\":\"abc\"}", .malformedLine),
   ("id with Crockford alias", env "create" ++ "\"id\":\"mefp30jkcmfvxaoe\"}", .malformedLine),
   ("missing id", env "create" ++ "\"title\":\"x\"}", .malformedLine),
   ("title must be a string", env "create" ++ s!"\"id\":\"{idA}\",\"title\":null}", .malformedLine),
   ("priority must be an integer", env "create" ++ s!"\"id\":\"{idA}\",\"priority\":\"high\"}",
    .malformedLine),
   ("priority float is malformed", env "create" ++ s!"\"id\":\"{idA}\",\"priority\":2.5}",
    .malformedLine),
   ("bad status enum", env "create" ++ s!"\"id\":\"{idA}\",\"status\":\"paused\"}", .malformedLine),
   ("claim without assignee", env "claim" ++ s!"\"id\":\"{idA}\"}", .malformedLine),
   ("close with mismatched status/resolution pair",
    env "close" ++ s!"\"closeResolution\":\"duplicate\",\"id\":\"{idA}\",\"status\":\"done\"}",
    .malformedLine),
   ("close without status", env "close" ++ s!"\"closeResolution\":\"done\",\"id\":\"{idA}\"}",
    .malformedLine),
   ("close with bad resolution",
    env "close" ++ s!"\"closeResolution\":\"wontfix\",\"id\":\"{idA}\",\"status\":\"cancelled\"}",
    .malformedLine),
   ("defer with non-canonical instant",
    env "defer" ++ s!"\"deferUntil\":\"2026-02-30T00:00:00Z\",\"id\":\"{idA}\"}", .malformedLine),
   ("defer missing Z", env "defer" ++ s!"\"deferUntil\":\"2026-06-15T09:00:00\",\"id\":\"{idA}\"}",
    .malformedLine),
   ("undefer without the explicit null", env "undefer" ++ s!"\"id\":\"{idA}\"}", .malformedLine),
   ("undefer with a value", env "undefer" ++ s!"\"deferUntil\":\"2026-06-15T09:00:00Z\",\"id\":\"{idA}\"}",
    .malformedLine),
   ("metaSet without value", env "metaSet" ++ s!"\"id\":\"{idA}\",\"key\":\"k\"}", .malformedLine),
   ("bad edge kind", env "depAdd" ++ s!"\"from\":\"{idB}\",\"kind\":\"requires\",\"to\":\"{idA}\"}",
    .malformedLine),
   ("observed must be an array",
    env "depRemove" ++ s!"\"from\":\"{idB}\",\"kind\":\"blocks\",\"observed\":\"{tagLater}\",\"to\":\"{idA}\"}",
    .malformedLine),
   ("observed tag malformed",
    env "depRemove" ++ s!"\"from\":\"{idB}\",\"kind\":\"blocks\",\"observed\":[\"junk\"],\"to\":\"{idA}\"}",
    .malformedLine),
   ("missing required envelope field",
    s!"\{\"v\":1,\"op\":\"reopen\",\"hlc\":\"0000018d07f4c812\",\"replica\":\"0123456789abc\",\"actor\":null,\"id\":\"{idA}\"}",
    .malformedLine)]

def failClosedTests : List Outcome :=
  failClosedRows.map (fun (name, line, code) =>
    match decodeLine line with
    | .error e =>
      if e.code = code then { name, passed := true }
      else { name, passed := false, msg := s!"expected {code.wire}, got {e.code.wire}: {e.message}" }
    | .ok _ => { name, passed := false, msg := "expected a decode error, got ok" })

/-- The pinned priority-clamp exception (vision §fields): out-of-range values
    clamp to 0–4 with a disclosure in `warnings`, and render clamped. -/
def clampTests : List Outcome :=
  let decodeP (line : String) : Option (ParsedOp × Fin 5) :=
    match decodeLine line with
    | .ok p => match p.op with
      | .create _ w => w.priority.map (p, ·)
      | _ => none
    | .error _ => none
  let high := env "create" ++ s!"\"id\":\"{idA}\",\"priority\":9}"
  let low := env "create" ++ s!"\"id\":\"{idA}\",\"priority\":-3}"
  [(match decodeP high with
    | some (p, prio) =>
      check "priority 9 clamps to 4 with a disclosure"
        (prio = (4 : Fin 5) && !p.warnings.isEmpty
          && ((renderLine p).splitOn "\"priority\":4").length == 2)
        s!"prio {prio}, warnings {p.warnings}"
    | none => { name := "priority 9 clamps to 4", passed := false, msg := "decode failed" }),
   (match decodeP low with
    | some (p, prio) =>
      check "priority -3 clamps to 0 with a disclosure"
        (prio = (0 : Fin 5) && !p.warnings.isEmpty)
        s!"prio {prio}, warnings {p.warnings}"
    | none => { name := "priority -3 clamps to 0", passed := false, msg := "decode failed" })]

/-- The verb→delta projection feeds the kernel fold correctly: a create →
    claim → close history materializes with the expected status/resolution,
    and the depAdd's edge is present. -/
def foldSmokeTests : List Outcome :=
  -- distinct, increasing HLCs so each later write genuinely wins by LWW
  let envAt (op hlc : String) : String :=
    (env op).replace "0000018d07f4c812" hlc
  let lines :=
    [envAt "create" "0000018d07f4c811" ++ s!"\"id\":\"{idA}\",\"title\":\"t\"}",
     envAt "depAdd" "0000018d07f4c812" ++ s!"\"from\":\"{idB}\",\"kind\":\"blocks\",\"to\":\"{idA}\"}",
     envAt "claim" "0000018d07f4c813" ++ s!"\"assignee\":\"carol\",\"id\":\"{idA}\"}",
     envAt "close" "0000018d07f4c814" ++ s!"\"closeResolution\":\"duplicate\",\"id\":\"{idA}\",\"status\":\"cancelled\"}"]
  match lines.mapM decodeLine with
  | .error e => [{ name := "fold smoke decode", passed := false, msg := e.message }]
  | .ok ps =>
    let s := Tl.Kernel.fold (ps.map ParsedOp.kernelOp)
    let d := s.issueData idA
    [check "folded status is cancelled (duplicate close wins by LWW)"
       (d.statusOf = Status.Cancelled) s!"got {repr d.statusOf}",
     check "folded closeResolution is duplicate"
       (d.closeResolution.value.getD none = some CloseResolution.Duplicate) "",
     check "folded assignee is carol"
       (d.assignee.value.getD none = some "carol") "",
     check "blocks edge is present"
       (s.blockersOf idA = [idB]) s!"got {repr (s.blockersOf idA)}"]

/-- Assignee is claim-only (ADR-0013): neither `create` nor `update` may set it
    (a record carrying it routes it to the unknown bag, never consumed into the
    op), and `reopen` clears it as part of closed→open. So assignee and status
    move together (claim sets both, reopen clears assignee + opens) and an
    open-but-assigned state is unreachable by construction. -/
def assigneeSemanticsTests : List Outcome :=
  let envAt (op hlc : String) : String := (env op).replace "0000018d07f4c812" hlc
  let createA := envAt "create" "0000018d07f4c810" ++ s!"\"assignee\":\"erin\",\"id\":\"{idA}\",\"status\":\"open\",\"title\":\"t\"}"
  let updLine := envAt "update" "0000018d07f4c813" ++ s!"\"assignee\":\"dana\",\"id\":\"{idA}\",\"title\":\"t2\"}"
  -- decode-gate: neither create nor update reads assignee into the op's writes
  let opAssigneeNone (line : String) : Bool := match decodeLine line with
    | .ok p => match p.op with | .create _ w | .update _ w => w.assignee.isNone | _ => false
    | .error _ => false
  let base :=
    [envAt "create" "0000018d07f4c811" ++ s!"\"id\":\"{idA}\",\"title\":\"t\"}",
     envAt "claim"  "0000018d07f4c812" ++ s!"\"assignee\":\"carol\",\"id\":\"{idA}\"}",
     updLine]
  let reopenLine := envAt "reopen" "0000018d07f4c814" ++ s!"\"id\":\"{idA}\"}"
  let assigneeOf (lines : List String) : Option (Option String) :=
    match lines.mapM decodeLine with
    | .error _ => none
    | .ok ps => some ((Tl.Kernel.fold (ps.map ParsedOp.kernelOp)).issueData idA |>.assignee.value.getD none)
  [check "create's assignee is routed to the unknown bag, not consumed into the op"
     (opAssigneeNone createA) "create.assignee was consumed into the op",
   check "update's assignee is routed to the unknown bag, not consumed into the op"
     (opAssigneeNone updLine) "update.assignee was consumed into the op",
   check "a create carrying assignee folds to an unassigned issue (no open+assigned by construction)"
     (assigneeOf [createA] == some none) s!"got {repr (assigneeOf [createA])}",
   check "an update carrying assignee does not change the materialized assignee (stays carol)"
     (assigneeOf base == some (some "carol")) s!"got {repr (assigneeOf base)}",
   check "reopen clears the assignee (closed→open drops the prior claim)"
     (assigneeOf (base ++ [reopenLine]) == some none) s!"got {repr (assigneeOf (base ++ [reopenLine]))}"]

/-- Literal identity vectors through the actual mint functions (finding 2):
    a fixed stamp → a hardcoded 16-char id, for both `mintIssueId` and
    `mintNoteId`. Unlike the SHA-256 worked vector (which recomputes the
    truncation inline over a hardcoded preimage), these run the shipped
    functions, so a change to `stampPreimage`'s component order, `mintId80`'s
    width/fold, or `mintNoteId`'s `"note:"` prefix — any silent id drift — fails
    here. The expected strings were generated with an independent
    `hashlib`+base32 script. -/
def identityVectorTests : List Outcome :=
  [checkEq "mintIssueId identity vector (fixed stamp → fixed id)"
     (mintIssueId tStamp) "mefp30jkcmfvxa0e",
   checkEq "mintNoteId identity vector (fixed stamp → fixed note id)"
     (mintNoteId tStamp) "6we29r21vvwm58mm",
   -- the two id spaces are disjoint on the same stamp (the domain prefix)
   check "issue-id and note-id of one stamp differ"
     (mintIssueId tStamp != mintNoteId tStamp)]

def codecTests : List Outcome :=
  canonicalRoundTripTests ++ escapeTests ++ crEscapeTest ++ failClosedTests
    ++ clampTests ++ foldSmokeTests ++ assigneeSemanticsTests ++ identityVectorTests

end Tl.Tests
