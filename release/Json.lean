/-
Typed JSON access and deterministic rendering for `tlrelease`.

Two jobs, both of which the shell did badly.

**Reading.** Every accessor returns `Except String`, and the message names the
field and the file rather than the failure. The Python this replaces raised
uncaught exceptions on a malformed `release/identity.json`, a manifest with no
`assets` key, and a non-JSON manifest — the operator got a traceback, which is
the opposite of ADR-0008's discipline that a message says what to do next.
Nothing here throws: parsed external data enters through `Except` and only
validated values reach a decision.

**Writing.** `render` is byte-for-byte what Python's
`json.dump(obj, indent=2, sort_keys=True)` followed by a newline produces, and
that is deliberate rather than nostalgic. Two consumers need it: the manifest
and the SBOM are hashed into `SHA256SUMS` and signed, so their bytes must be a
function of their content and nothing else — no map iteration order, no
timestamp; and while the shell generators are still in the tree they serve as
differential oracles, which is an exact comparison if the bytes match and an
argument about formatting if they do not.

`Lean.Json`'s own `pretty` is not that format, so this module renders instead
of delegating. Object keys come out sorted because `Json.obj` is an ordered
map over `String` and Lean's ordering agrees with Python's on the ASCII keys
these documents use; `Tests/ReleaseToolTests.lean` pins the exact bytes.
-/
import Lean.Data.Json

namespace Release

open Lean (Json JsonNumber)

/-! ## Reading -/

/-- Where a value was expected, for a message a human can act on: the document,
    then the path inside it. -/
structure Cursor where
  document : String
  path : List String := []
  deriving Inhabited

def Cursor.at (cursor : Cursor) (step : String) : Cursor :=
  { cursor with path := cursor.path ++ [step] }

def Cursor.render (cursor : Cursor) : String :=
  if cursor.path.isEmpty then cursor.document
  else s!"{cursor.document} at {String.intercalate "." cursor.path}"

def Cursor.fail (cursor : Cursor) (what : String) : Except String α :=
  .error s!"{cursor.render}: {what}"

/-- Parse a whole document. The message carries the file, because the operator
    is looking at a pipeline log and not at a REPL. -/
def parseDocument (cursor : Cursor) (text : String) : Except String Json :=
  match Json.parse text with
  | .ok value => .ok value
  | .error why =>
      cursor.fail s!"is not valid JSON ({why}). Regenerate it, or fix the file by hand if it was edited."

def getObj (cursor : Cursor) (value : Json) : Except String (List (String × Json)) :=
  match value with
  | .obj fields => .ok (fields.toArray.toList.map fun entry => (entry.1, entry.2))
  | _ => cursor.fail "is not a JSON object."

/-- A required field. Absence and a wrong type are different messages, because
    they have different fixes. -/
def field (cursor : Cursor) (value : Json) (name : String) : Except String (Cursor × Json) := do
  match value with
  | .obj _ =>
      match value.getObjVal? name with
      | .ok found => return (cursor.at name, found)
      | .error _ => cursor.fail s!"has no '{name}' field."
  | _ => cursor.fail "is not a JSON object."

/-- An optional field. Distinguished from a present `null`: `plannedFor` absent
    means an enabled channel, and `plannedFor: null` means someone deleted the
    value rather than the row, which is a different mistake. -/
def field? (value : Json) (name : String) : Option Json :=
  (value.getObjVal? name).toOption

def asString (cursor : Cursor) (value : Json) : Except String String :=
  match value with
  | .str text => .ok text
  | _ => cursor.fail "is not a string."

def asBool (cursor : Cursor) (value : Json) : Except String Bool :=
  match value with
  | .bool flag => .ok flag
  | _ => cursor.fail "is not a boolean."

def asArray (cursor : Cursor) (value : Json) : Except String (List (Cursor × Json)) :=
  match value with
  | .arr items =>
      .ok (items.toList.zipIdx.map fun (item, index) => (cursor.at s!"[{index}]", item))
  | _ => cursor.fail "is not an array."

/-- A required string field, the shape almost every read takes. -/
def stringField (cursor : Cursor) (value : Json) (name : String) : Except String String := do
  let (inner, found) ← field cursor value name
  asString inner found

/-- A required string field that must not be empty. The shell's nine
    build-metadata checks were `not build.get(field)`, which conflated absence
    with `""`, `0` and `false`; separating them is the point of doing this in a
    type system. -/
def nonEmptyStringField (cursor : Cursor) (value : Json) (name : String) :
    Except String String := do
  let (inner, found) ← field cursor value name
  let text ← asString inner found
  if text.isEmpty then
    inner.fail "is empty. A record with a blank field is not a complete record; regenerate it rather than filling the field in by hand."
  else return text

/-! ## Writing

Python's `json.dump(..., indent=2, sort_keys=True)`, reproduced. The escaping
follows its `ensure_ascii=True` default: everything outside printable ASCII
becomes a `\uXXXX` escape, so the output is pure ASCII and cannot acquire a
different byte length from an encoding choice. -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n + 87)

private def unicodeEscape (code : Nat) : String :=
  let digit (shift : Nat) := hexDigit ((code / shift) % 16)
  String.ofList ['\\', 'u', digit 4096, digit 256, digit 16, digit 1]

/-- One character, escaped the way Python's encoder escapes it. Characters
    above the BMP would need a surrogate pair; they cannot occur in any
    document this tool writes, and are rejected rather than mis-encoded. -/
private def escapeChar (c : Char) : Except String String :=
  match c with
  | '"' => .ok "\\\""
  | '\\' => .ok "\\\\"
  | '\n' => .ok "\\n"
  | '\r' => .ok "\\r"
  | '\t' => .ok "\\t"
  | _ =>
    let code := c.toNat
    if code == 8 then .ok "\\b"
    else if code == 12 then .ok "\\f"
    else if code < 0x20 || code > 0x7e then
      if code > 0xffff then
        .error s!"cannot render the character U+{code} — it is outside the Basic Multilingual Plane, and this encoder does not emit surrogate pairs. No release document is expected to contain one."
      else .ok (unicodeEscape code)
    else .ok (String.singleton c)

def escapeString (text : String) : Except String String := do
  let mut out := "\""
  for c in text.toList do
    out := out ++ (← escapeChar c)
  return out ++ "\""

/-- Every number these documents carry is a `schemaVersion`-style integer, so
    an integral value renders without a fractional part and anything else is
    refused rather than guessed at — Python would print an integral float as
    `1.0`, and matching its float formatting exactly is not a thing to guess.

    Decided on the *value*, not on the representation. `JsonNumber` is a
    mantissa and a decimal exponent, and `100` can arrive as `1000e-1`; an
    earlier version tested `exponent == 0` and would have refused that — a
    perfectly good integer rejected for how it was spelled. -/
private def renderNumber (n : JsonNumber) : Except String String :=
  let scale : Int := (10 : Int) ^ n.exponent
  if n.mantissa % scale == 0 then .ok (toString (n.mantissa / scale))
  else .error s!"cannot render {n.mantissa}e-{n.exponent}: it is not an integer, and release documents carry only integers. Matching Python's float formatting exactly is not something to guess at."

private partial def renderAt (indent : Nat) (value : Json) : Except String String := do
  let pad (n : Nat) : String := String.ofList (List.replicate (n * 2) ' ')
  match value with
  | .null => return "null"
  | .bool flag => return if flag then "true" else "false"
  | .num n => renderNumber n
  | .str text => escapeString text
  | .arr items =>
      if items.isEmpty then return "[]"
      let mut parts := #[]
      for item in items do
        parts := parts.push (pad (indent + 1) ++ (← renderAt (indent + 1) item))
      return "[\n" ++ String.intercalate ",\n" parts.toList ++ "\n" ++ pad indent ++ "]"
  | .obj fields =>
      let entries := fields.toArray
      if entries.isEmpty then return "{}"
      let mut parts := #[]
      for entry in entries do
        parts := parts.push
          (pad (indent + 1) ++ (← escapeString entry.1) ++ ": " ++ (← renderAt (indent + 1) entry.2))
      return "{\n" ++ String.intercalate ",\n" parts.toList ++ "\n" ++ pad indent ++ "}"

/-- The document as bytes to write: sorted keys, two-space indent, trailing
    newline. Deterministic — the same value renders to the same bytes on every
    run and every platform, which is what lets a signed manifest and an SBOM be
    regenerated and compared rather than trusted. -/
def render (value : Json) : Except String String := do
  return (← renderAt 0 value) ++ "\n"

end Release
