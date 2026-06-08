/-
`Tests.RecordTests` — the JSONL round-trip (ADR-0008): `render ∘ parse = id` on
canonical lines, preserve-unknown across a rewrite, the `actor: null` vs absent
distinction, and the fail-closed parse of malformed / envelope-incomplete lines.
-/
import Tl.Format.Record
import Tests.Harness

open Tl.Format Tl.Tests

/-- A canonical line: envelope in fixed order, payload keys lexicographic. -/
def canonicalLine : String :=
  "{\"v\":1,\"op\":\"create\",\"hlc\":\"0000000000000001\"," ++
  "\"replica\":\"2kxvmkxsa89vq\",\"nonce\":\"0000000000000000000000000a\"," ++
  "\"actor\":\"alice\",\"id\":\"tl-000000000000abcd\",\"priority\":2}"

/-- A line with `actor: null` and an unknown (future) field. -/
def unknownLine : String :=
  "{\"v\":1,\"op\":\"update\",\"hlc\":\"0000000000000002\"," ++
  "\"replica\":\"2kxvmkxsa89vq\",\"nonce\":\"0000000000000000000000000b\"," ++
  "\"actor\":null,\"futureField\":[1,2,3],\"title\":\"hi\"}"

/-- Re-render a parsed line; `.ok line` iff the line is canonical and round-trips. -/
def roundtrip (line : String) : Except String String := (Record.parse line).map Record.render

def recordTests : List Outcome := [
  -- render ∘ parse = id on canonical lines (the round-trip law)
  check "round-trip canonical create" (decide ((roundtrip canonicalLine).toOption = some canonicalLine)),
  -- preserve-unknown: an unrecognized field survives the rewrite verbatim
  check "preserve-unknown rewrite" (decide ((roundtrip unknownLine).toOption = some unknownLine)),
  -- actor:null is preserved (distinct from absent) and re-renders as null
  check "actor null preserved"
    (match Record.parse unknownLine with | .ok r => r.actor.isNone | .error _ => false),
  check "actor string parsed"
    (match Record.parse canonicalLine with | .ok r => r.actor = some "alice" | .error _ => false),
  -- envelope is extracted, not duplicated into fields
  check "envelope keys not in fields"
    (match Record.parse canonicalLine with
     | .ok r => r.fields.all (fun (k, _) => k ∉ envelopeKeys)
     | .error _ => false),
  checkEq "version parsed"
    (match Record.parse canonicalLine with | .ok r => r.v | .error _ => 0) 1,
  -- fail-closed parse (a `.error` ⇒ `toOption` is none)
  check "malformed json errors" (Record.parse "{not json}").toOption.isNone,
  check "empty line errors" (Record.parse "").toOption.isNone,
  check "missing op errors"
    (Record.parse "{\"v\":1,\"hlc\":\"x\",\"replica\":\"r\",\"nonce\":\"n\"}").toOption.isNone,
  check "op not a string errors"
    (Record.parse "{\"v\":1,\"op\":7,\"hlc\":\"x\",\"replica\":\"r\",\"nonce\":\"n\"}").toOption.isNone
]
