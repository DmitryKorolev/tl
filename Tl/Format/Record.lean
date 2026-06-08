/-
`Tl.Format.Record` — the on-disk JSONL record (ADR-0008).

One operation per line, UTF-8, LF. Every record shares the envelope `v, op, hlc,
replica, nonce, actor`; the rest are op-specific payload fields. The parsed model
keeps the typed envelope plus a `fields` bag holding *every* other key verbatim,
so additive evolution (new optional fields) never loses data on a rewrite
(preserve-unknown). The canonical render pins envelope keys in their fixed order
then the remaining keys lexicographically, no insignificant whitespace.

The round-trip law (ADR-0008) is over the model, not raw text:
`parse (render r) = r`, and `render (parse l) = l` on an already-canonical line.
Tested I/O shell (ADR-0004); covered by `Tests/RecordTests.lean`. No Mathlib.
-/
import Lean.Data.Json

namespace Tl.Format

open Lean (Json)

/-- A parsed wire record: the typed envelope plus the remaining keys verbatim
    (sorted by key), so unknown fields are preserved on a rewrite (ADR-0008). -/
structure Record where
  v : Nat
  op : String
  hlc : String
  replica : String
  nonce : String
  actor : Option String
  /-- Non-envelope keys, sorted by key (the op payload + any unknown fields). -/
  fields : List (String × Json)

/-- The reserved envelope keys, in canonical order. -/
def envelopeKeys : List String := ["v", "op", "hlc", "replica", "nonce", "actor"]

/-- Canonical JSONL render: envelope keys in fixed order, then the remaining keys
    lexicographically, no insignificant whitespace (ADR-0008). -/
def Record.render (r : Record) : String :=
  let kv (k : String) (v : Json) : String := (Json.str k).compress ++ ":" ++ v.compress
  let actorJson := match r.actor with | some a => Json.str a | none => Json.null
  let env := [s!"\"v\":{r.v}", kv "op" (Json.str r.op),
    kv "hlc" (Json.str r.hlc), kv "replica" (Json.str r.replica),
    kv "nonce" (Json.str r.nonce), kv "actor" actorJson]
  let payload := r.fields.map (fun (k, v) => kv k v)
  "{" ++ String.intercalate "," (env ++ payload) ++ "}"

/-- Parse a JSONL line back to the model. Fail-closed on a missing/ill-typed
    *required* envelope field — `v, op, hlc, replica, nonce`, the ordering/identity/
    dispatch core (ADR-0008 §corruption). `actor` is the deliberate exception: it is
    optional *provenance* (who wrote the op), not load-bearing for the fold, so a
    missing or non-string `actor` is read leniently as `none` rather than rejecting
    the whole record. -/
def Record.parse (s : String) : Except String Record := do
  let j ← Json.parse s
  let getStr (k : String) : Except String String := do (← j.getObjVal? k).getStr?
  let v ← (← j.getObjVal? "v").getNat?
  let op ← getStr "op"
  let hlc ← getStr "hlc"
  let replica ← getStr "replica"
  let nonce ← getStr "nonce"
  -- optional provenance (see the parse docstring): lenient, never fail-closed
  let actor : Option String :=
    match j.getObjVal? "actor" with
    | .ok (Json.str a) => some a
    | _ => none
  let obj ← j.getObj?
  -- `toList` is in key order; drop the envelope keys, keep the rest verbatim.
  let fields := obj.toList.filter (fun (k, _) => k ∉ envelopeKeys)
  return { v, op, hlc, replica, nonce, actor, fields }

end Tl.Format
