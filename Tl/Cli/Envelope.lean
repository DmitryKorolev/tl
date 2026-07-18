/-
`Tl.Cli.Envelope` — the `--json` response envelope (ADR-0008 §`--json` /
ADR-0020).

`{ "schemaVersion": <int>, "ok": <bool>, "data": … | "error": … }` — `ok` is
the explicit discriminant and exactly one of `data`/`error` is present, by
construction here. The envelope members are emitted in that deliberate order
(`Json.mkObj` would re-sort keys; the shape is a chosen contract, not whatever
a serializer happens to emit — ADR-0020). Inner `data` payloads built with
`Json.mkObj` render with sorted keys, which is fine: the `--json` contract is
additive-only over *fields*, with no byte-order promise (that promise exists
only for the on-disk log, ADR-0008 §canonical form).

Tested I/O shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Tl.Error

namespace Tl.Cli

open Lean (Json)

/-- The `--json` schema version (ADR-0008: bumps are breaking and disclosed;
    additive-only binds from 1.0). v2: `show`'s `claim.outcome` grew a third
    value `ended` and re-mapped some formerly-`won`/`superseded` states. v3: the
    issue object's `notes` field changed type — string → an array of journal
    entries (ADR-0027) — a re-typed field, so a 0.x break disclosed in the
    ADR-0008 ledger. -/
def schemaVersion : Nat := 3

private def member (k : String) (v : Json) : String :=
  (Json.str k).compress ++ ":" ++ v.compress

/-- The success envelope: `{"schemaVersion":3,"ok":true,"data":<data>}`, with an
    optional trailing `"notes":[…]` carrying the same loud-not-silent
    disclosures printed to stderr (foreign-refusal, skew-deferred, stale-read
    degrade — ADR-0008). **Omit-empty** (ADR-0020): absent when there are no
    notes, so the steady-state shape is unchanged and the field is additive.
    Callers pass already-sanitized notes (ADR-0014). -/
def okEnvelope (data : Json) (notes : List String := []) : String :=
  let notesField := if notes.isEmpty then ""
    else ",\"notes\":" ++ (Json.arr (notes.map Json.str).toArray).compress
  s!"\{\"schemaVersion\":{schemaVersion},\"ok\":true,\"data\":" ++ data.compress ++ notesField ++ "}"

/-- The error envelope:
    `{"schemaVersion":3,"ok":false,"error":{"code":…,"message":…,<context…>}}`,
    context members in the order the `Tl.Error` carries them (ADR-0020). -/
def errorEnvelope (e : Error) : String :=
  let members :=
    member "code" (Json.str e.code.wire) ::
    member "message" (Json.str e.message) ::
    e.context.map (fun (k, v) => member k v)
  s!"\{\"schemaVersion\":{schemaVersion},\"ok\":false,\"error\":\{" ++
    String.intercalate "," members ++ "}}"

end Tl.Cli
