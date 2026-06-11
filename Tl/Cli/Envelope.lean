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
    additive-only binds from 1.0). -/
def schemaVersion : Nat := 1

private def member (k : String) (v : Json) : String :=
  (Json.str k).compress ++ ":" ++ v.compress

/-- The success envelope: `{"schemaVersion":1,"ok":true,"data":<data>}`. -/
def okEnvelope (data : Json) : String :=
  s!"\{\"schemaVersion\":{schemaVersion},\"ok\":true,\"data\":" ++ data.compress ++ "}"

/-- The error envelope:
    `{"schemaVersion":1,"ok":false,"error":{"code":…,"message":…,<context…>}}`,
    context members in the order the `Tl.Error` carries them (ADR-0020). -/
def errorEnvelope (e : Error) : String :=
  let members :=
    member "code" (Json.str e.code.wire) ::
    member "message" (Json.str e.message) ::
    e.context.map (fun (k, v) => member k v)
  s!"\{\"schemaVersion\":{schemaVersion},\"ok\":false,\"error\":\{" ++
    String.intercalate "," members ++ "}}"

end Tl.Cli
