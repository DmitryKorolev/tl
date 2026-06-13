/-
`Tests.ErrorTests` — the error-code contract and the `--json` envelope
(ADR-0008 §`--json` / ADR-0020). The wire strings and exit codes are a stable,
additive-only contract, so they are pinned here byte-for-byte, one assertion
per code; the envelope shapes are pinned as exact strings (the member order is
deliberate) and re-parsed to prove they are valid JSON.
-/
import Tl.Error
import Tl.Cli.Envelope
import Tests.Harness

namespace Tl.Tests

open Tl (ErrorCode)
open Lean (Json)

/-- The pinned (wire, exit) table — one row per ADR-0008 code. -/
def errorCodeTable : List (ErrorCode × String × UInt32) :=
  [(.usage, "usage", 2),
   (.internal, "internal", 1),
   (.noProject, "no-project", 3),
   (.notFound, "not-found", 4),
   (.ambiguousId, "ambiguous-id", 5),
   (.forceRequired, "force-required", 6),
   (.malformedLine, "malformed-line", 7),
   (.unknownVersion, "unknown-version", 8),
   (.corruptClock, "corrupt-clock", 9),
   (.corruptReplica, "corrupt-replica", 9),
   (.pushRejected, "push-rejected", 10),
   (.noUpstream, "no-upstream", 11),
   (.stealthMode, "stealth-mode", 12),
   (.lockBusy, "lock-busy", 13),
   (.notClaimable, "not-claimable", 14),
   (.notCloseable, "not-closeable", 15),
   (.unsafePath, "unsafe-path", 16)]

def errorCodeTests : List Outcome :=
  -- the table covers the whole enum, and every wire string is distinct
  [checkEq "table covers the closed enum" errorCodeTable.length ErrorCode.all.length,
   checkEq "all enum values are in the table"
     (ErrorCode.all.filter (fun c => (errorCodeTable.find? (·.1 = c)).isNone)).length 0,
   checkEq "wire strings are pairwise distinct"
     (errorCodeTable.map (·.2.1)).eraseDups.length errorCodeTable.length] ++
  errorCodeTable.map (fun (c, w, x) =>
    check s!"{w} → wire/exit ({x})" (c.wire = w && c.exitCode = x)
      s!"got wire {c.wire}, exit {c.exitCode}")

def envelopeTests : List Outcome :=
  let okStr := Tl.Cli.okEnvelope (Json.mkObj [("count", Json.num 0)])
  let plainErr : Tl.Error := .mk' .noProject "no tl project here; run `tl init`"
  let ctxErr : Tl.Error :=
    { code := .lockBusy
      message := "another tl process holds the lock; retry shortly"
      context := [("path", Json.str ".tl/local/lock"), ("timeoutMs", Json.num 5000)] }
  let okNotes := Tl.Cli.okEnvelope (Json.mkObj [("count", Json.num 0)]) ["a", "b"]
  [checkEq "ok envelope bytes" okStr
     "{\"schemaVersion\":1,\"ok\":true,\"data\":{\"count\":0}}",
   checkEq "ok envelope appends a notes array (omit-empty otherwise)" okNotes
     "{\"schemaVersion\":1,\"ok\":true,\"data\":{\"count\":0},\"notes\":[\"a\",\"b\"]}",
   check "ok envelope with notes is valid JSON" (Json.parse okNotes).toOption.isSome,
   checkEq "error envelope bytes (no context)" (Tl.Cli.errorEnvelope plainErr)
     ("{\"schemaVersion\":1,\"ok\":false,\"error\":{\"code\":\"no-project\"," ++
      "\"message\":\"no tl project here; run `tl init`\"}}"),
   checkEq "error envelope bytes (context, in carried order)"
     (Tl.Cli.errorEnvelope ctxErr)
     ("{\"schemaVersion\":1,\"ok\":false,\"error\":{\"code\":\"lock-busy\"," ++
      "\"message\":\"another tl process holds the lock; retry shortly\"," ++
      "\"path\":\".tl/local/lock\",\"timeoutMs\":5000}}"),
   check "ok envelope is valid JSON" (Json.parse okStr).toOption.isSome,
   check "error envelope is valid JSON"
     (Json.parse (Tl.Cli.errorEnvelope ctxErr)).toOption.isSome,
   -- a message embedding a quote/control char stays valid JSON (escaping)
   check "error message escaping stays valid JSON"
     (Json.parse (Tl.Cli.errorEnvelope (.mk' .usage "bad \"arg\"\nsee --help"))).toOption.isSome]

end Tl.Tests
