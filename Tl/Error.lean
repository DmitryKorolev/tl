/-
`Tl.Error` — the structured error contract (ADR-0008 §`--json` / ADR-0020).

The `code` is the stable, closed, additive-only enum agents branch on; the
`message` teaches the fix — what to do next, not just what failed (a message
that only restates its code is a defect, AGENTS.md); `context` carries the
ADR-0020 named context fields verbatim into the `--json` `error` object. Each
code maps to a stable process exit code, assigned once and never renumbered
(several codes may share one exit number).

This module sits below `Tl.Format`/`Tl.Store`/`Tl.Cli` so every shell layer
can fail with the same structured type (the codec's decode, the store's lock
and path refusals, the CLI's argument errors). Tested I/O shell (ADR-0004);
no Mathlib (ADR-0009).
-/
import Lean.Data.Json

namespace Tl

open Lean (Json)

/-- The closed error-code enum (ADR-0008). Codes are *added* within a
    `schemaVersion`, never renamed or removed. Constructors are camelCase; the
    wire strings are lowercase-hyphen via `wire`. -/
inductive ErrorCode where
  | usage
  | internal
  | noProject
  | notFound
  | ambiguousId
  | forceRequired
  | malformedLine
  | unknownVersion
  | corruptClock
  | corruptReplica
  | pushRejected
  | noUpstream
  | stealthMode
  | lockBusy
  | notClaimable
  | notCloseable
  | unsafePath
  | verifyFailed
deriving DecidableEq, Repr

namespace ErrorCode

/-- The stable lowercase-hyphen wire string — the `--json` `error.code`. -/
def wire : ErrorCode → String
  | .usage => "usage"
  | .internal => "internal"
  | .noProject => "no-project"
  | .notFound => "not-found"
  | .ambiguousId => "ambiguous-id"
  | .forceRequired => "force-required"
  | .malformedLine => "malformed-line"
  | .unknownVersion => "unknown-version"
  | .corruptClock => "corrupt-clock"
  | .corruptReplica => "corrupt-replica"
  | .pushRejected => "push-rejected"
  | .noUpstream => "no-upstream"
  | .stealthMode => "stealth-mode"
  | .lockBusy => "lock-busy"
  | .notClaimable => "not-claimable"
  | .notCloseable => "not-closeable"
  | .unsafePath => "unsafe-path"
  | .verifyFailed => "verify-failed"

/-- The stable nonzero process exit code (ADR-0008; `corrupt-clock` and
    `corrupt-replica` share `9` by that assignment). -/
def exitCode : ErrorCode → UInt32
  | .usage => 2
  | .internal => 1
  | .noProject => 3
  | .notFound => 4
  | .ambiguousId => 5
  | .forceRequired => 6
  | .malformedLine => 7
  | .unknownVersion => 8
  | .corruptClock => 9
  | .corruptReplica => 9
  | .pushRejected => 10
  | .noUpstream => 11
  | .stealthMode => 12
  | .lockBusy => 13
  | .notClaimable => 14
  | .notCloseable => 15
  | .unsafePath => 16
  | .verifyFailed => 17

/-- Every code, for table-driven tests (kept in `wire`-table order). -/
def all : List ErrorCode :=
  [.usage, .internal, .noProject, .notFound, .ambiguousId, .forceRequired,
   .malformedLine, .unknownVersion, .corruptClock, .corruptReplica,
   .pushRejected, .noUpstream, .stealthMode, .lockBusy,
   .notClaimable, .notCloseable, .unsafePath, .verifyFailed]

end ErrorCode

/-- A structured failure: stable code, teaching message, and the ADR-0020
    context fields (emitted into the `--json` `error` object in the order
    given here). -/
structure Error where
  code : ErrorCode
  message : String
  context : List (String × Json) := []

namespace Error

/-- Convenience constructor without context. -/
def mk' (code : ErrorCode) (message : String) : Error := { code, message }

end Error

end Tl
