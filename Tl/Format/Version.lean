/-
`Tl.Format.Version` — the log format version policy (ADR-0008 §versioning).

`v` is a monotonic integer; v1 is the baseline a first writer stamps. The
policy is fail-closed on newer: a record whose `v` exceeds what this binary
supports refuses its *segment* (never the whole log — ADR-0008 §corruption),
with an upgrade message. `v = 0` (below the baseline) is not a version at all
— no writer ever stamped it — so it is malformed, not "older". The reserved
`snapshot` record kind ships with *destructive* log GC behind a `v` bump
(ADR-0008) — the non-destructive snapshot is the no-bump fold cache (ADR-0022) —
so this v1 reader correctly refuses a GC'd log as unknown-version; there is
deliberately no stage-1 snapshot code.

Tested I/O shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Tl.Error

namespace Tl.Format

/-- The newest log format version this binary reads. Writers stamp per
    record: the two note kinds carry `v: 2` (ADR-0027 — exactly what a
    pre-journal reader cannot fold, so it fail-closes with the upgrade
    message on any segment containing note ops), every other record stays
    `v: 1` (`WireOp.recordVersion`). -/
def supportedVersion : Nat := 2

/-- Fail closed on a version this binary cannot fold (ADR-0008). -/
def checkVersion (v : Nat) : Except Tl.Error Unit :=
  if v = 0 then
    .error (.mk' .malformedLine
      "record carries v=0, which no tl writer stamps — the line is damaged; repair it or rerun the read with --skip-bad")
  else if v > supportedVersion then
    .error (.mk' .unknownVersion
      s!"record carries log format v={v} but this tl reads up to v={supportedVersion} — upgrade tl to fold this segment")
  else
    .ok ()

end Tl.Format
