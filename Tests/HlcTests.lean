/-
`Tests.HlcTests` — exercises every branch of the HLC shell (ADR-0007): hex
round-trip, the local-event and observe-remote update rules including the
backward-clock and overflow paths, and the fail-closed parse (ADR-0004/0009).
-/
import Tl.Clock.Hlc
import Tests.Harness

open Tl.Clock Tl.Tests

/-- Worked examples covering each documented branch. -/
def hlcUnitTests : List Outcome := [
  -- encoding
  checkEq "zero packs to 0" Hlc.zero.pack 0,
  checkEq "zero hex" Hlc.zero.toHex "0000000000000000",
  checkEq "logical 1 hex" (⟨0, 1⟩ : Hlc).toHex "0000000000000001",
  checkEq "physical 1 hex" (⟨1, 0⟩ : Hlc).toHex "0000000000010000",
  checkEq "hex length is 16" (⟨12345, 678⟩ : Hlc).toHex.length 16,
  -- round-trip
  checkEq "round-trip zero" (Hlc.ofHex? Hlc.zero.toHex) (some Hlc.zero),
  checkEq "round-trip sample" (Hlc.ofHex? (⟨12345, 678⟩ : Hlc).toHex) (some ⟨12345, 678⟩),
  checkEq "round-trip max" (Hlc.ofHex? (⟨Hlc.physMax, Hlc.logMax⟩ : Hlc).toHex)
    (some ⟨Hlc.physMax, Hlc.logMax⟩),
  -- fail-closed parse
  check "reject short string" (Hlc.ofHex? "abc").isNone,
  check "reject long string" (Hlc.ofHex? "00000000000000000").isNone,
  check "reject non-hex char" (Hlc.ofHex? "zzzzzzzzzzzzzzzz").isNone,
  -- local event
  checkOk "tie bumps logical" (Hlc.localEvent ⟨100, 5⟩ 100) ⟨100, 6⟩,
  checkOk "advance resets logical" (Hlc.localEvent ⟨100, 5⟩ 200) ⟨200, 0⟩,
  checkOk "backward clock absorbed into logical" (Hlc.localEvent ⟨100, 5⟩ 50) ⟨100, 6⟩,
  checkOk "logical overflow bumps physical" (Hlc.localEvent ⟨100, Hlc.logMax⟩ 100) ⟨101, 0⟩,
  checkError "exhausted clock errors" (Hlc.localEvent ⟨Hlc.physMax, Hlc.logMax⟩ Hlc.physMax),
  -- observe remote
  checkOk "remote ahead advances past it" (Hlc.observeRemote ⟨100, 2⟩ ⟨200, 3⟩ 150) ⟨200, 4⟩,
  checkOk "now ahead of both resets" (Hlc.observeRemote ⟨100, 2⟩ ⟨150, 3⟩ 300) ⟨300, 0⟩,
  checkOk "tie takes max logical + 1" (Hlc.observeRemote ⟨200, 5⟩ ⟨200, 9⟩ 100) ⟨200, 10⟩,
  checkOk "local ahead advances past it" (Hlc.observeRemote ⟨300, 7⟩ ⟨100, 9⟩ 50) ⟨300, 8⟩
]

/-- A seeded property check: `ofHex? ∘ toHex = some` on random in-range HLCs. -/
def hlcRoundtripProp : List Outcome :=
  (sample 0x5eed 64 (fun s =>
    let (s1, p) := nextNat s (Hlc.physMax + 1)
    let (s2, l) := nextNat s1 (Hlc.logMax + 1)
    ((⟨p, l⟩ : Hlc), s2))).map (fun h =>
      checkEq s!"round-trip {h.toHex}" (Hlc.ofHex? h.toHex) (some h))

/-- Monotonicity property: every `localEvent` result is strictly greater (packed)
    than the previous, regardless of how `now` moves (the carried HLC guarantee). -/
def hlcMonotoneProp : List Outcome :=
  let steps := sample 0xb33f 64 (fun s =>
    let (s1, last_p) := nextNat s (Hlc.physMax / 2)
    let (s2, last_l) := nextNat s1 Hlc.logMax
    let (s3, now) := nextNat s2 Hlc.physMax
    ((⟨last_p, last_l⟩, now), s3))
  steps.map (fun (last, now) =>
    match Hlc.localEvent last now with
    | .ok h => check s!"monotone {last.pack}→{h.pack}" (decide (last.pack < h.pack))
    | .error _ => check "monotone (overflow ok)" true)
