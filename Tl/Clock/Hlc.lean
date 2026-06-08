/-
`Tl.Clock.Hlc` — the hybrid logical clock (ADR-0007).

A value is `(physical, logical)`: `physical` = ms since the Unix epoch (48 bits),
`logical` = a counter (16 bits), packed as the 64-bit `(physical << 16) | logical`
— exactly the `Tl.Crdt.Stamp.hlc` the kernel orders by. On the wire it is 16
lowercase hex digits (ADR-0008), chosen because lowercase hex is ASCII-monotonic,
so bytewise string order = integer order = LWW order.

This is the tested I/O shell (ADR-0004): the pure update rules and the hex
round-trip are exercised by `Tests/`; durable monotonic *persistence* and the
system clock remain carried assumptions (overview Trusted). No Mathlib (ADR-0009).
-/

namespace Tl.Clock

/-- A hybrid logical clock. -/
structure Hlc where
  physical : Nat
  logical : Nat
deriving DecidableEq, Repr, Inhabited

namespace Hlc

/-- Largest representable physical field (48 bits). -/
def physMax : Nat := 2 ^ 48 - 1
/-- Largest representable logical field (16 bits). -/
def logMax : Nat := 2 ^ 16 - 1

/-- The epoch clock. -/
def zero : Hlc := ⟨0, 0⟩

/-- The packed 64-bit ordering value (= `Stamp.hlc`, ADR-0007). -/
def pack (h : Hlc) : Nat := h.physical * 2 ^ 16 + h.logical

/-- Both fields in range. -/
def valid (h : Hlc) : Bool := h.physical ≤ physMax && h.logical ≤ logMax

/-! ### 16-hex encoding (ADR-0007/0008) -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)

private def hexVal? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

/-- 16 lowercase hex digits of the packed value, zero-padded, big-endian. -/
def toHex (h : Hlc) : String :=
  let v := h.pack
  String.ofList ((List.range 16).reverse.map (fun i => hexDigit ((v / 16 ^ i) % 16)))

/-- Parse 16 hex digits back to an HLC (fail-closed on bad length/chars). -/
def ofHex? (s : String) : Option Hlc := do
  let cs := s.toList
  if cs.length ≠ 16 then none
  else
    let v ← cs.foldlM (fun acc c => (hexVal? c).map (acc * 16 + ·)) 0
    some ⟨v / 2 ^ 16, v % 2 ^ 16⟩

/-! ### Update rules (ADR-0007) — fail-closed on overflow, no wrap -/

/-- Advance for a new local event: `physical = max(last.physical, now)`; on a tie
    `logical` increments, else resets to 0; a `logical` overflow within one ms bumps
    `physical`; a `physical` past 2⁴⁸ saturates and errors (ADR-0007). -/
def localEvent (last : Hlc) (now : Nat) : Except String Hlc :=
  let p := max last.physical now
  if p = last.physical then
    if last.logical < logMax then .ok ⟨p, last.logical + 1⟩
    else if p < physMax then .ok ⟨p + 1, 0⟩
    else .error "hlc-overflow: clock exhausted (physical past 2^48); upgrade or wait"
  else if p ≤ physMax then .ok ⟨p, 0⟩
  else .error "hlc-overflow: physical clock past 2^48"

/-- Observe a remote HLC while folding sync: advance strictly past `last`,
    `remote`, and `now`, preserving causality across the transport (ADR-0007). -/
def observeRemote (last remote : Hlc) (now : Nat) : Except String Hlc :=
  let p := max (max last.physical remote.physical) now
  let lLast := if p = last.physical then last.logical else 0
  let lRem := if p = remote.physical then remote.logical else 0
  let baseLog := max lLast lRem
  if p = last.physical ∨ p = remote.physical then
    if baseLog < logMax then .ok ⟨p, baseLog + 1⟩
    else if p < physMax then .ok ⟨p + 1, 0⟩
    else .error "hlc-overflow: clock exhausted observing remote"
  else if p ≤ physMax then .ok ⟨p, 0⟩
  else .error "hlc-overflow: physical past 2^48 observing remote"

end Hlc

end Tl.Clock
