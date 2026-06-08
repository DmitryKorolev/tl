/-
`Tl.Clock.Replica` — replica identity (ADR-0007).

A replica id is minted once per working copy: Crockford base32 of 64 random bits,
a fixed 13 lowercase chars. It is part of the LWW tie-break `(hlc, replica,
nonce)`, the op `replica` field, and issue-id derivation. Stored gitignored in
`.tl/local/replica` and never shared (a shared replica-id collapses the tie-break
and segment ownership). Tested I/O shell (ADR-0004); the real-world *uniqueness*
of the random source is a carried assumption (overview Trusted). No Mathlib.
-/
import Tl.Format.Crockford

namespace Tl.Clock

open Tl.Format

/-- A replica id (13 Crockford chars). -/
structure Replica where
  id : String
deriving DecidableEq, Repr, Inhabited

namespace Replica

/-- Encode a 64-bit value as a 13-char replica id. -/
def ofNat (v : Nat) : Replica := ⟨toCrockford v 13⟩

/-- Well-formed: 13 chars, all Crockford-decodable. -/
def valid (r : Replica) : Bool := r.id.length = 13 && (ofCrockford? r.id).isSome

/-- The decoded value (for issue-id derivation / the LWW tie-break). -/
def toNat? (r : Replica) : Option Nat := ofCrockford? r.id

/-- Mint a fresh replica id from 64 random bits (ADR-0007). -/
def mint : IO Replica := do
  return ofNat (← IO.rand 0 (2 ^ 64 - 1))

end Replica

end Tl.Clock
