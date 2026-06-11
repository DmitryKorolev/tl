/-
`Tl.Format.Ids` — issue-id minting and the display affix (ADR-0007/0018).

The id is the leftmost 80 bits of SHA-256 — the first 10 digest bytes, read
big-endian (the NIST truncation convention, ADR-0018) — over the canonical
fixed-width preimage `replica(13) ++ hlc(16 hex) ++ nonce(26)`, encoded as 16
Crockford chars. The stored form is bare; `tl-` is a display/reference affix
only — added on render, stripped on parse, never identity (ADR-0007).
Tested I/O shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Tl.Hash.Sha256
import Tl.Format.Codec

namespace Tl.Format

open Tl.Crdt (Stamp)
open Tl.Hash

/-- Mint the bare 16-char issue id from the create op's stamp (ADR-0007):
    the leftmost 80 bits — the first 10 of the digest's typed 32 bytes,
    `Fin`-indexed, so the slice can neither panic nor run off the end. -/
def mintIssueId (st : Stamp) : String :=
  let preimage := toCrockford st.replica 13 ++ hlcHex st.hlc ++ toCrockford st.nonce 26
  let digest := Sha256.digestVec preimage.toUTF8
  let v := (List.finRange 10).foldl
    (fun acc i => acc * 256 + (digest.get (i.castLE (Nat.le_add_right 10 22))).toNat) 0
  toCrockford v 16

/-- The display/reference form (`tl-` affix, ADR-0007). -/
def displayId (bare : String) : String := "tl-" ++ bare

end Tl.Format
