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

/-- The stamp's three canonical fixed-width components concatenated
    (`replica`(13) ++ `hlc`(16 hex) ++ `nonce`(26)) — the id-mint preimage
    body, shared by the issue-id and note-id mints (the latter prefixes a
    domain tag, ADR-0007/0027). -/
def stampPreimage (st : Stamp) : String :=
  toCrockford st.replica 13 ++ hlcHex st.hlc ++ toCrockford st.nonce 26

/-- Truncate a SHA-256 of `preimage` to the leftmost 80 bits — the first 10 of
    the digest's typed 32 bytes, `Fin`-indexed so the slice can neither panic
    nor run off the end — read big-endian and Crockford-encoded to 16 chars.
    The single id-mint core; both `mintIssueId` and `mintNoteId` call it, so the
    truncation convention (ADR-0018) lives in exactly one place. -/
def mintId80 (preimage : String) : String :=
  let digest := Sha256.digestVec preimage.toUTF8
  let v := (List.finRange 10).foldl
    (fun acc i => acc * 256 + (digest.get (i.castLE (Nat.le_add_right 10 22))).toNat) 0
  toCrockford v 16

/-- Mint the bare 16-char issue id from the create op's stamp (ADR-0007). -/
def mintIssueId (st : Stamp) : String := mintId80 (stampPreimage st)

/-- The display/reference form (`tl-` affix, ADR-0007). -/
def displayId (bare : String) : String := "tl-" ++ bare

/-- Mint the bare 16-char note id from the add op's stamp (ADR-0027): the same
    leftmost-80-bit truncation as `mintIssueId` (`mintId80`), behind the
    `"note:"` domain prefix so the two id spaces can never share a preimage.
    The prefix makes the preimage 60 bytes — two SHA-256 blocks where the
    issue-id preimage is one (ADR-0018's padding-edge vectors already cover
    multi-block). The component order matches ADR-0007/0027's pinned form
    (`"note:" ++ replica ++ hlc ++ nonce`). The id is minted at write time,
    carried as record data, and never re-derived on read (ADR-0008); it has no
    display affix — a note id only ever appears in the dedicated `<note-id>`
    position, so there is nothing to disambiguate. -/
def mintNoteId (st : Stamp) : String := mintId80 ("note:" ++ stampPreimage st)

end Tl.Format
