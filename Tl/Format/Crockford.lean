/-
`Tl.Format.Crockford` — Crockford base32 (ADR-0007).

The encoding for replica ids (13 chars / 64 bits), nonces (26 / 128), and issue
ids (16 / 80): `0-9 a-z` minus `i l o u`, lowercase, 5 bits/char — typo-resistant
(no `0/o`, `1/l`) and case-insensitive on decode (`i`,`l`→1, `o`→0). Tested I/O
shell (ADR-0004); no Mathlib (ADR-0009).
-/

namespace Tl.Format

/-- The Crockford alphabet (`0-9 a-z` minus `i l o u`), lowercase. -/
def crockfordAlphabet : List Char := "0123456789abcdefghjkmnpqrstvwxyz".toList

/-- The digit char for `n < 32`. -/
def crockfordChar (n : Nat) : Char := crockfordAlphabet.getD n '0'

/-- Decode one char (case-insensitive; `i`/`l`→1, `o`→0; ADR-0007). -/
def crockfordVal? (c : Char) : Option Nat :=
  match c.toLower with
  | 'i' | 'l' => some 1
  | 'o' => some 0
  | c' => crockfordAlphabet.findIdx? (· = c')

/-- `v` as `width` base32 digits, big-endian, zero-padded. -/
def toCrockford (v : Nat) (width : Nat) : String :=
  String.ofList ((List.range width).reverse.map (fun i => crockfordChar ((v / 32 ^ i) % 32)))

/-- Parse a Crockford string to a `Nat` (fail-closed on a bad char). -/
def ofCrockford? (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c => (crockfordVal? c).map (acc * 32 + ·)) 0

end Tl.Format
