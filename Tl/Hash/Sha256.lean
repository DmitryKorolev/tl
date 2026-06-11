/-
`Tl.Hash.Sha256` — SHA-256 as a direct FIPS 180-4 transcription (ADR-0018).

Pure Lean, no FFI, no dependency: the consumers (issue-id mint, the import
derivations) hash *public* data, so the only property needed is byte-exact
agreement with the standard — which `Tests/Sha256Tests.lean` checks against
CAVP-style vectors and the padding boundary lengths.

The fixed-shape state is `Vector`-typed (the AGENTS.md `Fin`-indices rule):
the 64 round constants, the 64-entry message schedule, the 8 hash words, and
the 32-byte digest all carry their length in the type, so indexing is total
with no panics and no side bound proofs. The one dynamic boundary — reading
block bytes out of the padded `ByteArray` — uses an explicit-default access
whose default arm is dead by `pad`'s postcondition (the padded stream is a
whole number of 64-byte blocks).

The pinned public API stays `digest : ByteArray → ByteArray` (all 32 bytes —
consumers slice; ids take the leftmost 80 bits, the first 10 bytes, NIST
truncation; import widths differ, which is why truncation does not live
here). `digestVec` is the same digest at type `Vector UInt8 32`, for
consumers that want the length by type. This transcription *is* the
production code: an optimized variant may only ever ship with a proved
`fast = spec` bridge (ADR-0018).

Tested I/O-shell tier (ADR-0004, pure code); no Mathlib (ADR-0009).
-/

namespace Tl.Hash

namespace Sha256

/-- The 64 round constants (FIPS 180-4 §4.2.2): the first 32 bits of the
    fractional parts of the cube roots of the first 64 primes. -/
def roundConstants : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value (§5.3.3): the first 32 bits of the fractional
    parts of the square roots of the first 8 primes. -/
def initialHash : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Right-rotation of a 32-bit word (§3.2; `1 ≤ n ≤ 31` at every use site). -/
def rotr (n x : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- `Ch` (§4.1.2). -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- `Maj` (§4.1.2). -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀` (§4.1.2). -/
def bigSigma0 (x : UInt32) : UInt32 := rotr 2 x ^^^ rotr 13 x ^^^ rotr 22 x

/-- `Σ₁` (§4.1.2). -/
def bigSigma1 (x : UInt32) : UInt32 := rotr 6 x ^^^ rotr 11 x ^^^ rotr 25 x

/-- `σ₀` (§4.1.2). -/
def smallSigma0 (x : UInt32) : UInt32 := rotr 7 x ^^^ rotr 18 x ^^^ (x >>> 3)

/-- `σ₁` (§4.1.2). -/
def smallSigma1 (x : UInt32) : UInt32 := rotr 17 x ^^^ rotr 19 x ^^^ (x >>> 10)

/-- §5.1.1 padding: append `0x80`, zero bytes to 56 mod 64, then the 64-bit
    big-endian *bit* length; the result is a whole number of 64-byte blocks
    (the postcondition `blockWords` relies on). -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : Nat := msg.size * 8
  let rem := (msg.size + 1) % 64
  let zeros := if rem ≤ 56 then 56 - rem else 56 + 64 - rem
  let mut out := msg.push 0x80
  for _ in [0:zeros] do
    out := out.push 0
  for i in (List.range 8).reverse do
    out := out.push (UInt8.ofNat ((bitLen >>> (8 * i)) % 256))
  return out

/-- The 16 big-endian words of the 64-byte block at byte offset `off`
    (§5.2.1). The byte source is the one dynamic boundary: access uses an
    explicit zero default, dead so long as `off + 64 ≤ msg.size` — `pad`'s
    whole-blocks postcondition at the single call site. -/
def blockWords (msg : ByteArray) (off : Nat) : Vector UInt32 16 :=
  let byte (i : Nat) : UInt32 := (msg[i]?.getD 0).toUInt32
  Vector.ofFn fun j =>
    let base := off + 4 * j.val
    (byte base <<< 24) ||| (byte (base + 1) <<< 16) |||
      (byte (base + 2) <<< 8) ||| byte (base + 3)

/-- §6.2.2 step 1 — extend the 16 block words to the 64-entry schedule. The
    recurrence indexes with `Fin 64` arithmetic (mod-64 subtraction never
    wraps here: every updated index is ≥ 16 and every offset ≤ 16). -/
def schedule (w16 : Vector UInt32 16) : Vector UInt32 64 := Id.run do
  let mut w : Vector UInt32 64 :=
    Vector.ofFn fun i => if h : i.val < 16 then w16.get ⟨i.val, h⟩ else 0
  for i in (List.finRange 64).drop 16 do
    w := w.set i (smallSigma1 (w.get (i - 2)) + w.get (i - 7)
      + smallSigma0 (w.get (i - 15)) + w.get (i - 16))
  return w

/-- §6.2.2 steps 2–4 — compress one block into the running hash. The round
    loop walks the zipped constants/schedule vectors, so it needs no index
    at all. -/
def compress (h : Vector UInt32 8) (w16 : Vector UInt32 16) : Vector UInt32 8 := Id.run do
  let mut a := h.get 0
  let mut b := h.get 1
  let mut c := h.get 2
  let mut d := h.get 3
  let mut e := h.get 4
  let mut f := h.get 5
  let mut g := h.get 6
  let mut hh := h.get 7
  for (k, wi) in (roundConstants.zip (schedule w16)).toList do
    let t1 := hh + bigSigma1 e + ch e f g + k + wi
    let t2 := bigSigma0 a + maj a b c
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #v[h.get 0 + a, h.get 1 + b, h.get 2 + c, h.get 3 + d,
            h.get 4 + e, h.get 5 + f, h.get 6 + g, h.get 7 + hh]

/-- The eight final hash words. -/
def digestWords (msg : ByteArray) : Vector UInt32 8 := Id.run do
  let padded := pad msg
  let mut h := initialHash
  for blk in [0:padded.size / 64] do
    h := compress h (blockWords padded (64 * blk))
  return h

/-- A word's four big-endian bytes. -/
def bytesOfWordBE (w : UInt32) : Vector UInt8 4 :=
  #v[(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- The digest with its length carried in the type (ADR-0018's
    "digest length = 32" hardening, by construction). -/
def digestVec (msg : ByteArray) : Vector UInt8 32 :=
  let h := digestWords msg
  bytesOfWordBE (h.get 0) ++ bytesOfWordBE (h.get 1)
    ++ bytesOfWordBE (h.get 2) ++ bytesOfWordBE (h.get 3)
    ++ bytesOfWordBE (h.get 4) ++ bytesOfWordBE (h.get 5)
    ++ bytesOfWordBE (h.get 6) ++ bytesOfWordBE (h.get 7)

/-- The full 32-byte digest — the pinned ADR-0018 API; consumers slice
    (issue ids take the *leftmost* 80 bits, the first 10 bytes, big-endian). -/
def digest (msg : ByteArray) : ByteArray := ⟨(digestVec msg).toArray⟩

/-- Digest of a string's UTF-8 bytes (the mint preimages are ASCII strings). -/
def digestString (s : String) : ByteArray := digest s.toUTF8

/-- Lowercase hex of a byte array (the test/fingerprint display form). -/
def toHex (b : ByteArray) : String := Id.run do
  let digit (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)
  let mut cs : List Char := []
  for byte in b do
    cs := digit (byte.toNat % 16) :: digit (byte.toNat / 16) :: cs
  return String.ofList cs.reverse

end Sha256

end Tl.Hash
