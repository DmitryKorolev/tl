/-
`Tests.Sha256Tests` — SHA-256 vectors (ADR-0018).

The FIPS 180-4 published vectors (`abc`, the 56-byte two-block message) plus
the padding boundary lengths where implementations actually break (0, 1, 55,
56, 63, 64, 65 bytes and a 200-byte multi-block message), and the one worked
end-to-end id-mint vector: `(replica, hlc, nonce)` preimage → digest →
leftmost 80 bits → 16-char Crockford id.

External cross-check for any row (the ADR-0018 one-liner):
  `printf '%s' 'abc' | shasum -a 256`
-/
import Tl.Hash.Sha256
import Tl.Format.Crockford
import Tests.Harness

namespace Tl.Tests

open Tl.Hash
open Tl.Format

/-- `(name, message, expected lowercase-hex digest)`. -/
def sha256Vectors : List (String × String × String) :=
  [("empty (0B)", "",
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
   ("one byte (1B)", "a",
    "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb"),
   ("abc (FIPS)", "abc",
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
   ("55B (one-block padding max)",
    "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabc",
    "595615dbe4f0f407ae397d08b4c2cb870cb9b0e11937416f950c5160acf9c005"),
   ("56B two-block (FIPS)",
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
   ("63B", "012345678901234567890123456789012345678901234567890123456789012",
    "074f6e9ac301d5d1b6df6f1dfb8c6f89c187ea945d352ce6a29279a9c630680b"),
   ("64B (exact block)",
    "0123456789012345678901234567890123456789012345678901234567890123",
    "9674d9e078535b7cec43284387a6ee39956188e735a85452b0050b55341cda56"),
   ("65B", "01234567890123456789012345678901234567890123456789012345678901234",
    "52774b57c10e45040a61c14d35c1c8ebefe880082313aa0a21ebb077734cd067"),
   ("200B multi-block",
    String.join (List.replicate 20 "0123456789"),
    "295cbb667c2d2380418d4c7576c666c4f1690de2a2433f0e301bd5923377f8ed")]

def sha256VectorTests : List Outcome :=
  sha256Vectors.map (fun (name, msg, expected) =>
    checkEq name (Sha256.toHex (Sha256.digestString msg)) expected)

/-- Every digest is exactly 32 bytes, and the padded length is always a whole
    number of blocks with room for the `0x80` + length trailer — checked
    exhaustively across the 0–130 byte range (two blocks' worth of edges). -/
def sha256ShapeTests : List Outcome :=
  let lengths := List.range 131
  [check "digest is 32 bytes at every length 0–130"
     (lengths.all (fun n =>
       (Sha256.digest (String.join (List.replicate n "x")).toUTF8).size = 32)),
   check "padded size is a positive multiple of 64 at every length 0–130"
     (lengths.all (fun n =>
       let p := (Sha256.pad (String.join (List.replicate n "x")).toUTF8).size
       p % 64 = 0 && p ≥ n + 9))]

/-- The worked end-to-end mint vector (ADR-0018): the canonical fixed-width
    preimage `replica(13) ++ hlc(16 hex) ++ nonce(26)` — 55 bytes, exactly the
    one-block padding max — through digest → first 10 bytes big-endian →
    `toCrockford v 16`. Generated with python3 `hashlib` (an independent
    implementation); cross-check with the shasum one-liner above. -/
def sha256MintVectorTests : List Outcome :=
  let preimage := "0123456789abc" ++ "0000018d07f4c812" ++ "0123456789abcdefghjkmnpqrs"
  let dig := Sha256.digestVec preimage.toUTF8
  let v := (List.finRange 10).foldl
    (fun acc i => acc * 256 + (dig.get (i.castLE (Nat.le_add_right 10 22))).toNat) 0
  [checkEq "mint preimage is 55 bytes" preimage.utf8ByteSize 55,
   checkEq "mint preimage digest"
     (Sha256.toHex ⟨dig.toArray⟩)
     "a39f618253651fbea80e6ab7b772effe8433f860b8d06327c271a32938eb20e2",
   checkEq "leftmost 80 bits → 16-char Crockford id"
     (toCrockford v 16) "mefp30jkcmfvxa0e"]

def sha256Tests : List Outcome :=
  sha256VectorTests ++ sha256ShapeTests ++ sha256MintVectorTests

end Tl.Tests
