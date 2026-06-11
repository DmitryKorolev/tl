/-
`Tests.SanitizeTests` — the ADR-0014 render sanitizer, one row per pinned
class: whole-sequence ANSI stripping (CSI and OSC, not just the ESC byte),
control-character policy per field class (single-line strips all; multi-line
keeps LF/TAB only), zero-width and bidi codepoints, and the 1 KiB / 64 KiB
bounds with the inline truncation disclosure on a UTF-8 boundary.
-/
import Tl.Cli.Sanitize
import Tests.Harness

namespace Tl.Tests

open Tl.Cli (sanitizeSingle sanitizeMulti)

def sanitizeTests : List Outcome :=
  let esc := String.singleton (Char.ofNat 0x1b)
  let bel := String.singleton (Char.ofNat 0x07)
  let zwsp := String.singleton (Char.ofNat 0x200B)
  let rlo := String.singleton (Char.ofNat 0x202E)
  let bom := String.singleton (Char.ofNat 0xFEFF)
  let del := String.singleton (Char.ofNat 0x7F)
  let c1 := String.singleton (Char.ofNat 0x9B)
  [checkEq "CSI sequence stripped whole" (sanitizeSingle ("Red " ++ esc ++ "[31mtext")) "Red text",
   checkEq "OSC sequence stripped whole (BEL-terminated)"
     (sanitizeSingle ("a" ++ esc ++ "]0;evil title" ++ bel ++ "b")) "ab",
   checkEq "OSC sequence stripped whole (ESC\\-terminated)"
     (sanitizeSingle ("a" ++ esc ++ "]8;;http://x" ++ esc ++ "\\b")) "ab",
   checkEq "bare ESC dropped" (sanitizeSingle ("a" ++ esc ++ "b")) "ab",
   checkEq "unterminated CSI consumed to the end" (sanitizeSingle ("a" ++ esc ++ "[31")) "a",
   checkEq "single-line strips all control chars" (sanitizeSingle "a\nb\tc\rd") "abcd",
   checkEq "single-line strips DEL and C1" (sanitizeSingle ("a" ++ del ++ "b" ++ c1 ++ "c")) "abc",
   checkEq "multi-line keeps LF and TAB only" (sanitizeMulti "a\nb\tc\rd") "a\nb\tcd",
   checkEq "zero-width and BOM stripped" (sanitizeSingle ("a" ++ zwsp ++ "b" ++ bom ++ "c")) "abc",
   checkEq "bidi controls stripped" (sanitizeSingle ("a" ++ rlo ++ "txet")) "atxet",
   check "1 KiB single-line bound with inline disclosure"
     (let r := sanitizeSingle (String.join (List.replicate 200 "0123456789"))
      r.endsWith "…[truncated]" && r.utf8ByteSize < 1100),
   check "the cut lands on a UTF-8 boundary"
     (let r := sanitizeSingle (String.join (List.replicate 600 "éé"))
      r.endsWith "…[truncated]" && (String.fromUTF8? r.toUTF8).isSome),
   check "multi-line 64 KiB bound"
     (let r := sanitizeMulti (String.join (List.replicate 7000 "0123456789"))
      r.endsWith "…[truncated]" && r.utf8ByteSize < 65700),
   checkEq "clean content passes through" (sanitizeSingle "Write the parser é😀/") "Write the parser é😀/"]

end Tl.Tests
