/-
`Tl.Cli.Sanitize` — render-time content sanitization (ADR-0014 T1, restated
as an ADR-0020 convention).

Free-form content is untrusted data; both render paths (human and `--json`)
apply the same pinned spec wherever content is surfaced: single-line fields
(`title`, `assignee`, `slug`, the rendered actor, labels, meta keys/values)
strip ALL control characters and bound at 1 KiB; multi-line fields
(`description`, `notes`) retain only LF and TAB and bound at 64 KiB; both
classes strip ANSI escape sequences (the whole CSI/OSC sequence, not just
the ESC byte), zero-width codepoints (ZWSP/ZWNJ/ZWJ/BOM), and bidi controls;
truncation is disclosed inline at the cut point. These are render bounds at
the consumption boundary, never storage bounds — the log keeps what was
written (a CRDT cannot reject a write).
-/

namespace Tl.Cli

private def isZeroWidthOrBidi (c : Char) : Bool :=
  let n := c.toNat
  n == 0x200B || n == 0x200C || n == 0x200D || n == 0xFEFF   -- ZWSP/ZWNJ/ZWJ/BOM
  || n == 0x200E || n == 0x200F                               -- LRM/RLM
  || (0x202A ≤ n && n ≤ 0x202E)                               -- LRE..PDF
  || (0x2066 ≤ n && n ≤ 0x2069)                               -- LRI..PDI

private def isControl (c : Char) : Bool :=
  c.toNat < 0x20 || c.toNat == 0x7F || (0x80 ≤ c.toNat && c.toNat ≤ 0x9F)

/-- Drop ANSI escape sequences whole: `ESC [ … final` (CSI) and
    `ESC ] … BEL|ESC\` (OSC); a bare ESC drops alone. -/
private def stripAnsi (cs : List Char) : List Char := Id.run do
  let a := cs.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  while i < a.size do
    let c := a[i]!
    if c == '\x1b' && i + 1 < a.size && a[i + 1]! == '[' then
      -- CSI: consume through the final byte (0x40–0x7E)
      let mut j := i + 2
      while j < a.size && !(0x40 ≤ (a[j]!).toNat && (a[j]!).toNat ≤ 0x7E) do
        j := j + 1
      i := min (j + 1) a.size
    else if c == '\x1b' && i + 1 < a.size && a[i + 1]! == ']' then
      -- OSC: consume through BEL or ESC\ (or to the end if unterminated)
      let mut j := i + 2
      let mut stop := a.size
      let mut found := false
      while j < a.size && !found do
        if a[j]! == '\x07' then
          stop := j + 1
          found := true
        else if a[j]! == '\x1b' && j + 1 < a.size && a[j + 1]! == '\\' then
          stop := j + 2
          found := true
        else
          j := j + 1
      i := stop
    else if c == '\x1b' then
      i := i + 1
    else
      out := out.push c
      i := i + 1
  return out.toList

/-- Truncate to `bound` UTF-8 bytes on a char boundary, disclosing inline. -/
private def boundBytes (bound : Nat) (s : String) : String :=
  if s.utf8ByteSize ≤ bound then s
  else
    let cut := go s.toList 0 []
    cut ++ "…[truncated]"
where
  go : List Char → Nat → List Char → String
    | [], _, acc => String.ofList acc.reverse
    | c :: rest, n, acc =>
      let n' := n + c.utf8Size
      if n' > bound then String.ofList acc.reverse else go rest n' (c :: acc)

private def sanitizeWith (keep : Char → Bool) (bound : Nat) (s : String) : String :=
  let cs := stripAnsi s.toList
  let cleaned := cs.filter (fun c => !isZeroWidthOrBidi c && (keep c || !isControl c))
  boundBytes bound (String.ofList cleaned)

/-- Single-line fields: ALL control characters stripped, 1 KiB bound. -/
def sanitizeSingle (s : String) : String :=
  sanitizeWith (fun _ => false) 1024 s

/-- Multi-line fields: LF and TAB are the only control characters retained,
    64 KiB bound. -/
def sanitizeMulti (s : String) : String :=
  sanitizeWith (fun c => c == '\n' || c == '\t') 65536 s

end Tl.Cli
