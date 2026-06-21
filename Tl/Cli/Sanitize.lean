/-
`Tl.Cli.Sanitize` — render-time content sanitization (ADR-0014 T1, restated
as an ADR-0020 convention).

Free-form content is untrusted data; both render paths (human and `--json`)
apply the same pinned spec wherever content is surfaced: single-line fields
(`title`, `assignee`, `slug`, the rendered actor, labels, meta keys/values)
strip all control characters and bound at 1 KiB; multi-line fields
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
    `ESC ] … BEL|ESC\` (OSC); a bare ESC drops alone. Access is
    proof-carrying (the dependent `while` binds the bound) or `Option`-based
    lookahead — nothing can panic. -/
private def stripAnsi (cs : List Char) : List Char := Id.run do
  let a := cs.toArray
  -- the index just past a CSI's final byte (0x40–0x7E), or the end
  let csiEnd (start : Nat) : Nat := Id.run do
    let mut j := start
    while h : j < a.size do
      let cj := a[j]
      if 0x40 ≤ cj.toNat && cj.toNat ≤ 0x7E then
        return j + 1
      j := j + 1
    return a.size
  -- the index just past an OSC terminator (BEL or ESC\), or the end
  let oscEnd (start : Nat) : Nat := Id.run do
    let mut j := start
    while h : j < a.size do
      let cj := a[j]
      if cj == '\x07' then
        return j + 1
      if cj == '\x1b' && a[j + 1]? == some '\\' then
        return j + 2
      j := j + 1
    return a.size
  let mut out : Array Char := #[]
  let mut i := 0
  while h : i < a.size do
    let c := a[i]
    if c == '\x1b' && a[i + 1]? == some '[' then
      i := csiEnd (i + 2)
    else if c == '\x1b' && a[i + 1]? == some ']' then
      i := oscEnd (i + 2)
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

/-- Single-line fields: all control characters stripped, 1 KiB bound. -/
def sanitizeSingle (s : String) : String :=
  sanitizeWith (fun _ => false) 1024 s

/-- Multi-line fields: LF and TAB are the only control characters retained,
    64 KiB bound. -/
def sanitizeMulti (s : String) : String :=
  sanitizeWith (fun c => c == '\n' || c == '\t') 65536 s

end Tl.Cli
