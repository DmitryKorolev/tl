/-
`Tests.JsonUtil` — shared option-returning JSON accessors for the test suites
that walk `helpJson` / envelope JSON. One definition so the grammar suites
(`GrammarTests`, `DocGrammarTests`) cannot drift apart — the same duplication
class `DocGrammarTests` itself guards against. Tested I/O shell (ADR-0004).
-/
import Lean.Data.Json

namespace Tl.Tests

open Lean (Json)

/-- An object field as raw `Json`, or `none` if absent/not an object. -/
def jGet (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

/-- An object field as a `Json` list (empty if absent or not an array). -/
def jArr (j : Json) (k : String) : List Json :=
  ((jGet j k).bind (fun v => v.getArr?.toOption)).map (·.toList) |>.getD []

/-- An object field as a string, or `none` if absent/not a string. -/
def jStr (j : Json) (k : String) : Option String :=
  (jGet j k).bind (fun v => v.getStr?.toOption)

end Tl.Tests
