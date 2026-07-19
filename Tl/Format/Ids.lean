/-
`Tl.Format.Ids` — the display affix (ADR-0007/0018/0027).

The id mints themselves (`mintIssueId`, `mintNoteId`, and the shared
`mintId80`/`stampPreimage` core) live in `Tl.Format.Codec`: the `noteRemove`
decoder re-derives a note id from its observed add-tag to enforce that a
removal names its own entry (ADR-0027), and `Codec` sits below this module, so
the mint core cannot live here. This module re-exports them via its import of
`Codec` and adds the `tl-` display/reference affix — added on render, stripped
on parse, never identity (ADR-0007). Tested I/O shell (ADR-0004); no Mathlib
(ADR-0009).
-/
import Tl.Format.Codec

namespace Tl.Format

/-- The display/reference form (`tl-` affix, ADR-0007). -/
def displayId (bare : String) : String := "tl-" ++ bare

end Tl.Format
