/-
`Tl.Crdt.Order` — the total order the whole CRDT rests on.

ADR-0002/0007: every LWW-register join and every OR-Set add-tag is keyed by the
triple `(hlc, replica, nonce)`, which MUST be a total order or the register
join is not a well-defined function and convergence fails. The kernel consumes
this triple as an opaque, totally-ordered key; the shell mints and validates the
concrete bytes (16-hex HLC, 13-char replica, 26-char nonce, ADR-0007/0008).

This module exists first because everything below — `Lww`, `OrSet`, `State` —
is parameterized over it. For now it is a placeholder establishing the build;
the real `Stamp` type and its `LinearOrder`-style total-order proof land with
the CRDT layer (task #2).
-/

namespace Tl.Crdt

/-- Marker that the build wiring is in place. Replaced by the real `Stamp`
    total-order development in the CRDT layer. -/
def orderScaffolded : Bool := true

end Tl.Crdt
