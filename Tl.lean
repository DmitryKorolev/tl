-- tl — root module. Every `.lean` file under `Tl/` must be imported here, or
-- it is invisible to `lake build` (AGENTS.md). Mapping to the TCB boundary
-- (ADR-0004): `Tl.Crdt.*` and `Tl.Kernel.*` are the proved core (no I/O);
-- `Tl.Format.*`, `Tl.Clock.*`, `Tl.Sync.*`, `Tl.Import.*`, `Tl.Cli.*` are the
-- tested shell. See docs/codebase-map.md.

-- Verified core (proved, no I/O)
import Tl.Crdt.Order
import Tl.Crdt.Map
import Tl.Crdt.Lww
import Tl.Crdt.OrSet
import Tl.Kernel.State
import Tl.Kernel.Op
import Tl.Kernel.Apply
import Tl.Kernel.Invariant

-- Tested I/O shell
