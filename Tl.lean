-- tl — root module. Every `.lean` file under `Tl/` must be imported here, or
-- it is invisible to `lake build` (AGENTS.md). Mapping to the TCB boundary
-- (ADR-0004): `Tl.Crdt.*` and `Tl.Kernel.*` are the proved core (no I/O);
-- `Tl.Format.*`, `Tl.Clock.*`, `Tl.Sync.*`, `Tl.Import.*`, `Tl.Cli.*` are the
-- tested shell. See docs/codebase-map.md.

-- Verified core (proved, no I/O)
import Tl.Crdt.Order
import Tl.Crdt.Map
import Tl.Crdt.MapFold
import Tl.Crdt.Lww
import Tl.Crdt.OrSet
import Tl.Kernel.State
import Tl.Kernel.Op
import Tl.Kernel.Apply
import Tl.Kernel.Invariant
import Tl.Kernel.Rollup
import Tl.Kernel.RollupSpec
import Tl.Kernel.RollupSat
import Tl.Kernel.RollupFast
import Tl.Kernel.Ready
import Tl.Kernel.ReadyFast
import Tl.Kernel.Cycles
import Tl.Kernel.CyclesFast
import Tl.Kernel.Theorems
import Tl.Kernel.FoldFast
import Tl.Kernel.Frame
import Tl.Kernel.CloseMono
import Tl.Kernel.Reach
import Tl.Kernel.RollupAcyclic
import Tl.Kernel.SccProps
import Tl.Kernel.Unblocks
import Tl.Kernel.Ranking

-- Tested I/O shell
import Tl.Error
import Tl.Hash.Sha256
import Tl.Clock.Hlc
import Tl.Clock.Replica
import Tl.Clock.Skew
import Tl.Clock.SkewConverge
import Tl.Format.Crockford
import Tl.Format.Record
import Tl.Format.Time
import Tl.Format.Version
import Tl.Format.Codec
import Tl.Format.Ids
import Tl.Store.Sys
import Tl.Store.Paths
import Tl.Store.Local
import Tl.Store.Segment
import Tl.Store.Materialize
import Tl.Store.Cache
import Tl.Store.Lock
import Tl.Sync.Merge
import Tl.Sync.Ref
import Tl.Sync.Local
import Tl.Sync.Remote
import Tl.Cli.Envelope
import Tl.Cli.Init
import Tl.Cli.Project
import Tl.Cli.Render
import Tl.Cli.Resolve
import Tl.Cli.Grammar
import Tl.Cli.Commands
import Tl.Cli.Main
