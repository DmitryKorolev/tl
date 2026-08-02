/-
Root module of the `Tests` lean_lib — imports every test source so a bare
`lake build` (which includes `Tests` in `defaultTargets`) compiles them all, not
only those transitively reached from the `tltest` exe's `Tests.Main`. The runner
itself is `Tests.Main` (`lake exe tltest`).
-/
import Tests.Harness
import Tests.ImportsTests
import Tests.HlcTests
import Tests.CrockfordTests
import Tests.RecordTests
import Tests.CacheTests
import Tests.PerfTests
import Tests.VerifyLoadedTests
import Tests.Main
