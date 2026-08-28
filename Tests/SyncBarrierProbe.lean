/-
`Tests.SyncBarrierProbe` — the test-only binding for the native durability
barrier's scripted attempt seam (ADR-0019).

The production and release paths, and this probe, all run `tl_sync_barrier` in
`ffi/tlsys.c`. The probe receives no descriptor and its scripted attempts make
no syscall. Keeping the binding in `Tests/` leaves the product no path to it,
while letting both the shim tests and the public Store tests drive failures a
real filesystem cannot be asked to produce on demand.
-/
import Tl.Store.Sys

namespace Tl.Tests.SyncBarrierProbe

open Tl.Store

/-- One scripted attempt result. These are stable test-seam codes, not errno
    values, so the same script has the same meaning on every host. -/
def ok : UInt8 := 0
def eintr : UInt8 := 1
def enotsup : UInt8 := 2
def einval : UInt8 := 3
def enotty : UInt8 := 4
def eopnotsupp : UInt8 := 5
def eio : UInt8 := 6
def enospc : UInt8 := 7
def eacces : UInt8 := 8
def ebadf : UInt8 := 9
def erofs : UInt8 := 10
def edquot : UInt8 := 11
def enxio : UInt8 := 12
def enodev : UInt8 := 13

@[extern "tl_sys_sync_probe"]
private opaque raw (hasFull : UInt8) (script : @&ByteArray) : IO UInt8

/-- Run the shipped barrier policy under a selected platform shape, decoding
    its result through the same function production `Sys.sync` uses. -/
def run (hasFull : Bool) (script : List UInt8) : IO Sys.SyncStrength := do
  Sys.strengthOrThrow (← raw (if hasFull then 1 else 0) ⟨script.toArray⟩)

/-- Whether production attempts a full barrier before its possible fallback.
    A successful real-file sync reports `fullBarrier` under either platform
    shape, so this is the observation that pins the compile-time selection. -/
@[extern "tl_sys_has_full_barrier"]
opaque hasFullBarrier : IO UInt8

end Tl.Tests.SyncBarrierProbe
