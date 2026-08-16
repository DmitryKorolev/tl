/-
`release.Sys` — release administration's native boundary, and all of it.

One declaration. Release evidence has to be replaced atomically through a
sibling that is created exclusively and without following a link, and Lean's
`IO.FS` offers no such create: `writeFile` truncates whatever is at the path,
including a symbolic link pointing somewhere else, and an existence check
before it cannot see a dangling one at all. The primitive lives in the same
small native object as the product's, and this module is the only way release
code reaches it.

Deliberately separate from `Tl.Store.Sys`, and not merely by convention: the
symbol is `tl_release_write`, not a `tl_sys_*` one. ADR-0028 keeps release
administration out of the product TCB, so a release binding to a product symbol
would be that boundary crossed in the one direction nothing else checks — and
the release drift gate enumerates every extern in this scope and refuses it.

Nothing is decided here. The primitive reports what happened as a row of
numbers and `release.Write` says what the numbers mean; this file is the wire.
-/
import release.Write

namespace Release.Sys

/-- Replace `components` beneath `base` with `contents`, atomically.

    `base` is the directory the operator named. It is opened with ordinary
    symlink semantics — it may be absolute, and it may be reached through a
    link, because a macOS `/var` temporary directory, a symlinked home and most
    container mounts all are. The no-follow and ownership walk begins at the
    first component beneath it.

    `components` is the validated relative name, one component per element,
    passed as an array so the native side never re-splits a path string: a
    second parser is a second set of rules to disagree with the first. Every
    component but the last is a directory to descend into; the last is the file.

    Returns the nine-slot observation `Release.Write.decode` reads. Filesystem
    failures are *in* that row rather than thrown, because which phase failed
    and whether the write committed are the two things release policy branches
    on. An exception from here is therefore the primitive itself failing, not
    the write failing — and `Release.Write.through` reports the two apart. -/
@[extern "tl_release_write_atomic"]
private opaque releaseWriteAtomic (base : @&String) (components : @&Array String)
    (contents : @&ByteArray) :
    IO (Array UInt32)

/-- The mechanism `Release.Write.through` is parameterised over, with the
    native primitive in place. The only place the two meet. -/
def mechanism : Write.Mechanism := fun base path contents =>
  releaseWriteAtomic base.path ((path.components.map (·.text)).toArray) contents

end Release.Sys
