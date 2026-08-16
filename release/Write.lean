/-
`release.Write` — what a release-evidence write *is*, stated before anything
performs one.

Three things live here, and each exists because the interim writer in
`release/Command.lean` cannot express it.

**Where the bytes may land.** That writer takes one path string and hands it to
`IO.FS`, so "which directory" and "which file" are the same value, and the only
thing standing between a caller and an absolute path or a `..` is that no caller
has written one yet. ADR-0028 replaces that with a directory the operator names
once and a *relative* output name that is a sealed, non-empty list of validated
components. `Component` refuses the empty string, `.`, `..`, an embedded `/` and
an embedded NUL; `OutputPath` refuses an absolute name and cannot be empty by
construction. The NUL check is not decoration: Lean's `String` admits one and
`lean_string_cstr` stops at it, so `dist\x00/../../etc` reaches C as `dist`.

**What the mechanism observed.** That writer returns `IO Unit`, so every way a
write can end collapses into "threw" or "did not". Two of those endings are not
the same fact: a rename that succeeded and a directory sync that then failed is
a write a later reader in this run *will* see, and reporting it as a failure
sends an operator to repair something that already happened. `WriteOutcome`
therefore separates commit from durability, and carries the sync strength and
the cleanup disposition alongside — because "the staging sibling is still
there" is the difference between a path a rerun can use and one it cannot.

**How that observation crosses the FFI boundary.** As a row of small integers,
decoded here. The prototype recovered the error class by matching the shim's
formatted prose — the errno name, spelled between colons, inside the message C
builds — which makes a sentence part of the contract: reword the message and
the classification silently stops matching, with no build failing. Operation and
errno are structured fields instead, and `Tests.ReleaseDriftTests` refuses the
prose form anywhere under `release/` permanently.

The decoder is also the seam. Every phase failure the native writer can report
is a row a test can hand to `decodeRow` without a filesystem that can produce
it, so the phase matrix is exercised here and the native implementation is
checked against the *same* expectations later — including the destination and
staging effects each outcome predicts, which is what a real fault test then
compares the directory against.

Nothing in this module does I/O; `Mechanism` is where the I/O would be, as a
parameter.
-/

namespace Release.Write

/-! ## Where the bytes may land -/

/-- One component of a relative output name: a directory or the file itself.

    Private constructor: the only way to one is `Component.parse`, so a value of
    this type has already been refused the five shapes below. -/
structure Component where
  private mk ::
  text : String
  deriving DecidableEq, Repr

/-- What a component may not be, each refused separately so that the message
    says which rule was broken rather than "invalid".

    `.` and `..` are refused rather than resolved. Resolving them here would
    mean this layer deciding what the caller meant, and `..` is the one where
    that decision escapes the directory the operator granted — the whole point
    of naming a base once. -/
def Component.parse (what : String) (text : String) : Except String Component :=
  if text.isEmpty then
    .error s!"{what}: an output name has an empty component. That is what a doubled or trailing '/' produces, and it names no file; write the components you mean."
  else if text == "." then
    .error s!"{what}: '.' is not an output component. It names the directory the write is already anchored to, so it is refused rather than skipped — a name that resolves to somewhere else than it reads is exactly what the anchored write exists to prevent."
  else if text == ".." then
    .error s!"{what}: '..' is not an output component. Release evidence is written beneath the directory given to --output-dir, and a component that climbs out of it would put the bytes somewhere the operator did not name."
  else if text.contains '/' then
    .error s!"{what}: '{text}' is one component and contains '/'. Pass the components separately — a component holding a separator is a path that was never checked as one."
  else if text.contains '\x00' then
    .error s!"{what}: '{text}' contains a NUL byte. C stops reading a path at the first NUL, so this would reach the filesystem as a shorter name than it reads here — a different file, silently."
  else .ok ⟨text⟩

/-- A relative output name: at least one component, by construction.

    Non-emptiness is structural rather than an invariant on a `List`, so there is
    no value of this type that names nothing and no caller that has to check. -/
structure OutputPath where
  private mk ::
  first : Component
  rest : List Component
  deriving DecidableEq, Repr

/-- The components, in order. -/
def OutputPath.components (path : OutputPath) : List Component :=
  path.first :: path.rest

/-- There is no empty output name. Stated rather than left to the reader of the
    structure, because it is the property the native side relies on when it
    treats the last component as the file and everything before it as
    directories to descend. -/
theorem OutputPath.components_ne_nil (path : OutputPath) : path.components ≠ [] :=
  List.cons_ne_nil _ _

/-- The name as it would be written, for a message. Never used to reach the
    filesystem: the components go to C as an array, unsplit. -/
def OutputPath.render (path : OutputPath) : String :=
  String.intercalate "/" ((path.components).map (·.text))

/-- The last component: the file the bytes end up in. -/
def OutputPath.leaf (path : OutputPath) : Component :=
  path.rest.getLast?.getD path.first

/-- The predictable staging sibling's name: the leaf with `.tmp` appended.

    Predictable rather than randomised, deliberately, and the reason is the same
    one that makes it safe: the sibling is created with `O_CREAT | O_EXCL |
    O_NOFOLLOW`, so an existing object at that name — including a dangling
    symlink, which an existence check cannot see — refuses the write before a
    byte is written, rather than being written through. A random name would
    make each run's leftovers a new file nobody looks for. -/
def OutputPath.stagingName (path : OutputPath) : String :=
  path.leaf.text ++ ".tmp"

/-- The staging sibling as a relative path beneath the output directory.

    The native side needs only `stagingName`, because it already holds the
    final directory descriptor. A refusal needs the whole relative path: for a
    nested output, telling an operator only `leaf.tmp` names the wrong place to
    inspect or remove. -/
def OutputPath.stagingRender (path : OutputPath) : String :=
  let parents := path.components.dropLast.map (·.text)
  String.intercalate "/" (parents ++ [path.stagingName])

/-- Parse a relative output name written as one string.

    Splitting on `/` here is not the thing ADR-0028 forbids: what may not happen
    is *deriving the base* by splitting an output path, because that would let a
    name choose its own anchor. The base is a separate value the operator gave;
    this only says which components, beneath it, the name has. -/
def OutputPath.parse (what : String) (name : String) : Except String OutputPath :=
  if name.startsWith "/" then
    .error s!"{what}: '{name}' is an absolute path. The output name is relative to --output-dir, which is the only thing that says where release evidence may be written; an absolute name would ignore it."
  else
    match name.splitOn "/" with
    | [] => .error s!"{what}: '{name}' names no components."
    | headText :: restText => do
        let first ← Component.parse what headText
        let rest ← restText.mapM (Component.parse what)
        return ⟨first, rest⟩

/-- The directory the operator named, and the only place a writing command may
    write.

    Deliberately *not* a component list. It is the operator's anchor: it may be
    absolute, it may be reached through a symlink, and the native side opens it
    that way on purpose — applying no-follow to the base would refuse ordinary
    anchors such as a macOS `/var` temporary directory or a symlinked home. The
    no-follow and ownership walk starts beneath it. So the only checks here are
    the two that would otherwise mean something different to C than to Lean. -/
structure OutputDirectory where
  private mk ::
  path : String
  deriving DecidableEq, Repr

def OutputDirectory.parse (what : String) (text : String) : Except String OutputDirectory :=
  if text.isEmpty then
    .error s!"{what}: the output directory is the empty string, which names no directory. Pass the directory to write into, or leave the option off — it defaults to the working directory."
  else if text.contains '\x00' then
    .error s!"{what}: the output directory contains a NUL byte, so C would read it as a shorter path than it reads here — a different directory, silently."
  else .ok ⟨text⟩

/-- The default: the process working directory, stated rather than discovered.

    A release step that gave no `--output-dir` writes where it was started, and
    nothing here searches upward for a repository root. -/
def OutputDirectory.working : OutputDirectory := ⟨"."⟩

/-- A relative output name located beneath the operator-selected base, for a
    message. This never reaches the filesystem: the held base and validated
    components remain separate all the way to the native call. -/
def OutputDirectory.locate (base : OutputDirectory) (relative : String) : String :=
  if base.path == "." then relative
  else if base.path.endsWith "/" then base.path ++ relative
  else base.path ++ "/" ++ relative

/-! ## What the mechanism observed

The names below are the ADR's, and the shape is deliberately not "an error or
nothing": a write has a commit fact, a durability fact and a leftovers fact, and
each is separately actionable. -/

/-- Which phase of the write the mechanism was in.

    These *are* the phases the fault matrix enumerates. Structured, so a
    refusal names the step rather than quoting whatever the C library formatted
    for that errno. -/
inductive Operation where
  /-- Opening the operator-supplied base, `O_DIRECTORY | O_CLOEXEC`. -/
  | openBase
  /-- Checking the opened base is owned by the effective uid. -/
  | ownBase
  /-- Opening one component beneath the base, no-follow. -/
  | walkDirectory
  /-- Checking one walked component is owned by the effective uid. -/
  | ownDirectory
  /-- Creating the staging sibling, `O_CREAT | O_EXCL | O_NOFOLLOW`. -/
  | createStaging
  /-- Writing the complete bytes into the staging sibling. -/
  | writeBytes
  /-- Flushing the staging file's bytes. -/
  | syncFile
  /-- Closing the staging file. -/
  | closeFile
  /-- Renaming the staging sibling over the destination. -/
  | rename
  /-- Flushing the directory entry after the rename. -/
  | syncDirectory
  /-- Removing a staging sibling this invocation created. -/
  | removeStaging
  deriving DecidableEq, Repr

/-- What the phase was trying to do, for a message. -/
def Operation.describe : Operation → String
  | .openBase => "opening the output directory"
  | .ownBase => "checking the output directory belongs to this user"
  | .ownDirectory => "checking a directory beneath it belongs to this user"
  | .walkDirectory => "opening a directory beneath the output directory"
  | .createStaging => "creating the staging file beside the destination"
  | .writeBytes => "writing the bytes"
  | .syncFile => "flushing the bytes to storage"
  | .closeFile => "closing the staging file"
  | .rename => "renaming the staging file over the destination"
  | .syncDirectory => "flushing the directory entry after the rename"
  | .removeStaging => "removing the staging file"

/-- What to do about a failure in this phase. Keyed by phase rather than by
    errno because the phase is what says *which* thing to look at; the errno
    below narrows it. -/
def Operation.remedy : Operation → String
  | .openBase =>
      "Pass --output-dir a directory that exists and this process can open."
  | .ownBase =>
      "Release evidence is written into a directory this user owns. In a container, mount a writable scratch directory and run with a --user that owns it; the read-only checkout is not an output directory."
  | .ownDirectory =>
      "Every directory beneath --output-dir must belong to this user; one of them does not. Remove it and let this run create it, or point --output-dir at a tree this user owns."
  | .walkDirectory =>
      "A directory in the output name could not be opened, or is a symbolic link. Links are refused rather than followed, so the bytes cannot be redirected out of the granted directory; replace it with a real directory."
  | .createStaging =>
      "The staging file is created exclusively, so anything already at that name refuses the write instead of being written through. Find out what left it there — an interrupted run, or a link pointing elsewhere — and remove it deliberately."
  | .writeBytes =>
      "The bytes did not all reach the staging file. Check free space and quota on the output directory."
  | .syncFile =>
      "The staging file could not be flushed, so it is not safe to rename over the destination. The destination still holds the previous contents."
  | .closeFile =>
      "The staging file could not be closed cleanly, which can be the first report of a deferred write error. The destination still holds the previous contents."
  | .rename =>
      "The staging file was complete but could not replace the destination. Check the destination is not a directory and that this user may rename within the output directory."
  | .syncDirectory =>
      "The replacement happened; only the directory entry's flush did not. Nothing needs repairing for this run."
  | .removeStaging =>
      "The write already failed; this is about the leftovers. Remove the staging file named above before rerunning, since the next run refuses to write through it."

private def openBaseCode : Nat := 1
private def ownBaseCode : Nat := 2
private def walkDirectoryCode : Nat := 3
private def ownDirectoryCode : Nat := 4
private def createStagingCode : Nat := 5
private def writeBytesCode : Nat := 6
private def syncFileCode : Nat := 7
private def closeFileCode : Nat := 8
private def renameCode : Nat := 9
private def syncDirectoryCode : Nat := 10
private def removeStagingCode : Nat := 11

/-- The wire code. `0` is not one of them: it is how the row says "no error
    here", which is what makes an absent error distinguishable from a present
    one rather than a default. -/
def Operation.code : Operation → Nat
  | .openBase => openBaseCode
  | .ownBase => ownBaseCode
  | .walkDirectory => walkDirectoryCode
  | .ownDirectory => ownDirectoryCode
  | .createStaging => createStagingCode
  | .writeBytes => writeBytesCode
  | .syncFile => syncFileCode
  | .closeFile => closeFileCode
  | .rename => renameCode
  | .syncDirectory => syncDirectoryCode
  | .removeStaging => removeStagingCode

def Operation.ofCode : Nat → Option Operation
  | 1 => some .openBase
  | 2 => some .ownBase
  | 3 => some .walkDirectory
  | 4 => some .ownDirectory
  | 5 => some .createStaging
  | 6 => some .writeBytes
  | 7 => some .syncFile
  | 8 => some .closeFile
  | 9 => some .rename
  | 10 => some .syncDirectory
  | 11 => some .removeStaging
  | _ => none

private theorem Operation.ofCode_code (operation : Operation) :
    Operation.ofCode operation.code = some operation := by
  cases operation <;> rfl

/-- Every phase, so the fault matrix enumerates them rather than sampling.

    A list beside an inductive can fall behind it, so the matrix checks it both
    ways: every code that decodes is in here, and everything in here decodes
    back to itself. A phase added to the inductive and not to this list is a
    phase with a code the first half finds and the list does not hold. -/
def Operation.all : List Operation :=
  [.openBase, .ownBase, .walkDirectory, .ownDirectory, .createStaging, .writeBytes,
    .syncFile, .closeFile, .rename, .syncDirectory, .removeStaging]

/-- The errno the phase reported, as a value.

    Closed for the ones a release write can actually meet, with `other` carrying
    the raw number for anything else — so an unrecognised errno is reported
    honestly as a number rather than folded into a catch-all name that reads
    like a diagnosis. `notOwned` has no errno: it is the ownership refusal,
    which is this pipeline's rule and not the kernel's. -/
inductive Errno where
  | eacces | eperm | eexist | enoent | enotdir | eisdir | eloop | einval
  | eio | enospc | erofs | edquot | emfile | enfile | enomem | ebadf
  | enametoolong | ebusy | eintr | enotsup
  | notOwned
  | other (raw : Nat)
  deriving DecidableEq, Repr

/-- The name to print. Rendering a name is not classifying one: nothing reads
    this back. -/
def Errno.name : Errno → String
  | .eacces => "EACCES"
  | .eperm => "EPERM"
  | .eexist => "EEXIST"
  | .enoent => "ENOENT"
  | .enotdir => "ENOTDIR"
  | .eisdir => "EISDIR"
  | .eloop => "ELOOP"
  | .einval => "EINVAL"
  | .eio => "EIO"
  | .enospc => "ENOSPC"
  | .erofs => "EROFS"
  | .edquot => "EDQUOT"
  | .emfile => "EMFILE"
  | .enfile => "ENFILE"
  | .enomem => "ENOMEM"
  | .ebadf => "EBADF"
  | .enametoolong => "ENAMETOOLONG"
  | .ebusy => "EBUSY"
  | .eintr => "EINTR"
  | .enotsup => "ENOTSUP"
  | .notOwned => "not owned by this user"
  | .other raw => s!"errno {raw}"

/-- The half of the fix the errno determines, where it determines one. `none`
    leaves the phase's own remedy to say it. -/
def Errno.remedy : Errno → Option String
  | .eacces | .eperm =>
      some "The permissions on the path refuse this user."
  | .eexist =>
      some "Something is already at that name."
  | .enoent =>
      some "A directory in the name does not exist; this write creates no directories."
  | .enotdir =>
      some "A component of the name is not a directory."
  | .eloop =>
      some "A component of the name is a symbolic link, which is refused rather than followed."
  | .enospc | .edquot =>
      some "The filesystem is out of space or over quota."
  | .erofs =>
      some "The filesystem is mounted read-only."
  | .notOwned =>
      some "The directory belongs to another user."
  | _ => none

private def notOwnedCode : Nat := 21
private def otherCode : Nat := 99

/-- The wire code. As with `Operation.code`, `0` is reserved for "no error". -/
def Errno.code : Errno → Nat
  | .eacces => 1
  | .eperm => 2
  | .eexist => 3
  | .enoent => 4
  | .enotdir => 5
  | .eisdir => 6
  | .eloop => 7
  | .einval => 8
  | .eio => 9
  | .enospc => 10
  | .erofs => 11
  | .edquot => 12
  | .emfile => 13
  | .enfile => 14
  | .enomem => 15
  | .ebadf => 16
  | .enametoolong => 17
  | .ebusy => 18
  | .eintr => 19
  | .enotsup => 20
  | .notOwned => notOwnedCode
  | .other _ => otherCode

/-- The raw number, carried only by `other`. A named errno encodes a zero here,
    so one value has one encoding — which is what makes a row that names an
    errno *and* carries a stray number a refusal rather than a second spelling
    of the same error. -/
def Errno.raw : Errno → Nat
  | .other raw => raw
  | _ => 0

private def namedErrnoOfCode : Nat → Option Errno
  | 1 => some .eacces
  | 2 => some .eperm
  | 3 => some .eexist
  | 4 => some .enoent
  | 5 => some .enotdir
  | 6 => some .eisdir
  | 7 => some .eloop
  | 8 => some .einval
  | 9 => some .eio
  | 10 => some .enospc
  | 11 => some .erofs
  | 12 => some .edquot
  | 13 => some .emfile
  | 14 => some .enfile
  | 15 => some .enomem
  | 16 => some .ebadf
  | 17 => some .enametoolong
  | 18 => some .ebusy
  | 19 => some .eintr
  | 20 => some .enotsup
  | 21 => some .notOwned
  | _ => none

def Errno.ofCode (code raw : Nat) : Option Errno :=
  if code == otherCode then some (.other raw)
  else if raw == 0 then namedErrnoOfCode code
  else none

private theorem Errno.ofCode_code (errno : Errno) :
    Errno.ofCode errno.code errno.raw = some errno := by
  cases errno <;> rfl

/-- Every named errno, checked against the codes the same way `Operation.all`
    is. `other` is not here: it is a family rather than a value. -/
def Errno.named : List Errno :=
  [.eacces, .eperm, .eexist, .enoent, .enotdir, .eisdir, .eloop, .einval,
    .eio, .enospc, .erofs, .edquot, .emfile, .enfile, .enomem, .ebadf,
    .enametoolong, .ebusy, .eintr, .enotsup, .notOwned]

/-- A phase and what it reported. The two structured fields ADR-0028 requires,
    and the whole of what the native side says about a failure. -/
structure NativeError where
  operation : Operation
  errno : Errno
  deriving DecidableEq, Repr

/-- One sentence about a native error, ending in what to do. -/
def NativeError.describe (error : NativeError) : String :=
  let cause := s!"{error.operation.describe} failed with {error.errno.name}"
  match error.errno.remedy with
  | none => s!"{cause}. {error.operation.remedy}"
  | some hint => s!"{cause}. {hint} {error.operation.remedy}"

/-- How hard the bytes were pushed before the rename.

    Both are accepted by release policy, and the ADR says why: this mechanism
    needs the replacement to be atomic *within the run*, not to survive power
    loss after the run has died. `fullBarrier` is Darwin's `F_FULLFSYNC`;
    `ordinaryFsync` is what a filesystem that documents no support for it gets,
    and recording which one happened is what keeps that from being invisible. -/
inductive SyncStrength where
  | fullBarrier
  | ordinaryFsync
  deriving DecidableEq, Repr

def SyncStrength.describe : SyncStrength → String
  | .fullBarrier => "flushed through the drive's write barrier"
  | .ordinaryFsync => "flushed with an ordinary fsync"

/-- Whether the directory entry itself was flushed after the rename.

    Separate from the commit, because it happens *after* it. A failure here is
    not a failed write — the replacement is visible to every later open in this
    run — so it is reported and not raised. -/
inductive DirectorySync where
  | synced
  | unsynced (error : NativeError)
  deriving DecidableEq, Repr

/-- What became of the staging sibling.

    `notCreated` and `removed` are both "nothing is left behind", and they are
    kept apart because only the second one means this invocation touched that
    path. `retained` is the one a rerun has to know about: the next attempt
    refuses to write through an occupied staging name, so a leftover is a
    failure that repeats until someone removes it. -/
inductive CleanupDisposition where
  | notCreated
  | removed
  | retained (error : NativeError)
  deriving DecidableEq, Repr

/-- Everything the mechanism reports about one write. -/
inductive WriteOutcome where
  /-- The rename happened. The destination holds the new bytes. -/
  | committed (strength : SyncStrength) (directory : DirectorySync)
  /-- The rename did not happen. The destination holds whatever it held. -/
  | failedBeforeCommit (error : NativeError) (cleanup : CleanupDisposition)
  deriving DecidableEq, Repr

/-- Did the bytes replace the destination? The one question every caller asks,
    and the one the interim writer answered by whether it threw. -/
def WriteOutcome.landed : WriteOutcome → Bool
  | .committed _ _ => true
  | .failedBeforeCommit _ _ => false

/-! ### What the destination and the staging path look like afterwards

The mechanism's observation predicts the directory's state, and stating the
prediction here is what lets a fault test compare the real directory against
something other than a second reading of the same code. -/

/-- What the destination path holds after the write. -/
inductive Destination where
  /-- The bytes that were passed in. -/
  | replaced
  /-- Whatever was there before, byte for byte — including nothing. -/
  | untouched
  deriving DecidableEq, Repr

/-- What the staging path holds after the write. -/
inductive Staging where
  /-- Nothing: either never created, or created and removed. -/
  | absent
  /-- A file this invocation created and could not remove. -/
  | occupied
  deriving DecidableEq, Repr

def WriteOutcome.destination : WriteOutcome → Destination
  | .committed _ _ => .replaced
  | .failedBeforeCommit _ _ => .untouched

def WriteOutcome.staging : WriteOutcome → Staging
  | .committed _ _ => .absent
  | .failedBeforeCommit _ .notCreated => .absent
  | .failedBeforeCommit _ .removed => .absent
  | .failedBeforeCommit _ (.retained _) => .occupied

/-- **The destination changed exactly when the write committed.**

    The direction that matters is right to left: an outcome that did not commit
    can never predict replaced bytes, so a fault test comparing the destination
    against this prediction is checking the mechanism rather than agreeing with
    it. -/
theorem WriteOutcome.destination_replaced_iff_landed (outcome : WriteOutcome) :
    outcome.destination = .replaced ↔ outcome.landed = true := by
  cases outcome with
  | committed _ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | failedBeforeCommit _ _ =>
      exact ⟨fun contradiction => Destination.noConfusion contradiction,
        fun contradiction => Bool.noConfusion contradiction⟩

/-- **Something is left at the staging path exactly when cleanup retained it.**

    Which is the fact a rerun depends on: the next attempt creates that sibling
    exclusively, so anything left there fails the *next* write too. -/
theorem WriteOutcome.staging_occupied_iff_retained (outcome : WriteOutcome) :
    outcome.staging = .occupied ↔
      ∃ error cleanupError, outcome = .failedBeforeCommit error (.retained cleanupError) := by
  cases outcome with
  | committed _ _ =>
      exact ⟨fun contradiction => Staging.noConfusion contradiction,
        fun ⟨_, _, absurdity⟩ => WriteOutcome.noConfusion absurdity⟩
  | failedBeforeCommit error cleanup =>
      cases cleanup with
      | notCreated =>
          exact ⟨fun contradiction => Staging.noConfusion contradiction,
            fun ⟨_, _, absurdity⟩ => by
              injection absurdity with _ cleanupEq
              exact CleanupDisposition.noConfusion cleanupEq⟩
      | removed =>
          exact ⟨fun contradiction => Staging.noConfusion contradiction,
            fun ⟨_, _, absurdity⟩ => by
              injection absurdity with _ cleanupEq
              exact CleanupDisposition.noConfusion cleanupEq⟩
      | retained cleanupError => exact ⟨fun _ => ⟨error, cleanupError, rfl⟩, fun _ => rfl⟩

/-! ## The row the native side reports

Nine numbers, because a structured value is what keeps a message string from
becoming a contract. The layout is regular: a tag, two small enumerations, and
two error triples.

```text
0  tag           0 committed, 1 failedBeforeCommit
1  strength      committed: 0 fullBarrier, 1 ordinaryFsync   failed: 0
2  disposition   committed: 0 synced, 1 unsynced             failed: 0 notCreated, 1 removed, 2 retained
3  operation ┐   committed: the directory sync's error, present exactly when unsynced
4  errno     │   failed:    the failing phase's error, always present
5  raw errno ┘
6  operation ┐   committed: nothing (0, 0, 0)
7  errno     │   failed:    the cleanup error, present exactly when retained
8  raw errno ┘
```

Every slot that carries no error is `(0, 0, 0)` and a row that fills one anyway
is refused, so there is exactly one row per outcome. That is what
`decodeRow_encodeRow` and `decodeRow_landed_iff` are about, and between them
they rule out both silent failures: an outcome the decoder rejects, and a row
the decoder reads as a write that landed when the mechanism did not say so. -/

/-- The tag a committed write carries. -/
def committedTag : Nat := 0

/-- The tag a write that did not commit carries. -/
def failedTag : Nat := 1

/-- The wire code for a sync strength. -/
def SyncStrength.code : SyncStrength → Nat
  | .fullBarrier => 0
  | .ordinaryFsync => 1

/-- One outcome as the row that reports it. The native side builds the same
    numbers; this exists so the decoder can be characterised against something
    total rather than against a C function nothing in Lean can call.

    Written out slot by slot rather than assembled from pieces, because the row
    *is* the contract and a reader of it should not have to evaluate list
    concatenation to see what is in slot six. -/
def encodeRow : WriteOutcome → List Nat
  | .committed strength .synced =>
      [committedTag, strength.code, 0, 0, 0, 0, 0, 0, 0]
  | .committed strength (.unsynced error) =>
      [committedTag, strength.code, 1,
        error.operation.code, error.errno.code, error.errno.raw, 0, 0, 0]
  | .failedBeforeCommit error .notCreated =>
      [failedTag, 0, 0,
        error.operation.code, error.errno.code, error.errno.raw, 0, 0, 0]
  | .failedBeforeCommit error .removed =>
      [failedTag, 0, 1,
        error.operation.code, error.errno.code, error.errno.raw, 0, 0, 0]
  | .failedBeforeCommit error (.retained cleanupError) =>
      [failedTag, 0, 2,
        error.operation.code, error.errno.code, error.errno.raw,
        cleanupError.operation.code, cleanupError.errno.code, cleanupError.errno.raw]

private def malformed (why : String) : String :=
  s!"the release writer reported an outcome this build cannot read: {why}. The row the native side writes and the row this decodes are one contract; a mismatch means they were changed apart, which is a defect in the release tool rather than something you invoked wrongly."

private def decodeError (operation errno raw : Nat) : Except String NativeError :=
  match Operation.ofCode operation with
  | none => .error (malformed s!"phase {operation} is not one this build knows")
  | some operation =>
      match Errno.ofCode errno raw with
      | none =>
          .error (malformed s!"errno code {errno} with raw {raw} is not a value this build knows")
      | some errno => .ok { operation, errno }

private theorem decodeError_encode (error : NativeError) :
    decodeError error.operation.code error.errno.code error.errno.raw = .ok error := by
  simp only [decodeError, Operation.ofCode_code, Errno.ofCode_code]

private def decodeAbsent (operation errno raw : Nat) : Except String Unit :=
  if operation == 0 then
    if errno == 0 then
      if raw == 0 then .ok ()
      else .error (malformed "a slot that carries no error carries a raw errno")
    else .error (malformed "a slot that carries no error names an errno")
  else .error (malformed "a slot that carries no error names a phase")

private def decodeStrength (strength : Nat) : Except String SyncStrength :=
  if strength == 0 then .ok .fullBarrier
  else if strength == 1 then .ok .ordinaryFsync
  else .error (malformed s!"sync strength {strength} is not one this build knows")

private theorem decodeStrength_encode (strength : SyncStrength) :
    decodeStrength strength.code = .ok strength := by
  cases strength <;> rfl

private def decodeCommitted : List Nat → Except String (SyncStrength × DirectorySync)
  | [strength, disposition, operation, errno, raw, operation', errno', raw'] =>
      match decodeStrength strength with
      | .error message => .error message
      | .ok strength =>
          match decodeAbsent operation' errno' raw' with
          | .error message => .error message
          | .ok () =>
              if disposition == 0 then
                match decodeAbsent operation errno raw with
                | .error message => .error message
                | .ok () => .ok (strength, .synced)
              else if disposition == 1 then
                match decodeError operation errno raw with
                | .error message => .error message
                | .ok error => .ok (strength, .unsynced error)
              else
                .error (malformed s!"directory sync {disposition} is not one this build knows")
  | row => .error (malformed s!"a row has 9 fields and this one has {row.length + 1}")

private def decodeFailed : List Nat → Except String (NativeError × CleanupDisposition)
  | [strength, disposition, operation, errno, raw, operation', errno', raw'] =>
      if strength != 0 then
        .error (malformed "a write that did not commit reported a sync strength, which it never reaches")
      else
        match decodeError operation errno raw with
        | .error message => .error message
        | .ok error =>
            if disposition == 0 then
              match decodeAbsent operation' errno' raw' with
              | .error message => .error message
              | .ok () => .ok (error, .notCreated)
            else if disposition == 1 then
              match decodeAbsent operation' errno' raw' with
              | .error message => .error message
              | .ok () => .ok (error, .removed)
            else if disposition == 2 then
              match decodeError operation' errno' raw' with
              | .error message => .error message
              | .ok cleanupError => .ok (error, .retained cleanupError)
            else
              .error (malformed s!"cleanup disposition {disposition} is not one this build knows")
  | row => .error (malformed s!"a row has 9 fields and this one has {row.length + 1}")

/-- Read the mechanism's row.

    Total, and a refusal rather than a default on everything it does not
    recognise: the one reading this cannot ask the writer again, so a row it
    half-understands has to be a refusal or it becomes a write that reads as
    successful. -/
def decodeRow (row : List Nat) : Except String WriteOutcome :=
  match row with
  | [] => .error (malformed "the row is empty")
  | tag :: rest =>
      if tag == committedTag then
        match decodeCommitted rest with
        | .error message => .error message
        | .ok (strength, directory) => .ok (.committed strength directory)
      else if tag == failedTag then
        match decodeFailed rest with
        | .error message => .error message
        | .ok (error, cleanup) => .ok (.failedBeforeCommit error cleanup)
      else .error (malformed s!"outcome tag {tag} is not one this build knows")

/-- Read a row as it crosses the FFI boundary. The native side hands over an
    array of 32-bit words; everything about *what they mean* is above. -/
def decode (row : Array UInt32) : Except String WriteOutcome :=
  decodeRow (row.toList.map UInt32.toNat)

/-- **Every outcome the mechanism can report is one this reads back unchanged.**

    The silent failure this rules out is the opposite of the one below: a write
    that really did commit, reported in a row the decoder refuses, becomes a
    release step that fails after doing its work — and a rerun of that step then
    meets its own staging file. -/
theorem decodeRow_encodeRow (outcome : WriteOutcome) :
    decodeRow (encodeRow outcome) = .ok outcome := by
  cases outcome with
  | committed strength directory =>
      cases directory with
      | synced =>
          simp only [encodeRow, decodeRow, decodeCommitted, decodeStrength_encode]
          rfl
      | unsynced error =>
          simp only [encodeRow, decodeRow, decodeCommitted, decodeStrength_encode,
            decodeError_encode]
          rfl
  | failedBeforeCommit error cleanup =>
      cases cleanup with
      | notCreated =>
          simp only [encodeRow, decodeRow, decodeFailed, decodeError_encode]
          rfl
      | removed =>
          simp only [encodeRow, decodeRow, decodeFailed, decodeError_encode]
          rfl
      | retained cleanupError =>
          simp only [encodeRow, decodeRow, decodeFailed, decodeError_encode]
          rfl

/-- **A decoded write reports itself as landed only if the mechanism said so.**

    This is the false negative that matters, and it is why the decoder is a
    verdict function rather than a parser: everything downstream — the signed
    manifest, the SBOM hashed into `SHA256SUMS`, the pin the standalone verifier
    reads — is trusted on the strength of a write having happened. A row the
    decoder read generously would make a release step report success over a file
    that was never replaced.

    Stated over the tag rather than over the whole row on purpose: the claim is
    that `landed` tracks the mechanism's own commit report and cannot be
    manufactured by anything else in the row. -/
theorem decodeRow_landed_iff {row : List Nat} {outcome : WriteOutcome}
    (decoded : decodeRow row = .ok outcome) :
    outcome.landed = true ↔ row.head? = some committedTag := by
  cases row with
  | nil => simp only [decodeRow, reduceCtorEq] at decoded
  | cons tag rest =>
      simp only [decodeRow] at decoded
      by_cases isCommitted : tag == committedTag
      · have tagEq : tag = committedTag := beq_iff_eq.mp isCommitted
        rw [if_pos isCommitted] at decoded
        cases decodedPair : decodeCommitted rest with
        | error message => rw [decodedPair] at decoded; simp only [reduceCtorEq] at decoded
        | ok pair =>
            obtain ⟨strength, directory⟩ := pair
            rw [decodedPair] at decoded
            simp only at decoded
            injection decoded with outcomeEq
            subst outcomeEq
            simp only [WriteOutcome.landed, List.head?, tagEq]
      · have tagNe : ¬ tag = committedTag := fun equal =>
          isCommitted (by rw [equal]; exact beq_self_eq_true _)
        rw [if_neg isCommitted] at decoded
        by_cases isFailed : tag == failedTag
        · rw [if_pos isFailed] at decoded
          cases decodedPair : decodeFailed rest with
          | error message => rw [decodedPair] at decoded; simp only [reduceCtorEq] at decoded
          | ok pair =>
              obtain ⟨error, cleanup⟩ := pair
              rw [decodedPair] at decoded
              simp only at decoded
              injection decoded with outcomeEq
              subst outcomeEq
              simp only [WriteOutcome.landed, List.head?]
              exact ⟨fun contradiction => Bool.noConfusion contradiction,
                fun headEq => absurd (Option.some.inj headEq) tagNe⟩
        · rw [if_neg isFailed] at decoded
          simp only [reduceCtorEq] at decoded

/-! ## What a command does with the observation -/

/-- What to tell the operator about a write that did not happen. -/
def WriteOutcome.refusal (destination : String) (staging : String)
    (error : NativeError) (cleanup : CleanupDisposition) : String :=
  let leftovers :=
    match cleanup with
    | .notCreated => "Nothing was left behind."
    | .removed => s!"The staging file {staging} was removed."
    | .retained cleanupError =>
        s!"The staging file {staging} is still there: {cleanupError.describe}"
  s!"could not write {destination}: {error.describe} {destination} still holds what it held. {leftovers}"

/-- What to disclose about a write that did happen but could not be fully
    flushed. `none` when there is nothing to disclose.

    A disclosure and not a refusal, and that is the ADR's decision rather than
    this function's: the rename succeeded, so every later open in this run reads
    the new bytes. Reporting it as a failure would send an operator to repair a
    file that is already correct. -/
def WriteOutcome.disclosure (destination : String) : WriteOutcome → Option String
  | .committed _ .synced => none
  | .committed _ (.unsynced error) =>
      some s!"{destination} was replaced, and only the directory entry's flush did not complete: {error.describe}"
  | .failedBeforeCommit _ _ => none

/-- The command-level reading of an outcome: a refusal carrying what to do, or
    the bytes landed plus anything worth disclosing.

    `staging` is passed rather than derived so the message names the exact path
    a rerun will meet, which is the only thing an operator can act on. -/
def accept (destination staging : String) : WriteOutcome → Except String (Option String)
  | .failedBeforeCommit error cleanup =>
      .error (WriteOutcome.refusal destination staging error cleanup)
  | outcome@(.committed _ _) => .ok (outcome.disclosure destination)

/-- **A write is accepted exactly when it committed.**

    The whole reason `accept` is a function over the typed outcome instead of a
    `try`/`catch` around an `IO Unit`: neither an unflushed directory entry nor
    a retained staging file can turn into a refusal, and no failure before the
    rename can turn into an acceptance. -/
theorem accept_isOk_iff_landed (destination staging : String) (outcome : WriteOutcome) :
    (accept destination staging outcome).toOption.isSome = outcome.landed := by
  cases outcome with
  | committed strength directory =>
      cases directory <;> rfl
  | failedBeforeCommit error cleanup => rfl

/-! ## The seam

The mechanism is a parameter, so every phase failure is reachable from a test
without a filesystem that can produce it — an `EIO` from a dying disk, a
`syncDirectory` failure after a successful rename, a cleanup that could not
remove what it created. The real one arrives with the native writer and is the
only thing that changes here. -/

/-- Perform one write and report what happened, as a row.

    Deliberately the whole write rather than the individual steps: the phases
    run against file descriptors the caller never sees, which is what keeps the
    directory the bytes land in the same one that was checked. -/
abbrev Mechanism :=
  OutputDirectory → OutputPath → ByteArray → IO (Array UInt32)

/-- Write, decode, and read the observation as a command would.

    The two failures are kept apart deliberately. A row this build cannot read
    is a defect in the release tool; a write that did not commit is a refusal
    about the filesystem. Both refuse — nothing here reports a write that did
    not happen as one that did — and each says which it was. -/
def through (mechanism : Mechanism) (base : OutputDirectory) (path : OutputPath)
    (contents : ByteArray) : IO (Except String (Option String)) := do
  match ← (mechanism base path contents).toBaseIO with
  | .error error =>
      return .error s!"could not write {path.render} in {base.path}: {error}"
  | .ok row =>
      match decode row with
      | .error message => return .error message
      | .ok outcome =>
          return accept (base.locate path.render) (base.locate path.stagingRender) outcome

end Release.Write
