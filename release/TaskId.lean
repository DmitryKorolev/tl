/-
The no-task-ID-leakage gate (AGENTS.md, "Artifacts must be human-readable";
ADR-0026), as a decision this tool makes rather than one a shell script
assembles out of `git grep`.

The rule is unchanged: the ADR-0007 display affix followed by at least four
Crockford base32 digits, opened by a token boundary, anywhere in a tracked file
outside `docs/`, `README.md` and the placeholder registry. A token in scope is a
leak unless the registry lists it, and registering one is where a human asserts
it is a synthetic id rather than a reference into a tracker.

What changes is how many places state that rule. The shell held it in three: an
extended regular expression for the line scan, a second one for pulling the
tokens off a matching line, and a pathspec whose selftest compared it against a
`git ls-files | grep -v` spelling of the same scope. Here the class is one total
function over bytes, the scope is one predicate over paths, and the shapes the
scan must keep matching are a table in `Tests/ReleaseToolTests.lean` rather than
a selftest arm inside the thing it tests.

Three differences from the shell are deliberate, and none of them narrows what
the gate catches:

- The token boundary now governs extraction as well as detection. The shell
  applied it only to the line scan and then re-extracted tokens without it, so
  on a line that already held a match, a run of digits after a word ending in
  the affix's letters — which the documented rule does not call a token, since
  nothing opens it — counted as an unregistered one.
- Files are read as bytes. There is no locale to set and no binary sniff to
  defeat: `git grep` needed `-a` and `LC_ALL=C` to reach a blob a
  `.gitattributes` marking or a NUL byte would otherwise have hidden.
- A tracked symlink is counted and not read, which is what `git grep` does with
  one. Its content is a path rather than the target's bytes, and where the
  target is itself tracked it is scanned as its own entry. The count is
  disclosed rather than dropped, so the scope a run covered is legible from the
  run.

The registry is read from the checkout rather than compiled in: it is data a
human edits in the same change as the placeholder, and a gate carrying its own
copy would pass on a registration the tree does not have.
-/
import release.Command
import release.Process

namespace Release

namespace TaskId

/-! ## The lexical rule

Bytes rather than characters, because that is the unit the scan is defined over:
a tracked file is a byte string. No byte of a multi-byte sequence is a Crockford
digit or a word character, so such a sequence can never extend a token, and every
one of its bytes *opens* a boundary — which is both what `git grep` under
`LC_ALL=C` did with the same bytes and the conservative direction, since a token
written straight after a non-ASCII character is still found. Each byte is read as
the character of the same code point purely so the classes read like the ones
ADR-0026 states. -/

/-- The display affix (ADR-0007). Assembled from here rather than written into
    the scan, so this module can state what it looks for without holding a
    literal the gate would then have to excuse in its own source. -/
def affix : String := "tl-"

/-- `shortIdFloor`: the fewest digits that make a display id, and so the fewest
    that make a token. -/
def digitFloor : Nat := 4

/-- Crockford base32 (`0-9 a-z` minus `i l o u`), in either case.

    Case-insensitive because the id surface is: `Tl/Cli/Resolve` lowercases a
    token before testing the affix, so `TL-…`, `Tl-…` and `tl-…` resolve to the
    same issue and are equally a leak. The *symbol* aliases (`o`→`0`, `i`/`l`→`1`)
    stay out, which is an ADR-0026 residual rather than an oversight: admitting
    them would match this project's own vocabulary. -/
def isCrockford (c : Char) : Bool :=
  if '0' ≤ c && c ≤ '9' then true
  else
    let lower := c.toLower
    'a' ≤ lower && lower ≤ 'z'
      && lower != 'i' && lower != 'l' && lower != 'o' && lower != 'u'

/-- What may precede the affix: anything that is not a word character. A hyphen
    and a slash are both boundaries, so an id written after either is still a
    token, while one whose affix is glued to the end of a word is not — the
    boundary is what keeps a compound from hiding a match without making every
    word that ends in the affix's letters into one. -/
def isBoundary (c : Char) : Bool :=
  !(('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_')

/-- The byte at `index`, read as a character; out of range reads as NUL, which
    is neither a Crockford digit nor a word character and so ends a token and
    opens a boundary exactly the way the end of the file should. -/
private def charAt (bytes : ByteArray) (index : Nat) : Char :=
  if index < bytes.size then Char.ofNat (bytes.get! index).toNat else '\x00'

/-- One token, and the line it sits on. -/
structure Finding where
  line : Nat
  token : String
  deriving Repr, BEq

/-- How many Crockford digits run from `index`. -/
private def runLength (bytes : ByteArray) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, index =>
      if isCrockford (charAt bytes index) then 1 + runLength bytes fuel (index + 1) else 0

private def tokenAt (bytes : ByteArray) (start length : Nat) : String :=
  (List.range length).foldl (fun text offset => text.push (charAt bytes (start + offset))) ""

/-- Every token in `bytes`, in the order they occur, each with its line.

    A candidate that fails resumes at the next byte rather than after what it
    read: text that writes the affix twice before a long enough run carries a
    token starting inside the failed candidate, and a scan that consumed what it
    read would step over it — the same case a backtracking regular expression
    finds by trying every start position. The
    retry is bounded by the length of a Crockford run, so the pass stays linear
    in practice; a token itself is skipped over, and no token can start inside
    one because every byte of it is a word character. -/
private def scanFrom (bytes : ByteArray) (index line : Nat) (found : List Finding) :
    List Finding :=
  if bound : index < bytes.size then
    let current := charAt bytes index
    let opened := index == 0 || isBoundary (charAt bytes (index - 1))
    let affixHere := opened && current.toLower == 't'
      && (charAt bytes (index + 1)).toLower == 'l' && charAt bytes (index + 2) == '-'
    let digits := if affixHere then runLength bytes bytes.size (index + 3) else 0
    if affixHere && digits ≥ digitFloor then
      -- No byte of a token is a newline, so stepping over one keeps the line.
      scanFrom bytes (index + 3 + digits) line
        ({ line, token := tokenAt bytes index (3 + digits) } :: found)
    else
      scanFrom bytes (index + 1) (if current == '\n' then line + 1 else line) found
  else found.reverse
  termination_by bytes.size - index
  decreasing_by
    · exact Nat.sub_lt_sub_left bound
        (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos 2)) (Nat.le_add_right _ _))
    · exact Nat.sub_lt_sub_left bound (Nat.lt_succ_self index)

/-- Every token in a tracked file's bytes. -/
def findings (bytes : ByteArray) : List Finding := scanFrom bytes 0 1 []

/-- Every token in a string, for the corpus rows that state the rule. -/
def findingsIn (text : String) : List Finding := findings text.toUTF8

/-! ## The registry -/

/-- Where the placeholder registry lives, relative to the checkout. Part of the
    pinned contract (ADR-0026), so it is named here and not passed in: a run
    that could be pointed at another file could be pointed at one that excuses
    everything. -/
def registryRelative : String := "scripts/task-id-placeholders.txt"

/-- The registered placeholders, lowercased.

    Both sides of the comparison fold case, because the CLI resolves both: a
    placeholder written the way the CLI also accepts must not read as a leak,
    and a registry line that shouted would otherwise excuse nothing. -/
def registryTokens (text : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    let entry := line.trimAscii.toString.toLower
    if entry.isEmpty then none else some entry

/-- One token that is in scope and not registered. -/
structure Leak where
  path : String
  line : Nat
  token : String
  deriving Repr, BEq, DecidableEq

def Leak.render (leak : Leak) : String := s!"{leak.path}:{leak.line}: {leak.token}"

/-- The tokens of one file that the registry does not excuse. Every token is
    checked, not only the first: a leak sharing a line with a registered
    placeholder is still a leak. -/
def unregistered (registry : List String) (path : String) (found : List Finding) :
    List Leak :=
  found.filterMap fun finding =>
    if registry.contains finding.token.toLower then none
    else some { path, line := finding.line, token := finding.token }

/-! ## The scope -/

/-- Every tracked file except the two prose surfaces that render sample CLI
    output and the registry itself (ADR-0026).

    Fail-open by construction in the direction that matters: a new top-level
    file is in scope without anyone adding it, and only these three exclusions
    take one out. -/
def inScope (path : String) : Bool :=
  !path.startsWith "docs/" && path != "README.md" && path != registryRelative

/-- A tracked entry: what git says it is, and where it is. -/
structure Entry where
  mode : String
  path : String
  deriving Repr, BEq, DecidableEq

/-- Whether an entry is a regular file, and so something to read. The other
    modes a tree carries — a symlink, a submodule — have no bytes at that path
    to scan, which is why `git grep` passes over them too. -/
def Entry.isRegularFile (entry : Entry) : Bool :=
  entry.mode == "100644" || entry.mode == "100755"

/-- One `git ls-files -s -z` record: `<mode> <object> <stage>\t<path>`.

    A record this cannot read is a refusal rather than a skipped file. The one
    shape that reaches it is a path holding a tab, which is exactly the case
    where guessing which side is the path would scan the wrong file or none. -/
def parseEntry (record : String) : Except String Entry :=
  match record.splitOn "\t" with
  | [metadata, path] =>
      match metadata.splitOn " " with
      | [mode, _object, _stage] =>
          if path.isEmpty then .error s!"a tracked entry carries no path: '{record}'"
          else .ok { mode, path }
      | _ => .error s!"could not read the mode of a tracked entry: '{record}'"
  | _ => .error s!"could not read a tracked entry as '<mode> <object> <stage><tab><path>': '{record}'"

/-- One entry per path, or a refusal.

    `git ls-files -s` writes a record per index stage, so a path in an unresolved
    merge arrives two or three times — consecutively, the index being ordered by
    path and then stage. Reading it once per stage would scan one working-tree
    file repeatedly and report a single leak as several. `git grep` reads such a
    path once, and so does this.

    Keeping one stage and discarding the rest is only sound while they agree
    about whether the path has bytes. A type-change conflict — a symlink on one
    side, a regular file on the other — lists both, and then the stage that
    happens to be kept decides whether the working tree's file is scanned at all:
    keeping the symlink stage counts the path as unread and passes over a file
    that is really there. There is no honest guess between them, so a path whose
    stages disagree is a refusal. -/
def collapseStages (entries : List Entry) : Except String (List Entry) :=
  let (kept, ambiguous) := entries.foldl
    (fun (state : List Entry × List String) entry =>
      let (kept, ambiguous) := state
      match kept with
      | previous :: _ =>
          if previous.path != entry.path then (entry :: kept, ambiguous)
          else if previous.isRegularFile == entry.isRegularFile then state
          else (kept, entry.path :: ambiguous)
      | [] => ([entry], ambiguous))
    ([], [])
  if ambiguous.isEmpty then .ok kept.reverse
  else
    .error s!"the index lists {String.intercalate ", " ambiguous.eraseDups} at more than one stage, and the stages disagree about whether the path has bytes to read — a symlink at one and a regular file at another, which an unresolved type-change conflict produces. Which stage this kept would decide whether the working tree's file is scanned at all, so it refuses instead. Resolve the merge, then run this again."

/-- Every tracked entry in a `git ls-files -s -z` listing. The trailing NUL
    leaves an empty final record, which is the listing's terminator and not an
    entry. -/
def parseEntries (listing : String) : Except String (List Entry) :=
  ((listing.splitOn "\x00").filter (!·.isEmpty)).mapM parseEntry

/-! ## The decision -/

/-- One or many, for a count a human reads. -/
private def plural (n : Nat) (one many : String) : String := if n == 1 then one else many

private def lintOptions : List OptionSpec :=
  [{ name := "root", takesValue := true }]

private structure LintArgs where
  root : String

private def lintArgs (options : Options) : Except String LintArgs := do
  return { root := ← options.required "root" }

/-- The tracked entries of the checkout at `root`.

    From git rather than from a directory walk, because "tracked" is the scope
    ADR-0026 states and only git knows it: a walk would read build output, an
    editor's scratch file and anything else the tree happens to hold, and would
    miss nothing but would report on files no reader can fix. -/
private def trackedEntries (root : String) : Decision (List Entry) := do
  let listing ← ofIO (do
    match ← Release.succeededGit #["-C", root, "ls-files", "-s", "-z", "--"] with
    | .ok output => return .ok output.stdout
    | .error message =>
        return .error s!"could not list the tracked files under {root}: {message}. This gate reads its scope from git, so it must be run against a checkout.")
  ofExcept (parseEntries listing)

private def lintDecision (args : LintArgs) : Decision String := do
  let registryPath := args.root ++ "/" ++ registryRelative
  let registryText ← attempt
    s!"could not read {registryPath}. The registry is part of this gate's pinned contract (ADR-0026): it is the exclusion set, and its absence means the file was removed rather than that nothing is registered. Restore it rather than removing the gate's exclusions"
    (IO.FS.readFile registryPath)
  let registry := registryTokens registryText
  if registry.isEmpty then
    decline s!"{registryPath} holds no placeholder. The registry is part of this gate's pinned contract (ADR-0026): it is the exclusion set, and an empty one means the file was truncated rather than that nothing is registered. Restore it rather than removing the gate's exclusions."
  let entries ← trackedEntries args.root
  let collapsed ← ofExcept (collapseStages entries)
  let inspected := collapsed.filter (fun entry => inScope entry.path)
  if inspected.isEmpty then
    decline s!"no tracked file under {args.root} is in scope. Every tracked file except docs/, README.md and {registryRelative} is (ADR-0026), so an empty scope means the listing was read wrongly rather than that there is nothing to check — a scan over nothing must not report clean."
  let readable := inspected.filter (·.isRegularFile)
  let unread := inspected.filter (!·.isRegularFile)
  if readable.isEmpty then
    decline s!"no tracked file under {args.root} has bytes to scan: every one of the {inspected.length} in scope is a symlink or a submodule. A scan that read nothing must not report clean, for the same reason an empty scope must not."
  let perFile ← readable.mapM fun entry => do
    let filePath : String := args.root ++ "/" ++ entry.path
    let bytes ← attempt
      s!"could not read {entry.path}, which git tracks. The working tree has to hold every file the index lists for this scan to cover the scope it reports"
      (IO.FS.readBinFile filePath)
    return unregistered registry entry.path (findings bytes)
  let leaks := perFile.flatten
  if leaks.isEmpty then
    let disclosure :=
      if unread.isEmpty then ""
      else
        s!", and {unread.length} tracked {plural unread.length "entry" "entries"} with no bytes at that path (a symlink or a submodule) counted and not read — a symlink's content is a path, and where its target is tracked it is scanned as its own entry"
    return s!"clean — no tracker id in {readable.length} tracked {plural readable.length "file" "files"}{disclosure}"
  decline (s!"task-tracker id in a tracked artifact. Code and comments must stand on their own — describe the substance instead (AGENTS.md, \"Artifacts must be human-readable\"). If one of these is a test or example placeholder rather than a reference into the tracker, register it in {registryRelative} in this same change.\n"
    ++ String.join (leaks.map fun leak => s!"  {leak.render}\n"))

private def lintCommand : Command :=
  optionCommand "task-id-lint" "--root <dir>"
    "Refuse a tracker id in a tracked artifact outside docs/ and README.md."
    ["--root", "."]
    lintOptions lintArgs lintDecision

def taskIdCommands : List Command := [lintCommand]

end TaskId

export TaskId (taskIdCommands)

end Release
