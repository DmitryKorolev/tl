---
name: verify
description: Build and drive the tl binary end-to-end to verify a change against its real CLI surface (throwaway repos, real git, real sync legs). Use when verifying that a tl code change works, before committing.
---

# Verifying a tl change end-to-end

Build and locate the binary (from the repo/worktree root):

    lake exe cache get   # mathlib oleans; fast when the pin is cached
    lake build           # must be warning-free
    TL=$PWD/.lake/build/bin/tl

Drive it only in throwaway repos — never against this repo's real `.tl/`
(`tl sync` here pushes refs/tl/log to the GitHub origin). Always set
`TL_ACTOR=tl-dev` for writes.

    S=$(mktemp -d)            # scratch root
    git init -q $S/a && cd $S/a
    $TL init --json           # REQUIRED before anything else (no-project error otherwise)
    $TL create "task" --json
    $TL sync --json           # local leg only until a remote exists

Remote leg: `git init --bare -q $S/bare && git remote add origin $S/bare`,
then `tl sync` pushes; a second repo `git clone $S/bare $S/b` + `tl init`
+ `tl sync` exercises pull/merge. A fresh-bare clone prints git's
empty-repository warning — harmless.

Inspect transport state with plumbing, not tl: `git ls-tree refs/tl/log`,
`git rev-parse refs/tl/log` (tip stability = no-churn), `ls .tl/log/`
(what got materialized). To craft a foreign/junk tree entry the way a
foreign writer would:

    OID=$(echo content | git hash-object -w --stdin)
    T=$( (git ls-tree refs/tl/log; printf '100644 blob %s\tNAME\n' $OID) | git mktree)
    C=$(GIT_AUTHOR_NAME=tl GIT_AUTHOR_EMAIL=tl@localhost \
        GIT_COMMITTER_NAME=tl GIT_COMMITTER_EMAIL=tl@localhost \
        git commit-tree $T -p $(git rev-parse refs/tl/log) -m x)
    git update-ref refs/tl/log $C

Every command takes `--json`; assert on `ok`, `data`, and the top-level
`notes` array (non-fatal disclosures). `tl doctor --json` → `data.healthy`
is the end-of-run health check. A pre-change binary for before/after
comparison usually exists in the main checkout's `.lake/build/bin/tl`.
