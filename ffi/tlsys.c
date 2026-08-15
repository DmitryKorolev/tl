/*
 * tlsys.c — the native primitives shim (ADR-0019).
 *
 * Mechanism only: OS primitives the pinned Lean toolchain cannot express or
 * does not contractually guarantee — no-follow opens (walked component by
 * component, so a symlink at ANY path component is refused, ADR-0015 §6),
 * fsync (F_FULLFSYNC on Darwin, where plain fsync stops at the drive cache),
 * fd locks, OS CSPRNG entropy, the ownership check, and the release tool's
 * capability-anchored atomic replacement. Policy — what to refuse, error
 * codes, retry loops — lives in tested Lean above this (Tl/Store/Sys.lean and
 * its callers; release/Sys.lean and release/Write.lean for the release side).
 *
 * The two sides are separate surfaces on purpose. `tl_sys_*` is the product's;
 * `tl_release_*` is release administration's, which ADR-0028 keeps out of the
 * product TCB. A release-side binding to a `tl_sys_*` symbol would put one
 * inside the other, and the drift gate refuses it.
 *
 * The shim owns its file descriptors end to end and touches no Lean runtime
 * internals beyond the documented FFI surface (lean.h), so toolchain bumps
 * cannot break it. Errors surface as IO userError strings of the fixed shape
 * "tlsys:<op>:<ERRNO-NAME>: <detail>"; the Lean side branches on the token.
 *
 * POSIX is the gating, fully-tested path (Linux, macOS, Windows-via-WSL —
 * ADR-0006/0015 §7). Native Win32 is deferred and undistributed: deliberately
 * not implemented here; building for it yields honest unsupported errors,
 * never a silently weaker primitive.
 */
#include <lean/lean.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32

static lean_obj_res tl_sys_unsupported(const char *op) {
    char buf[256];
    snprintf(buf, sizeof buf,
             "tlsys:%s:ENOSYS: native Windows is not supported — the Win32 primitives are "
             "unimplemented (ADR-0006); run tl under WSL2", op);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

LEAN_EXPORT lean_obj_res tl_sys_open(b_lean_obj_arg base, b_lean_obj_arg rel, uint32_t flags, lean_obj_arg w) {
    (void)base; (void)rel; (void)flags; (void)w; return tl_sys_unsupported("open");
}
LEAN_EXPORT lean_obj_res tl_sys_read_all(uint32_t fd, lean_obj_arg w) {
    (void)fd; (void)w; return tl_sys_unsupported("read_all");
}
LEAN_EXPORT lean_obj_res tl_sys_write_all(uint32_t fd, b_lean_obj_arg data, lean_obj_arg w) {
    (void)fd; (void)data; (void)w; return tl_sys_unsupported("write_all");
}
LEAN_EXPORT lean_obj_res tl_sys_sync(uint32_t fd, lean_obj_arg w) {
    (void)fd; (void)w; return tl_sys_unsupported("sync");
}
LEAN_EXPORT lean_obj_res tl_sys_try_lock(uint32_t fd, uint8_t exclusive, lean_obj_arg w) {
    (void)fd; (void)exclusive; (void)w; return tl_sys_unsupported("try_lock");
}
LEAN_EXPORT lean_obj_res tl_sys_unlock(uint32_t fd, lean_obj_arg w) {
    (void)fd; (void)w; return tl_sys_unsupported("unlock");
}
LEAN_EXPORT lean_obj_res tl_sys_entropy(uint32_t n, lean_obj_arg w) {
    (void)n; (void)w; return tl_sys_unsupported("entropy");
}
LEAN_EXPORT lean_obj_res tl_sys_owned_by_caller(uint32_t fd, lean_obj_arg w) {
    (void)fd; (void)w; return tl_sys_unsupported("owned_by_caller");
}
LEAN_EXPORT lean_obj_res tl_sys_close(uint32_t fd, lean_obj_arg w) {
    (void)fd; (void)w; return tl_sys_unsupported("close");
}
LEAN_EXPORT lean_obj_res tl_sys_mkdir(b_lean_obj_arg base, b_lean_obj_arg rel, lean_obj_arg w) {
    (void)base; (void)rel; (void)w; return tl_sys_unsupported("mkdir");
}
LEAN_EXPORT lean_obj_res tl_release_write_atomic(b_lean_obj_arg base, b_lean_obj_arg components,
                                          b_lean_obj_arg contents, lean_obj_arg w) {
    (void)base; (void)components; (void)contents; (void)w;
    return tl_sys_unsupported("release_write_atomic");
}

#else /* POSIX */

#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/types.h>
#if defined(__APPLE__) || defined(__linux__)
#include <sys/random.h>
#endif

/* Synthetic token for the ADR-0015 §6 ownership refusal (no errno fits). */
#define TL_E_NOTOWNED (-9001)

static const char *tl_errno_name(int e) {
    if (e == TL_E_NOTOWNED) return "ENOTOWNED";
    switch (e) {
    case ELOOP: return "ELOOP";
    case EEXIST: return "EEXIST";
    case ENOENT: return "ENOENT";
    case EACCES: return "EACCES";
    case EPERM: return "EPERM";
    case ENOTDIR: return "ENOTDIR";
    case EISDIR: return "EISDIR";
    case EINVAL: return "EINVAL";
    case EAGAIN: return "EAGAIN";
#if EWOULDBLOCK != EAGAIN
    case EWOULDBLOCK: return "EWOULDBLOCK";
#endif
    case EINTR: return "EINTR";
    case ENOMEM: return "ENOMEM";
    case EMFILE: return "EMFILE";
    case EBADF: return "EBADF";
    case EIO: return "EIO";
    default: return "EOTHER";
    }
}

static lean_obj_res tl_sys_err(const char *op, int e) {
    char buf[512];
    const char *detail =
        (e == TL_E_NOTOWNED) ? "path component not owned by the caller" : strerror(e);
    snprintf(buf, sizeof buf, "tlsys:%s:%s: %s", op, tl_errno_name(e), detail);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

/* Flag bits — keep in sync with Tl/Store/Sys.lean. */
#define TL_F_WRITE 1u
#define TL_F_APPEND 2u
#define TL_F_CREATE_EXCL 4u
#define TL_F_TRUNCATE 8u
#define TL_F_DIRECTORY 16u
#define TL_F_CREATE 32u

/* The ADR-0015 §6 ownership check, applied to every opened component. */
static int tl_owned_by_caller(int fd) {
    struct stat st;
    if (fstat(fd, &st) != 0) return -1;
    return st.st_uid == geteuid() ? 1 : 0;
}

/*
 * Open `rel` under the directory `base`, refusing a symlink at ANY `rel`
 * component (openat(O_NOFOLLOW) per component) AND refusing any component
 * not owned by the caller (ADR-0015 §6 — the check rides every open, so no
 * caller can forget it). The base itself keeps NORMAL symlink/ownership
 * semantics — the §6 discipline is scoped to the `.tl` components; a repo
 * root reached through a symlinked ancestor (a macOS /var temp dir, a
 * symlinked home) is legitimate. An empty base means the current directory.
 * Returns the fd, or -1 with *err_out set (TL_E_NOTOWNED for ownership).
 */
static int tl_open_walk(const char *base, const char *rel, int final_flags, int *err_out) {
    if (rel[0] == '\0') { *err_out = EINVAL; return -1; }
    char *dup = strdup(rel);
    if (!dup) { *err_out = ENOMEM; return -1; }
    int dirfd = AT_FDCWD;
    if (base[0] != '\0') {
        dirfd = open(base, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        if (dirfd < 0) { *err_out = errno; free(dup); return -1; }
    }
    char *save = NULL;
    char *tok = strtok_r(dup, "/", &save);
    if (!tok) { *err_out = EINVAL; free(dup); if (dirfd != AT_FDCWD) close(dirfd); return -1; }
    while (tok) {
        char *next = strtok_r(NULL, "/", &save);
        int fd;
        if (next) {
            fd = openat(dirfd, tok, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        } else {
            fd = openat(dirfd, tok, final_flags | O_NOFOLLOW | O_CLOEXEC, 0644);
        }
        int e = errno;
        if (dirfd != AT_FDCWD) close(dirfd);
        if (fd < 0) { *err_out = e; free(dup); return -1; }
        int owned = tl_owned_by_caller(fd);
        if (owned != 1) {
            *err_out = (owned == 0) ? TL_E_NOTOWNED : errno;
            close(fd);
            free(dup);
            return -1;
        }
        dirfd = fd;
        tok = next;
    }
    free(dup);
    return dirfd;
}

LEAN_EXPORT lean_obj_res tl_sys_open(b_lean_obj_arg base, b_lean_obj_arg rel, uint32_t flags, lean_obj_arg w) {
    (void)w;
    int final_flags;
    if (flags & TL_F_DIRECTORY) {
        final_flags = O_RDONLY | O_DIRECTORY;
    } else if (flags & (TL_F_WRITE | TL_F_APPEND | TL_F_CREATE_EXCL | TL_F_TRUNCATE | TL_F_CREATE)) {
        final_flags = O_WRONLY;
        if (flags & TL_F_APPEND) final_flags |= O_APPEND;
        if (flags & TL_F_CREATE_EXCL) final_flags |= O_CREAT | O_EXCL;
        if (flags & TL_F_CREATE) final_flags |= O_CREAT;
        if (flags & TL_F_TRUNCATE) final_flags |= O_TRUNC;
    } else {
        final_flags = O_RDONLY;
    }
    int err = 0;
    int fd = tl_open_walk(lean_string_cstr(base), lean_string_cstr(rel), final_flags, &err);
    if (fd < 0) return tl_sys_err("open", err);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/*
 * Create `rel` (a path of components) under `base`, like a no-follow
 * createDirAll: each component is mkdirat'd (EEXIST tolerated) then opened
 * with openat(O_NOFOLLOW|O_DIRECTORY) and ownership-checked before descending
 * — so a symlink planted as any component (e.g. `.tl/log -> /elsewhere`) is
 * refused (ELOOP / TL_E_NOTOWNED), never followed and created through
 * (ADR-0015 §6). Idempotent. Returns unit.
 */
LEAN_EXPORT lean_obj_res tl_sys_mkdir(b_lean_obj_arg base, b_lean_obj_arg rel, lean_obj_arg w) {
    (void)w;
    const char *base_c = lean_string_cstr(base);
    char *dup = strdup(lean_string_cstr(rel));
    if (!dup) return tl_sys_err("mkdir", ENOMEM);
    int dirfd = AT_FDCWD;
    if (base_c[0] != '\0') {
        dirfd = open(base_c, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        if (dirfd < 0) { int e = errno; free(dup); return tl_sys_err("mkdir", e); }
    }
    char *save = NULL;
    for (char *tok = strtok_r(dup, "/", &save); tok; tok = strtok_r(NULL, "/", &save)) {
        if (mkdirat(dirfd, tok, 0755) != 0 && errno != EEXIST) {
            int e = errno;
            if (dirfd != AT_FDCWD) close(dirfd);
            free(dup);
            return tl_sys_err("mkdir", e);
        }
        int fd = openat(dirfd, tok, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        int e = errno;
        if (dirfd != AT_FDCWD) close(dirfd);
        if (fd < 0) { free(dup); return tl_sys_err("mkdir", e); }
        int owned = tl_owned_by_caller(fd);
        if (owned != 1) {
            int oe = (owned == 0) ? TL_E_NOTOWNED : errno;
            close(fd);
            free(dup);
            return tl_sys_err("mkdir", oe);
        }
        dirfd = fd;
    }
    if (dirfd != AT_FDCWD) close(dirfd);
    free(dup);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res tl_sys_read_all(uint32_t fd, lean_obj_arg w) {
    (void)w;
    size_t cap = 65536, len = 0;
    uint8_t *buf = malloc(cap);
    if (!buf) return tl_sys_err("read_all", ENOMEM);
    for (;;) {
        if (len == cap) {
            cap *= 2;
            uint8_t *nbuf = realloc(buf, cap);
            if (!nbuf) { free(buf); return tl_sys_err("read_all", ENOMEM); }
            buf = nbuf;
        }
        ssize_t n = read((int)fd, buf + len, cap - len);
        if (n < 0) {
            if (errno == EINTR) continue;
            int e = errno; free(buf); return tl_sys_err("read_all", e);
        }
        if (n == 0) break;
        len += (size_t)n;
    }
    lean_object *arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), buf, len);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res tl_sys_write_all(uint32_t fd, b_lean_obj_arg data, lean_obj_arg w) {
    (void)w;
    const uint8_t *ptr = lean_sarray_cptr((lean_object *)data);
    size_t len = lean_sarray_size((lean_object *)data);
    size_t off = 0;
    while (off < len) {
        ssize_t n = write((int)fd, ptr + off, len - off);
        if (n < 0) {
            if (errno == EINTR) continue;
            return tl_sys_err("write_all", errno);
        }
        off += (size_t)n;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res tl_sys_sync(uint32_t fd, lean_obj_arg w) {
    (void)w;
#if defined(__APPLE__)
    /* Plain fsync on Darwin stops at the drive cache; F_FULLFSYNC is the
       actual durability barrier (ADR-0019). Fall back if the fs lacks it. */
    if (fcntl((int)fd, F_FULLFSYNC) == 0)
        return lean_io_result_mk_ok(lean_box(0));
#endif
    for (;;) {
        if (fsync((int)fd) == 0) return lean_io_result_mk_ok(lean_box(0));
        if (errno != EINTR) return tl_sys_err("sync", errno);
    }
}

LEAN_EXPORT lean_obj_res tl_sys_try_lock(uint32_t fd, uint8_t exclusive, lean_obj_arg w) {
    (void)w;
    int op = (exclusive ? LOCK_EX : LOCK_SH) | LOCK_NB;
    for (;;) {
        if (flock((int)fd, op) == 0) return lean_io_result_mk_ok(lean_box(1));
        if (errno == EWOULDBLOCK || errno == EAGAIN) return lean_io_result_mk_ok(lean_box(0));
        if (errno != EINTR) return tl_sys_err("try_lock", errno);
    }
}

LEAN_EXPORT lean_obj_res tl_sys_unlock(uint32_t fd, lean_obj_arg w) {
    (void)w;
    if (flock((int)fd, LOCK_UN) != 0) return tl_sys_err("unlock", errno);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res tl_sys_entropy(uint32_t n, lean_obj_arg w) {
    (void)w;
    lean_object *arr = lean_alloc_sarray(1, n, n);
    uint8_t *ptr = lean_sarray_cptr(arr);
    uint32_t off = 0;
    while (off < n) {
        /* getentropy is capped at 256 bytes per call */
        size_t chunk = (n - off > 256) ? 256 : (size_t)(n - off);
        if (getentropy(ptr + off, chunk) != 0) {
            int e = errno;
            lean_dec_ref(arr);
            return tl_sys_err("entropy", e);
        }
        off += (uint32_t)chunk;
    }
    return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res tl_sys_owned_by_caller(uint32_t fd, lean_obj_arg w) {
    (void)w;
    struct stat st;
    if (fstat((int)fd, &st) != 0) return tl_sys_err("owned_by_caller", errno);
    return lean_io_result_mk_ok(lean_box(st.st_uid == geteuid() ? 1 : 0));
}

LEAN_EXPORT lean_obj_res tl_sys_close(uint32_t fd, lean_obj_arg w) {
    (void)w;
    if (close((int)fd) != 0 && errno != EINTR) return tl_sys_err("close", errno);
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * ============================================================================
 * Release administration's atomic evidence write (ADR-0028).
 *
 * Separate from everything above, and deliberately shaped differently. The
 * product's primitives hand a formatted userError back to Lean and let the
 * caller recover a class from the token in it. This one reports a row of
 * numbers, because release policy branches on which phase failed and on
 * whether the write committed, and a classification that reads a message
 * string makes rewording that string a silent behaviour change.
 *
 * The row is nine slots, and release/Write.lean is the other half of the
 * contract:
 *
 *   0 tag          0 committed, 1 failed before the commit
 *   1 strength     committed: 0 full barrier, 1 ordinary fsync; failed: 0
 *   2 disposition  committed: 0 synced, 1 unsynced
 *                  failed:    0 nothing created, 1 removed, 2 retained
 *   3..5           committed: the directory sync's error, iff unsynced
 *                  failed:    the failing phase's error, always
 *   6..8           committed: nothing; failed: the cleanup error, iff retained
 *
 * A triple is (phase, errno code, raw errno), and (0, 0, 0) means "no error
 * here". Only an errno this file cannot name carries a raw number; a named one
 * carries zero, so one outcome has exactly one row.
 *
 * The base is opened with ordinary symlink semantics, on purpose: it is the
 * directory the operator named, and applying no-follow to it would refuse a
 * macOS /var temporary directory, a symlinked home, and most container mounts.
 * The no-follow and ownership walk starts at the first component BENEATH the
 * held base descriptor. Everything after that is done through descriptors, so
 * renaming an ancestor mid-run cannot move where the bytes land.
 * ============================================================================
 */

/* Phase codes — keep in sync with `Operation.code` in release/Write.lean. */
#define TL_W_OPEN_BASE 1
#define TL_W_OWN_BASE 2
#define TL_W_WALK_DIRECTORY 3
#define TL_W_OWN_DIRECTORY 4
#define TL_W_CREATE_STAGING 5
#define TL_W_WRITE_BYTES 6
#define TL_W_SYNC_FILE 7
#define TL_W_CLOSE_FILE 8
#define TL_W_RENAME 9
#define TL_W_SYNC_DIRECTORY 10
#define TL_W_REMOVE_STAGING 11

/* Errno codes — keep in sync with `Errno.code` in release/Write.lean. */
#define TL_W_ENOTOWNED 21
#define TL_W_EOTHER 99

/* The suffix the staging sibling gets. release/Write.lean renders the same
   name for the message an operator has to act on, so the two must agree. */
#define TL_W_STAGING_SUFFIX ".tmp"

/* An errno as the closed code release/Write.lean knows, or 0 if it has no
   name there — in which case the raw number travels in the next slot rather
   than being folded into a name that would read like a diagnosis. */
static uint32_t tl_release_errno_code(int e) {
    switch (e) {
    case EACCES: return 1;
    case EPERM: return 2;
    case EEXIST: return 3;
    case ENOENT: return 4;
    case ENOTDIR: return 5;
    case EISDIR: return 6;
    case ELOOP: return 7;
    case EINVAL: return 8;
    case EIO: return 9;
    case ENOSPC: return 10;
    case EROFS: return 11;
#ifdef EDQUOT
    case EDQUOT: return 12;
#endif
    case EMFILE: return 13;
    case ENFILE: return 14;
    case ENOMEM: return 15;
    case EBADF: return 16;
    case ENAMETOOLONG: return 17;
    case EBUSY: return 18;
    case EINTR: return 19;
    case ENOTSUP: return 20;
#if defined(EOPNOTSUPP) && EOPNOTSUPP != ENOTSUP
    case EOPNOTSUPP: return 20;
#endif
    default: return 0;
    }
}

/* One error triple, written into `row` at `at`. `e` is a real errno, or the
   synthetic ownership refusal, which has no errno because it is this
   pipeline's rule rather than the kernel's. */
static void tl_release_put_error(uint32_t *row, size_t at, uint32_t phase, int e) {
    row[at] = phase;
    if (e == TL_E_NOTOWNED) {
        row[at + 1] = TL_W_ENOTOWNED;
        row[at + 2] = 0;
        return;
    }
    uint32_t code = tl_release_errno_code(e);
    if (code == 0) {
        row[at + 1] = TL_W_EOTHER;
        row[at + 2] = (e > 0) ? (uint32_t)e : 0;
    } else {
        row[at + 1] = code;
        row[at + 2] = 0;
    }
}

static lean_obj_res tl_release_row(const uint32_t *row) {
    lean_object *array = lean_alloc_array(9, 9);
    for (size_t i = 0; i < 9; i++)
        lean_array_set_core(array, i, lean_box_uint32(row[i]));
    return lean_io_result_mk_ok(array);
}

/* A write that never reached the rename. `created` says whether this
   invocation is the one that made the staging sibling, which is the only thing
   that entitles it to remove one: an occupied staging path is evidence, and
   removing another run's file would destroy it. */
static lean_obj_res tl_release_failed(uint32_t phase, int e, int dirfd,
                                      const char *staging, int created) {
    uint32_t row[9] = {1, 0, 0, 0, 0, 0, 0, 0, 0};
    tl_release_put_error(row, 3, phase, e);
    if (created) {
        if (unlinkat(dirfd, staging, 0) == 0) {
            row[2] = 1;
        } else {
            row[2] = 2;
            tl_release_put_error(row, 6, TL_W_REMOVE_STAGING, errno);
        }
    }
    return tl_release_row(row);
}

/*
 * Flush the staging file's bytes. Returns 0 on success with *strength set, or
 * the errno to refuse with.
 *
 * On Darwin an interrupted F_FULLFSYNC is retried, and only a documented
 * "this filesystem does not do that" result falls back to ordinary fsync — an
 * EIO or ENOSPC surfacing here is the write failing, and answering it with a
 * weaker flush would report a barrier that did not happen. Elsewhere fsync is
 * the platform's barrier, so there is nothing to fall back from.
 */
static int tl_release_sync_file(int fd, uint32_t *strength) {
#if defined(__APPLE__)
    for (;;) {
        if (fcntl(fd, F_FULLFSYNC) == 0) { *strength = 0; return 0; }
        if (errno == EINTR) continue;
        if (errno == ENOTSUP || errno == EINVAL || errno == ENOTTY
#if defined(EOPNOTSUPP) && EOPNOTSUPP != ENOTSUP
            || errno == EOPNOTSUPP
#endif
        ) break;
        return errno;
    }
    *strength = 1;
#else
    *strength = 0;
#endif
    for (;;) {
        if (fsync(fd) == 0) return 0;
        if (errno != EINTR) return errno;
    }
}

LEAN_EXPORT lean_obj_res tl_release_write_atomic(b_lean_obj_arg base, b_lean_obj_arg components,
                                          b_lean_obj_arg contents, lean_obj_arg w) {
    (void)w;
    uint32_t row[9] = {1, 0, 0, 0, 0, 0, 0, 0, 0};
    size_t count = lean_array_size((lean_object *)components);
    if (count == 0) {
        /* release/Write.lean's output name cannot be empty by construction, so
           this is unreachable from the Lean side and is answered rather than
           assumed away. */
        tl_release_put_error(row, 3, TL_W_OPEN_BASE, EINVAL);
        return tl_release_row(row);
    }

    int dirfd = open(lean_string_cstr(base), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dirfd < 0) {
        tl_release_put_error(row, 3, TL_W_OPEN_BASE, errno);
        return tl_release_row(row);
    }
    int owned = tl_owned_by_caller(dirfd);
    if (owned != 1) {
        int e = (owned == 0) ? TL_E_NOTOWNED : errno;
        close(dirfd);
        tl_release_put_error(row, 3, TL_W_OWN_BASE, e);
        return tl_release_row(row);
    }

    /* Everything before the last component is a directory to descend into,
       no-follow and ownership-checked. The components arrive as an array and
       are used one at a time: nothing here re-splits a path string, so there
       is no second parser to disagree with the one that validated them. */
    for (size_t i = 0; i + 1 < count; i++) {
        const char *component = lean_string_cstr(lean_array_get_core((lean_object *)components, i));
        int next = openat(dirfd, component, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        int e = errno;
        close(dirfd);
        if (next < 0) {
            tl_release_put_error(row, 3, TL_W_WALK_DIRECTORY, e);
            return tl_release_row(row);
        }
        dirfd = next;
        owned = tl_owned_by_caller(dirfd);
        if (owned != 1) {
            int oe = (owned == 0) ? TL_E_NOTOWNED : errno;
            close(dirfd);
            tl_release_put_error(row, 3, TL_W_OWN_DIRECTORY, oe);
            return tl_release_row(row);
        }
    }

    const char *leaf = lean_string_cstr(lean_array_get_core((lean_object *)components, count - 1));
    size_t staging_len = strlen(leaf) + sizeof TL_W_STAGING_SUFFIX;
    char *staging = malloc(staging_len);
    if (!staging) {
        close(dirfd);
        tl_release_put_error(row, 3, TL_W_CREATE_STAGING, ENOMEM);
        return tl_release_row(row);
    }
    snprintf(staging, staging_len, "%s%s", leaf, TL_W_STAGING_SUFFIX);

    /* Exclusive and no-follow: every pre-existing object at the staging name
       refuses the write before a byte is written, including a dangling symlink
       an existence check cannot see. */
    int fd = openat(dirfd, staging, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0644);
    if (fd < 0) {
        int e = errno;
        lean_obj_res result = tl_release_failed(TL_W_CREATE_STAGING, e, dirfd, staging, 0);
        close(dirfd);
        free(staging);
        return result;
    }

    const uint8_t *bytes = lean_sarray_cptr((lean_object *)contents);
    size_t length = lean_sarray_size((lean_object *)contents);
    size_t written = 0;
    int failure = 0;
    uint32_t phase = TL_W_WRITE_BYTES;
    while (written < length) {
        ssize_t n = write(fd, bytes + written, length - written);
        if (n < 0) {
            if (errno == EINTR) continue;
            failure = errno;
            break;
        }
        if (n == 0) {
            /* A regular file write returning zero is not a short write to
               retry; nothing is making progress and looping would hang. */
            failure = EIO;
            break;
        }
        written += (size_t)n;
    }

    uint32_t strength = 0;
    if (failure == 0) {
        failure = tl_release_sync_file(fd, &strength);
        if (failure != 0) phase = TL_W_SYNC_FILE;
    }

    /* Closed either way: the descriptor is this function's to release. A close
       error is only the write's error when nothing has failed yet, since it can
       be the first report of a deferred write failure. */
    if (close(fd) != 0 && failure == 0 && errno != EINTR) {
        failure = errno;
        phase = TL_W_CLOSE_FILE;
    }

    if (failure != 0) {
        lean_obj_res result = tl_release_failed(phase, failure, dirfd, staging, 1);
        close(dirfd);
        free(staging);
        return result;
    }

    if (renameat(dirfd, staging, dirfd, leaf) != 0) {
        lean_obj_res result = tl_release_failed(TL_W_RENAME, errno, dirfd, staging, 1);
        close(dirfd);
        free(staging);
        return result;
    }
    free(staging);

    /* Past here the replacement has happened and every later open in this run
       reads the new bytes, so a directory-sync failure is reported as an
       unsynced commit rather than as a write that did not occur. */
    row[0] = 0;
    row[1] = strength;
    row[2] = 0;
    for (size_t i = 3; i < 9; i++) row[i] = 0;
    for (;;) {
        if (fsync(dirfd) == 0) break;
        if (errno == EINTR) continue;
        row[2] = 1;
        tl_release_put_error(row, 3, TL_W_SYNC_DIRECTORY, errno);
        break;
    }
    close(dirfd);
    return tl_release_row(row);
}

#endif /* POSIX */
