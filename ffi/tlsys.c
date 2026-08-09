/*
 * tlsys.c — the native primitives shim (ADR-0019).
 *
 * Mechanism only: OS primitives the pinned Lean toolchain cannot express or
 * does not contractually guarantee — no-follow opens (walked component by
 * component, so a symlink at ANY path component is refused, ADR-0015 §6),
 * fsync (F_FULLFSYNC on Darwin, where plain fsync stops at the drive cache),
 * fd locks, OS CSPRNG entropy, and the ownership check. Policy — what to
 * refuse, error codes, retry loops — lives in tested Lean above this
 * (Tl/Store/Sys.lean and its callers).
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

#endif /* POSIX */
