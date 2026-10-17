#!/usr/bin/env bash
# DEV ONLY (not used by CI). neard raises RLIMIT_NOFILE to 65535 at start and
# exits ("couldn't set the file descriptor limit") when the hard limit is
# lower, as in some containers. This builds an LD_PRELOAD shim that makes
# setrlimit/prlimit for RLIMIT_NOFILE report success, and runs "$@" under it.
# CI's macOS runners don't need it.
#
#   scripts/dev-nofile-shim.sh scripts/run-sandbox.sh
set -euo pipefail
out="${TMPDIR:-/tmp}/nofile-shim.so"
if [ ! -f "$out" ]; then
    src="$(mktemp --suffix=.c)"
    cat > "$src" <<'C'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <sys/resource.h>
#include <sys/types.h>
typedef int (*setrl_t)(__rlimit_resource_t, const struct rlimit *);
typedef int (*prl_t)(pid_t, __rlimit_resource_t, const struct rlimit64 *, struct rlimit64 *);
int setrlimit(__rlimit_resource_t r, const struct rlimit *l) {
    if (r == RLIMIT_NOFILE) return 0;
    return ((setrl_t)dlsym(RTLD_NEXT, "setrlimit"))(r, l);
}
int setrlimit64(__rlimit_resource_t r, const struct rlimit64 *l) {
    if (r == RLIMIT_NOFILE) return 0;
    return ((setrl_t)dlsym(RTLD_NEXT, "setrlimit64"))(r, (const struct rlimit *)l);
}
int prlimit64(pid_t p, __rlimit_resource_t r, const struct rlimit64 *n, struct rlimit64 *o) {
    prl_t real = (prl_t)dlsym(RTLD_NEXT, "prlimit64");
    if (r == RLIMIT_NOFILE && n) return real(p, r, 0, o);
    return real(p, r, n, o);
}
C
    gcc -shared -fPIC -O2 -o "$out" "$src" -ldl
    rm -f "$src"
fi
LD_PRELOAD="$out${LD_PRELOAD:+:$LD_PRELOAD}" exec "$@"
