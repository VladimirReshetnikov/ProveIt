/* Windows shim standing in for `landrun` (which is Linux-only).
   Mirrors scripts/fake-landrun.sh: swallow landrun's own flags, then exec the
   rest.  Provides NO sandboxing - fine here, we are only testing comparator's
   *verification* logic, not its isolation. */
#include <stdio.h>
#include <string.h>
#include <process.h>

static int is_value_flag(const char *f) {
    static const char *vf[] = {"--ro","--rox","--rw","--rwx","--bind-tcp",
                               "--connect-tcp","--log-level","--env", NULL};
    for (int i = 0; vf[i]; i++) if (strcmp(f, vf[i]) == 0) return 1;
    return 0;
}

int main(int argc, char **argv) {
    int i = 1;
    if (i < argc && (strcmp(argv[i],"-V")==0 || strcmp(argv[i],"--version")==0)) {
        fprintf(stderr, "XXX NOT LANDRUN, FAKE SHIM XXX\n"); return 0;
    }
    while (i < argc) {
        if (strcmp(argv[i], "--") == 0) { i++; break; }
        if (argv[i][0] == '-') { if (is_value_flag(argv[i])) i++; i++; }
        else break;
    }
    if (i >= argc) { fprintf(stderr, "landrun shim: no command given\n"); return 2; }
    fprintf(stderr, "WARNING: FAKE LANDRUN - running unsandboxed: %s\n", argv[i]);
    fflush(stderr);
    return (int)_spawnvp(_P_WAIT, argv[i], (const char * const *)(argv + i));
}
