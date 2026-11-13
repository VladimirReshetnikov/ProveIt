# Small confined Lean scratch experiment

`poc.sh` creates a private user/mount namespace and 16 MiB tmpfs, then runs a
real Lean toy compilation with a read-only host-root bind, a writable scratch
bind, and TMPDIR inside scratch. Selected device nodes are explicitly bound.
It tests successful object and TMPDIR writes, denied writes to `/tmp` and
`/dev` outside scratch, and a scratch overflow reporting ENOSPC. It unmounts
and removes its scratch directory on normal exit. The script does not run a
project build or establish confinement of every possible descendant, device,
shared-memory, kernel or network write path. Tmpfs can use swap, and no
host-wide free-space reserve is guaranteed.

The reproducible script actually exited 0 and printed the object SHA-256
`ee8c6c64689e1dfa6d2686f366793215c7b956d4140ab64c1be484e828fc07c3`,
16,777,216 bytes used of 16,777,216, and
`PASS_CONFINED_LEAN_TOY output TMPDIR outside-tmp-dev-denied ENOSPC`.
Earlier exploratory controls are relevant: the first 1 MiB test falsely
appeared to pass because read-only `/dev/null` prevented the negative commands
from executing; a later test with only null/zero bound failed because Lean
needed `/dev/urandom` (actual exit 1). The final script explicitly binds
null, zero, urandom and random and checks the overflow message. These toy
observations do not authorize or predict a full rebuild.
