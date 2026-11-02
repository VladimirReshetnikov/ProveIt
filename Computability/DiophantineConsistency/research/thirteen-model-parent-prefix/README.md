# Proposed coherent 2011 parent-zero prefix rebuild

This is a **builder and preflight packet**, not a completed build, an
actual-zero theorem, a rank-phase theorem, or an iPRA proof. It selects the
20 frozen project sources reachable from `ArithmeticHalfBinomial2011`, a
subset of the separately reviewed 44-source extension. That prefix contains
the actual 2011 scalar equations, carrier power, rank-population lower bound,
and the required `PAHF`/`FirstOrder` source imports. An actual-zero caller
must still be written and checked; the remaining 24-source window/rank
extension is not rebuilt by this driver.

[`replay.py`](replay.py) is designed to compile the 20 frozen sources in
topological order on each of the two independently audited 70-source parent
libraries. It uses fresh symlink overlays, checks every direct `lean --deps`
result against the declared imports, guards the direct object/companion
inputs, records logs and child exits, and demands matching corresponding
source, object and log hashes. It rechecks the independent source-freezer and
70-source parent audits before and after. Its accepted invocation is
`python3 -I -S`; it rejects optimized Python and fresh outputs anywhere other
than directly below `/tmp` with the expected name prefix. The actual launcher
and any future output need an independent exact-byte prelaunch review.

Each Lean compiler is invoked with `-M4000 -j1`, and the inherited independently
reviewed monitor samples leader RSS and `/tmp` free space once per second. It
requests termination above 3.5 GiB sampled RSS, below 4 GiB sampled free
space, or after 300 seconds per module; these are sampled stops, **not** hard
memory/disk quotas or continuously enforced reserves. The monitored process
and descendants outside a verified process group, mutations between checks,
and package-transitive/dynamic imports remain outside these guarantees. The
original Foundation build wrapper's outer exit remains unobserved. A failed or
interrupted attempt must be retained as such, without inferring child exit
from a progress file.

## Read-only preflight

The exact current driver SHA-256 and observed controls are recorded in
[`preflight-observation.json`](preflight-observation.json). Session 70371
actually exited 0 with `PREFLIGHT_PASS 20 sampled_free_bytes 5732978688`;
no Lean build or output directory was created. Direct optimized and
non-isolated invocation controls exited 1 before build work. The preflight
checks the frozen manifest and current-source audit, the 70-source parent
audit, all 44 frozen source bytes and direct external pins, current fallback
namespace absence, fresh output path, and one free-space sample. It does not
independently test or run the entire builder loop. The `--preflight-only`
option is read-only except for the audited freezer's temporary test snapshot,
which its review script removes; its pass is not permission to skip the
independent launcher review or a claim that future resources remain available.
