# Independent 338+4 successor prelaunch audit

The committed freezer, snapshot and launcher in `3a03b220a6` passed this
**no-Lean prelaunch review**, subject to the operating and post-build
conditions below. The [receipt](CHECK.json) records the tested exact hashes,
actual sessions and evidence hashes. The separately committed supplemental
notes do not change the reviewed freezer or launcher bytes.

The [snapshot check](snapshot_check.py) exited 0 in session 74050: the tracked
and retained manifest match, its freezer hash matches the committed freezer,
and all 338 frozen source files match their workspace bytes, plan hashes and
the pinned `ca2b5071e3` Git blobs. It confirms the 807 seed names and the
338-source order. The launcher itself pins the manifest but does not pin the
freezer script or check the manifest's freezer-hash field; that provenance
relationship was checked separately here at this observation point. Freezer
preflight session 36716 and launcher preflight session 56174 both exited 0,
rerunning the audited plan, seed/direct-output companion and external guards.
The 27 external module guards and the 807 historical seed closure remain
point-in-time observations, not continuous protection.

The [fake-loop test](fake_loop.py) exited 0 in session 50777. It runs the
actual launcher loop with an injected fake dependency executable and fake
compiler/monitor, producing 342 rows per sibling and testing a separate
synthetic `sorryAx` failure. It checked 685 fake dependency queries and 685
fake compiles in total, child environment scrubbing, and matching fake
outputs. This is neither a Lean build nor a test of the real monitor's
resource enforcement. Separate actual-monitor controls exited 0 in session
66999 for missing/transient RSS, fast exit, exceptions and external SIGTERM;
they exercised verified leader and same-group descendant cleanup. Sampled
RSS, disk and timeout controls also exited 0 using harmless sleeping children.
These are sampled stops, not whole-tree hard quotas, continuous reservations,
or a guarantee for descendants that escape the verified group.

The startup/output [controls](guard_test.py) rejected non-isolated and
optimized Python, occupied outputs and output symlinks; the synthetic
[companion controls](guard_drift_test.py) rejected changed, missing and
unexpected files. A native [loader canary](loader_test.py) executed before
the Python guard, confirming that `-I -S` alone cannot sanitize the initial
native loader. Start with a trusted clean loader environment, for example by
clearing `LD_PRELOAD`, `LD_LIBRARY_PATH`, and `LD_AUDIT` **before** Python
starts. Coordinate a sole Lean slot and stable Git HEAD externally; the
launcher does not pin HEAD. The later merge `ec42d7f83b` added
`ModelThirteenCarrierChecks.lean`; it was not in this frozen source plan.

The monitor applies to compilation children. Each separate `lean --deps`
query uses a 120-second `subprocess.run` timeout, without sampled RSS/disk
limits or explicit descendant-group cleanup; its leader timeout is not a
descendant guarantee. The launcher checks that the final inventory contains
eight allowed axiom-report lines, but does not compare their names. Its
pinned checks source names the intended eight declarations; the post-build
artifact audit **must verify every emitted declaration name and axiom set**,
all actual exits and warnings, and the exact endpoint statements. The fake
test deliberately emits synthetic names, demonstrating the count check's
scope. The inherited Foundation outer-wrapper exit remains unobserved;
package-transitive/dynamic ancestry and changes between checks remain outside
this review. No endpoint theorem or internal iPRA equivalence is established
by preflight or mock execution.
