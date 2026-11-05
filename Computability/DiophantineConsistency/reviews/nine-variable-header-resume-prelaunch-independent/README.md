# Initial independent prelaunch audit: changes required

**The reviewed initial runner is not ready for a PASS gate.** This packet
freezes the exact initial code, tests and control receipts under [snapshot](snapshot/).
It records review findings against those bytes and does not authorize or start
a static-header traversal. A later revision needs a separate review packet;
the negative findings here are historical evidence, not a verdict on revised
code. No review-gate or approval receipt was created by this audit.

## Material findings

1. **The gate is enforced only by the launcher.** In the initial
   `worker.py`, `main()` accepts a fresh `runs/<name>/candidate.json` path
   and can instantiate `BoundedReader` without reading `review-gate.json`.
   The module also calls `main()` when run directly. Thus direct worker
   invocation bypasses the prelaunch gate, bounded-session supervisor and
   low-priority launch path. If the gate is intended to constrain every
   reader invocation, guard the worker as well and require a verifiable
   supervised launch context. A mere environment flag would be a workflow
   convention, not an unforgeable security boundary. Add a no-gate direct
   invocation regression that cannot reach `BoundedReader`.

2. **A signaling error can interrupt session cleanup.** `drain` catches
   `ProcessLookupError` from individual `os.kill` calls, but another
   `OSError`, such as `PermissionError`, exits the loop immediately. The
   second drain in `supervise` can fail the same way, before the prior
   subreaper state is restored. A mocked regression demonstrates that the
   first error escapes before the second synthetic member is signaled; it
   makes no real signals or process claims. Handle errors per member, continue
   attempting all members and reaping, report an unsuccessful cleanup, and
   restore the subreaper setting in an unconditional `finally`. Also test
   inspection and signal failures, including failure during cleanup itself.

3. **The linked history is not replayed as a sequence.** `checked_parent`
   checks each ancestor's receipt fields, links and hashes, but calls no
   `core.restore` for the ancestors and does not compare each child to its
   linked parent's processed prefix, nonbaseline module records, artifact
   entries or namespace observations. The selected latest state is replayed
   separately. The in-memory control here constructs two individually valid
   queue states in which the child's earlier nonbaseline record differs from
   the parent's; each passes `restore`. This is not evidence that a trusted
   worker actually produced such a chain. It shows that the chain validator
   itself does not establish the README's claim that **every** checkpoint's
   frontier, seen set and baseline records were replayed, or that a child's
   history extends its parent. Validate each linked state and each transition,
   including the exact new-processing suffix and unchanged prior records,
   and include a mutation regression. Hash links and locally writable JSON
   receipts provide integrity checks, not signatures or independent proof of
   who produced a receipt.

4. **A pinned Python helper is executed before its pin is checked.** The
   initial `worker.py` imports `compiled-header-inventory/inventory.py` at
   module load, before `main()` calls `check_inputs()`. The known pinned
   helper was inspected and the check below verified its current hash, but a
   changed helper could execute top-level Python before its mismatch is
   detected. Verify the helper bytes before executing them, ideally execute
   exactly the bytes that were checked, and add a controlled changed-helper
   regression. This is a fail-closed input-order finding, not evidence of a
   malicious or changed helper in the observed workspace. The launcher has
   the analogous ordering: it imports `supervision.py` and `traversal_core.py`
   before `main()` checks the gate's hashes. Those imports execute top-level
   helper code, so gate-based drift rejection happens after that execution.

There is also a **PID reuse race** worth addressing in the process design:
`group_members` observes a numeric PID and `drain` later signals that PID.
If the member exits and the number is reused between those operations, the
signal could reach a different process. PID file descriptors or an equivalent
identity-safe signaling design are preferable; merely checking `/proc` just
before `kill` narrows but does not remove the race. This race was not induced
by the audit. Session escape and supervisor SIGKILL are already documented
limitations and are not claimed to be solved by the existing tests.

## What did pass and what it covers

The pinned baseline and survey replay to 64 expanded modules, the original
199-name frontier and a 287-name starting frontier after all 128 distinct
source-declared seeds are accounted for as expanded or queued. The audit
independently ran the worker's read-only `check_inputs()`: all six listed
input pins and all 1,212 recorded project-source hashes matched. That check
did not instantiate a reader. Seed coverage is static-header coverage under
the recorded namespace policy; it is not evidence of a combined Lean import,
dynamic loads, or a path from a diagnostic seed to every actual seed.

The supplied `test_core.py`, `test_preflight.py`, and `test_supervision.py`
were each rerun successfully against the initial source bytes. The last used
only synthetic Python children and grandchildren to exercise monitor
exception, leader exit and timeout, and observed session drain in those
cases. It does not cover the injected cleanup failure above, all OS errors,
PID reuse, deliberate session escape, or unsampled resource peaks. The
original receipts contain process-specific PIDs and are not expected to be
byte-identical on replay. The 3.5-GiB RSS, 10-GiB memory and 4-GiB disk
limits are sampled guards; the disk check watches `cwd`, while temporary-file
locations can in general reside on another filesystem. `/tmp` and the work
directory were on the same filesystem at the time of this audit, but this is
not guaranteed by the implementation.

The local gate checks decision, nonempty reviewer text and exact hashes of
the four runtime scripts. It does not itself prove reviewer independence,
pin the three test scripts or their receipts, or authenticate OS tools and
dynamic libraries. Those are scope/assurance limits, not claims that the
reviewer field or controls were falsified.

Run the pinned historical regressions while the separately pinned baseline
inputs and 1,212 source files remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/nine-variable-header-resume-prelaunch-independent/check.py
```

Its [result](result.json) records the snapshot hash checks, seed replay and
in-memory/mocked findings. It starts no Lean process, does not traverse any
new header, and does not modify the actual runs directory or gate.
