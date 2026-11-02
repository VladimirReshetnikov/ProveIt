# Independent sampled-monitor review

The independently reviewed corrected monitor code passes the explicit
fake-process controls below, with the limits stated here. The reviewed driver
`ea404d70…` and final driver `c5cc9ec8…` are retained as byte-pinned
snapshots. An exact byte comparison shows the latter changes **only** the
composition-source SHA pin, and the new pin matches the retained source.
Thus the monitor controls apply to the same code in the final driver; they do
not establish that a later Lean replay succeeds.

The original first attempt, wrapper session 91549, exited 1 when the RSS
reader found no `VmRSS`; its child exit was not observed, even though a
compiler log existed. It is a failed monitor attempt, not a proof receipt.
The second attempt, session 56381, had wrapper exit 1 and an observed final
compiler exit 1 with proof errors and `sorryAx`; it is a separate failed
composition attempt. Their terminal observations are retained here and the
author retains the corresponding driver and compiler logs.

An actual temporary fake-child test of the second attempt's driver
`bcf08ab9…` exposed a separate interruption gap: external SIGTERM ended the
wrapper with exit −15 while its new-session child stayed alive. The test
then explicitly killed and reaped that fake child. A second independent test
of that driver's exception path passed after a same-group descendant confirmed
that it had installed a SIGTERM-ignoring handler: the verified-group leader and
descendant were both absent/reaped after cleanup.

The corrected driver installs temporary SIGTERM and SIGINT handlers during
each monitored child run. Independent actual-subprocess controls for both
signals reported the corresponding interruption reason and reaped the fake
leader and a same-group descendant that had confirmed SIGTERM-ignore before
the signal. Injected missing RSS, excessive leader RSS, low free disk and
timeout each returned its fail-closed reason and reaped the fake leader. The
author's corrected control suite was also rerun: tool session 14750 actually
exited 0, with its stdout retained. The independent aggregate verifier
actually exited 0 in session 49114.

These tests exercise specific process groups. Reaping the direct leader is
not evidence that every possible descendant has exited: the descendant tests
cover only the recorded same-group cases, and a process that escapes the
group is outside the mechanism. PID/group verification is not atomic; forced
SIGKILL of the wrapper cannot execute its cleanup. Signal handlers apply while
the monitored child runs, not as a blanket guarantee for the entire wrapper.
RSS is sampled for the direct compiler PID, not summed across a process tree;
sampling and free-disk checks are not continuous enforcement, reservations,
or hard quotas.

After the third wrapper attempt had ended, `check_after_run_manifest.py`
observed that both the repository source-freeze manifest and the frozen
snapshot manifest had the independently audited `9a7059e4…` hash. At that
instant all 70 frozen/workspace source pairs and all 12 suffix source pins
matched. The live driver did **not** hash-pin the manifest when it read it:
this later observation does not establish its exact execution-time bytes or
rule out transient changes between checks. The separate output is recorded
in `post-run-manifest.json`.

`CHECK.json` preserves the test outcomes, exact driver and source hashes and
the failed-attempt classifications. `terminal-observation.json` binds actual
tool exits to the receipt. Re-run the independent controls with temporary fake
processes, without invoking Lean:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-denominator-monitor-independent-audit/verify.py
```
