# Independent audit of norm38 first run and corrected retry

The initial author-recorded outer session **48446 exited 1**. Its retained
state and logs show a successful dependency scan followed by a failed
`SharingGateModel` compile: Lean reported unknown `Function.update_same` and
`Function.update_noteq` identifiers and consequent type mismatches. No later
stage ran. The recorded direct guards preceded that failed compile; the
runner's success-path post-compile check was not reached.

The author-recorded retry session **16634 exited 1**, after successful scans
and compiles of the repaired `SharingGateModel` and the unchanged
`ForwardWitness38`. The gate module checks generic signed-pair algebra,
forward gate replay and the reverse replay **conditional on a residual
trace**. The forward module defines the 38-coordinate witness constructor;
it does not prove its residuals vanish or connect it to the seed. The generic
gate compile has two unused-simp-argument warnings. No axiom report was
requested for either module.

The next stage, `SharingSeed38`, had a successful dependency scan, then its
compile stopped at the 120-second timeout with exit `-15` and an empty log.
This evidence does not identify which declaration stalled. No seed
degree/normalization result, subsequent stage, model bridge or iPRA endpoint
follows from that attempt.

`check.py` verifies both retained states and logs against the live attempt
directories, both passing object hashes, the 400 recorded direct-provider
guard slots, and all 1,055 overlay links per attempt as current point
observations. It also verifies the exact source differences: the gate and
trace files only replace `Function.update_same` with `Function.update_self`
and `Function.update_noteq` with `Function.update_apply` (two occurrences of
each in the gate file, one each in the trace file); the other four sources are
byte-identical. The trace file was not compiled in the retry. The runner delta
is limited to output path and manifest pin.

The two outer exits above appear in post-hoc `outer-terminal-author-record.json`
files, which explicitly identify themselves as the author's records of the
actual tool results and not raw transcripts. Their SHA-256 hashes are
`29c4c6fd69b58838c3573bcaca5a13232c5a582bbd064fd2a870bca7e37782b5`
and `d1f76bff9ac4273c14fc1b9fc38f83f9f1eaee57bec8ef3d92a28b4617054db7`.
This reviewer did not observe those exits directly. All other results are checks of retained states/logs and current
files, not a Lean replay. Failed-stage direct guards are initial snapshots,
though this review also confirms they still match now; there is no final
all-stage guard audit after either stopped run. Inherited provider ancestry,
dynamic loads and sampled resource limits remain outside this audit.
