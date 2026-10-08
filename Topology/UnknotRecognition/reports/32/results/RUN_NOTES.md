# Execution notes

All mathematics and homology data use exact F_2 arithmetic. Wall times use a
shared Linux execution environment and are not a quiet-machine benchmark.

- `unit_tests.txt`: completed 24-test run, no failures.
- `validation.json`: completed 175-case / 355-scan audit, no failures.
- `growth.json`: completed all 11 requested structural examples, including a
  48-crossing torus word. These single-run times are not paired timing samples.
- `cutoff_check.json`: exact rational coefficient identity proving m < 39 from
  the three displayed inequalities. This is not a check of the entire cited
  Morse construction.

## Timing attempts, including incomplete jobs

The first benchmark request contained torus m=4,8,12,16, mixed blocks, and a
weaving control, with five shuffled rounds per case. An outer 150-second tool
execution timeout stopped the job during the m=16 case. The first three complete
cases were saved atomically. They are retained in
`benchmark_aborted_completed.json` and used as batch A in `benchmark.json`.
No partial m=16 result is used as a complete timing case.

A second request omitted m=16 and attempted the remaining five cases. An outer
120-second execution timeout stopped it while processing m=12, after m=4 and
m=8 completed. Those results are in `benchmark_retry_completed.json` (batch B).
The smallest comparison reversed under a visibly noisy A/A control. This retry
is included in the paper instead of being suppressed.

`benchmark.py` is the second requested corpus, which a sufficiently long run
can complete. It atomically saves completed cases. It is not guaranteed to
finish within the outer execution limits above. Re-running overwrites
`benchmark.json`; the separately named archived batches are retained.

The partial console logs match their separately named archived batches.
The file `benchmark_console.txt` is the second request's console log, not a log
of the curated combination of complete batch-A results in `benchmark.json`.

No claim is made of a general speedup or of superiority over current production
fastunknot. The ablation changes indexing only; the mathematical scheduling
bound and exact operation counts are the primary performance contribution.
