# Signed-run structural certificate interface benchmark

This is one final run of seven seeded, shuffled paired rounds for each of
`m = 101, 1001, 10001`. Each case uses the **same already parsed input** on
five strands:

```json
{"strands": 5, "runs": [[1, 101], [2, -101], [3, 101], [4, -101]]}
```

The larger cases replace every magnitude `101` by the stated `m`. The
immutable tuple of four `Run` objects is constructed once outside timing.
No JSON parsing is included in any arm.

**Arm A** expands this tuple into `4*m` signed letters, constructs and
validates a fresh `Diagram.from_braid`, and runs the maintained
`seifert_certificate` on that diagram. **Arm A/A** independently repeats the
same operation. **Arm B** calls `signed_run_certificate` directly on the
shared run tuple, with 100 fresh invocations per timing sample. Its batch
duration, including loop and output-list append overhead, is divided by
100. Outputs are retained for verification outside the timer.

Every field in the expanded certificate is compared with the direct
certificate, including status, criterion, all graph counts, genus, writhe,
and Rasmussen interval. All 2,100 direct outputs also pass
`verify_signed_run_certificate` outside timing. All answers are `KNOTTED`
by `homogeneous-seifert-genus`, with writhe zero, Rasmussen interval `[0,0]`,
and canonical genus `2*m-2`.

| Run magnitude | Expanded crossings | Median expanded time | Median direct time per call | Median paired speedup | Median A/A |
|---:|---:|---:|---:|---:|---:|
| 101 | 404 | 4.787 ms | 5.971 microseconds | 741.2 | 1.053 |
| 1,001 | 4,004 | 48.083 ms | 5.039 microseconds | 7,894.7 | 1.039 |
| 10,001 | 40,004 | 484.068 ms | 4.482 microseconds | 106,985.4 | 0.958 |

A median paired speedup need not equal the ratio of two median times.
Batch durations, individual arm timings, arm orders, source hashes, compared
field names, certificates, and verifier counts are retained in
`signed_run_structural_benchmark.json`. The numeric table is also supplied
as `signed_run_structural_summary.csv`.

The environment was a shared virtual machine with uncontrolled load. The
parent reported an integration regression suite running concurrently in
the shared environment. No attempt was made to isolate or measure that
load, and the benchmark was not rerun to improve the timing values. These
are observational measurements of the declared interfaces.

The improvement avoids work that scales with the expanded crossing count.
It evaluates the **same established structural certificate** on succinct
input. This benchmark does not time the complete recognition portfolio and
does not show an improvement on residual hard-unknot instances.

From the package root, reproduce the declared protocol with:

```bash
python benchmarks/benchmark_signed_run_structural.py --rounds 7 --direct-batch 100
```

The driver resolves package imports and default output paths relative to
itself and can run from another current directory. Use both `--output` and
`--summary` to preserve the delivered data when recording a separate run.

## Final verifier revision

After this measurement, the independent verifier was extended to accept the
hexadecimal numeric fields emitted for huge certificates. The timed
`signed_run_certificate` producer is unchanged. The exact revision and both
module hashes are retained in `provenance/structural_verifier_serialization.patch`
and `provenance/structural_benchmark_revision.json`. The final regression suite
includes full huge-certificate JSON round-trip replay.
