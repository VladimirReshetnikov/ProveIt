# Independent Cauchy component and cache-schedule checks

## Final-cutoff addition: ratio fusion

The late `sat_frontier_improvements` packet already contains the quadratic
Cauchy recurrence. Thus the original recurrence below is an independent
reproduction, not the final corpus's new practical contribution. The new
improvement is isolated in `fused_cauchy.py`: cached transition unit ratios
and one-time target-prefactor absorption reduce quadratic table work from
`(5N^2+N)/2` to `N^2+N` ring multiplications, with additional O(L) preparation
and the same single unit inversion. Its matched baseline independently
reproduces the late packet's one-inversion quadratic mathematical algorithm.
No archive code is imported or executed.

```sh
python3 code/verify_fused_cauchy.py
python3 code/benchmark_fused_cauchy.py --max-a 9 --repeats 5
```

The full-preparation timings and every raw sample appear in
`results/fused_cauchy_benchmark_mask_all.json`. Both methods use the
same optimized MaskRing backend, and every timed return was checked outside
timing. The file combines disjoint small/large fixture runs and records their
unchanged raw-file hashes. Older percent-reduction runs remain separate.
This is the relevant matched authored comparison against the late quadratic
algorithm; the earlier cubic-reference timings
below are retained only as historical/reproduction evidence. The exact
checks include zero prefactors and recovering a unit output after an
intermediate normalized residue vanishes modulo two.

## Earlier independent reproduction and schedule checks

These programs were authored for this iteration from mathematical formulas.
They do not import or execute any code from the reviewed incoming archives.
Only the Python standard library is needed for the delivered programs here.

From the archive root:

```sh
python3 code/cauchy_checks.py
python3 code/verify_cache_schedule.py
python3 code/benchmark_cauchy.py --max-a 8 --repeats 5
```

The first script compares two modular algorithms with an independent exact
rational oracle, reconstructs the original kernel, and verifies exact
operation counts. It includes the non-prime residue field F4 and zero
prefactors. The second certifies the new cache schedule with exact rational
and integer inequalities. Their checks remain enabled under `python3 -O`.

The benchmark compares identical full dense target/source output. Every
timed call includes denominator-cache construction, batch inversion,
prefactor preparation, zero initialization and feature generation. Both
algorithms skip known triangular zeros and share modular arithmetic and
denominator inverses. A symmetric untimed warmup precedes five alternating
order samples. Wall time and process CPU time are recorded separately.

Benchmark parameters use zeta=U in the degree-two unramified extension
and precision p=4N+16. This avoids restricting the comparison to tiny
fixed precision, where many target modes could be omitted. It does not
represent every upstream precision regime or on-demand workload. Small
cases can lose from overhead and measurement noise; all raw samples are
retained. No SAT runtime, new SAT exponent order, or universal speedup is
claimed from this component experiment.

Outputs are written to `results/`. The original first-pass benchmark is
preserved as `cauchy_benchmark_first_pass.json`; the five-sample confirmatory
record is `cauchy_benchmark_confirm.json`. Rerunning the benchmark writes
`cauchy_benchmark.json` and CSV without modifying those two archived records.
