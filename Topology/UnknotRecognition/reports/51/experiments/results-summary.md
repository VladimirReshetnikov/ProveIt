# Independent singleton-DAG experimental record

The guarded implementation gives a large checked-group-stage gain on the
stabilized-circle family. The preserved ordinary corpus does **not** show a
whole-recognizer acceleration. The optional terminal guard was selected after
an eager partial-batch prototype caused a concrete lost positive within the
established work budget. The complete eager result is retained separately.

## Reproducible boundary and protocol

Baseline commit: `483b7397a1086206bc463222094315390c42550d`.
Python: `3.12.14`; platform: `Linux-6.18.44-x86_64-with-glibc2.39`.
Full packages are copied into distinct frozen directories and imported as
`fastunknot` in separate persistent subprocesses. Every package `.py` file is
hashed before and after, as is the harness. Baseline/current source hashes
match across the guarded audit and both timing runs. This avoids mixing
absolute imports from different versions. `PYTHONHASHSEED=0`.

Each timed call encloses exactly `fn(Diagram.from_pd(pd), **options)` inside
the corresponding worker. Fresh source validation, search, and mandatory
independent compressed replay are included; imports, interprocess transport,
and result serialization are outside this timer. Each case has six randomly
shuffled arms: baseline default and forest, current guarded singleton, and an
A/A duplicate of each. One warmup per arm is excluded; five rounds are
retained. Ratios are medians of per-round paired ratios, so they need not
equal ratios of the displayed medians. All source PDs, settings, sample
orders, statuses, counters, certificates, and hashes are stored in the JSON.
This is one machine and five measured rounds; no general performance claim
or statistical confidence interval is inferred from those timings.

## Independent source audit

The guarded audit contains 81 actual validated source diagrams,
243 exact legacy default/projection/forest
certificate-and-nondecision comparisons, and 54
singleton-enabled positives that each pass both independent literal and
compressed replay from the original diagram. Legacy statistics are also
identical: `True`. There are zero newly closed and zero lost
positives against either default or forest in this finite audit.

Guarded certificate versions: `{5: 22, 8: 29, 1: 3}`. The 29 version-8 positive
proofs contain 29 singleton batches and
307 certified pivots. The corpus consists of 19
preserved ordinary cases, fixed-seed random valid one-component braid
closures, and seven stabilized circles. This is a soundness/regression
audit, not evidence of completeness on arbitrary unknots.

The eager prototype audit had 53 positives,
zero newly closed cases, and one lost positive: the 141-crossing Gordian
input. Its initial partial batch eliminated 60 generators, but subsequent
search exhausted work 20,000,000. The guarded mode skips partial batches
and eventually accepts a terminal batch of three pivots on this input,
restoring a source-checked certificate. Its search work is 1,292,253 versus
baseline default 1,215,145; the guard is a search-policy correction, not a
claim of zero overhead.

## Checked group stage on an actual unknot source family

Each input is the closure of `sigma_1 ... sigma_n` on n+1 strands; it has n
crossings and is a succession of stabilizations of the circle. The
repository's initial group presentation has n generators. Earlier diagram
simplification is deliberately bypassed here. These are easy unknots, and
the following numbers are **not whole-recognition speedups**.

All 150 measured calls and 30
warmups completed. The common options are `seconds=None`,
`max_work=50_000_000`, `max_nodes=1_000_000`, `compressed_search=True`.

| Crossings | Default ms | Forest ms | Singleton ms | Paired default/singleton | Paired forest/singleton | Forest batches | Singleton pivots |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 16 | 6.217 | 3.552 | 1.352 | 4.203 | 2.401 | 7 | 15 |
| 32 | 15.764 | 7.348 | 2.859 | 5.755 | 2.570 | 15 | 31 |
| 64 | 60.712 | 18.818 | 5.372 | 12.112 | 3.813 | 31 | 63 |
| 128 | 219.120 | 60.203 | 10.477 | 21.205 | 5.656 | 63 | 127 |
| 256 | 876.726 | 244.618 | 23.583 | 36.468 | 9.444 | 127 | 255 |

The singleton mode takes one raw terminal batch in every row. For n=256,
search work is 1,905,056 (default), 595,473 (forest), and 92,547 (singleton).
Corresponding grammar node counts are 98,939, 2,041, and 2,547; the singleton
batch does not minimize every size metric. Canonical JSON certificate sizes
are 17,600, 49,244, and 12,770 bytes. The measured mechanism is fewer
repeated passes and a shorter trace, with shared raw composition. Across
the stage cases, paired A/A medians span 0.901–1.104.
Node construction is linear on this family; charged producer work includes
sorting, and these finite timings do not establish an asymptotic bound.

## Complete ordinary-corpus recognition

All 570 measured calls and 114
warmups completed. Fifteen unknots reach the checked group stage. Four
knots finish earlier: trefoil and figure-eight by the homogeneous Seifert
genus filter, Conway and Kinoshita–Terasaka by the modular Jones filter.
Timing differences for those four cannot be attributed to this feature.

Only Gordian uses a singleton batch under the terminal guard; the other
fourteen unknot cases preserve the default version-5 proof but pay
eligibility-planning overhead. No new ordinary case is solved.

| Input | Crossings | Default ms | Forest ms | Singleton ms | Paired default/singleton | Paired forest/singleton | Singleton batches |
| --- | --- | --- | --- | --- | --- | --- | --- |
| survivor-00 | 16 | 12.022 | 13.303 | 11.997 | 0.970 | 1.064 | 0 |
| survivor-01 | 15 | 11.000 | 10.582 | 10.389 | 1.059 | 1.017 | 0 |
| survivor-02 | 15 | 12.929 | 11.724 | 11.987 | 0.943 | 0.989 | 0 |
| survivor-03 | 13 | 8.406 | 9.513 | 8.876 | 0.848 | 1.024 | 0 |
| mirror-03 | 13 | 23.508 | 24.634 | 18.523 | 1.245 | 1.313 | 0 |
| survivor-04 | 13 | 7.378 | 8.019 | 7.540 | 0.911 | 0.954 | 0 |
| survivor-05 | 13 | 18.598 | 19.196 | 15.077 | 1.234 | 1.013 | 0 |
| survivor-06 | 12 | 7.467 | 7.769 | 8.048 | 0.925 | 0.961 | 0 |
| survivor-07 | 12 | 14.327 | 15.372 | 20.256 | 0.747 | 0.902 | 0 |
| survivor-08 | 11 | 4.836 | 7.888 | 5.384 | 0.956 | 1.409 | 0 |
| mirror-08 | 11 | 13.089 | 14.260 | 15.950 | 0.807 | 0.866 | 0 |
| survivor-09 | 11 | 5.324 | 5.786 | 7.994 | 0.669 | 0.742 | 0 |
| survivor-10 | 11 | 4.759 | 4.740 | 5.076 | 0.889 | 0.935 | 0 |
| survivor-11 | 11 | 4.995 | 5.103 | 5.676 | 0.879 | 0.895 | 0 |
| gordian | 141 | 952.834 | 993.982 | 1005.899 | 0.950 | 0.980 | 1 |
| trefoil | 3 | 0.039 | 0.059 | 0.049 | 0.779 | 1.168 | 0 |
| figure_eight | 4 | 0.042 | 0.041 | 0.047 | 0.880 | 0.859 | 0 |
| conway | 11 | 0.637 | 0.622 | 0.655 | 0.952 | 0.912 | 0 |
| kinoshita_terasaka | 11 | 0.589 | 0.632 | 0.672 | 0.919 | 0.869 | 0 |

The median of paired ratios of the per-round total time for the entire
19-case workload is 0.954856 for default/singleton and
0.985518 for forest/singleton. Ratios below one favor
the baseline. Corresponding workload A/A medians are
0.977439, 0.986358, and
1.001674. Per-case A/A medians span
0.896–1.249, including submillisecond cases.
This record supports keeping the feature opt-in and investigating cheaper
eligibility discovery; it does not support a broad speedup claim.

## Files and rerun

- `singleton_dag_research.py`: frozen audit and randomized paired harness.
- `summarize_singleton_dag.py`: derives this summary and the CSV tables.
- `audit-guarded.json`, `stages-guarded.json`, `benchmark-guarded.json`:
  complete final guarded records with source hashes and certificates.
- `audit-eager.json`: retained development regression evidence.
- `frozen-guarded/`: package snapshots used by all final records.
- `frozen-eager/`: package snapshots used by the eager audit.

Run the harness's `audit`, `stages`, and `benchmark` modes sequentially,
providing `--baseline-fast`, `--current-fast`, `--corpus`, `--snapshots`,
and `--output`; use fresh snapshot/output directories for changed code.
Default stage sizes are 16,32,64,128,256; default measured rounds are five.
Then run `python summarize_singleton_dag.py` beside the named output files.
No timing run should overlap other CPU-intensive work.
