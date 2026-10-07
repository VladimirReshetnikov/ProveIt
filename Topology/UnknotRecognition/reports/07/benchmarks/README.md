# Benchmarks and reproducibility

This directory records two separate experiments: the effect of component
compression on the **raw Khovanov scanner**, and the effect of signed Seifert
certificates on the **complete recognition function**. Their timing boundaries
and ratio conventions differ. Read those definitions before comparing numbers.

The archived JSON files contain the original measurements. Reproduction commands
below write files ending in `_rerun.json` so that the original observations remain
available for comparison. The scripts select the sibling `fast/` implementation
using their own location, so a separately installed `fastunknot` does not take
precedence.

## Files

| File | Purpose |
|---|---|
| `component_benchmark.json` | Seven interleaved rounds comparing the raw baseline scanner with exact and saturated component sharing, including an A/A control. |
| `benchmark_components.py` | Reproduces the component-scanner experiment. |
| `structural_benchmark_raw.json` | Original structural-front-end experiment: 20 cases, nine paired rounds, ordinary GC settings and no CPU pinning. |
| `structural_benchmark_pinned_raw.json` | Structural robustness repeat: nine rounds, CPU affinity `[8]`, cyclic GC disabled, and longer batches. |
| `benchmark_seifert.py` | Reproduces either structural experiment. |
| `plot_results.py` | Regenerates `paper/figures/performance_summary.pdf` and `.png` directly from the original structural report and component report, without running benchmarks. Requires Matplotlib. |
| `euler_examples.json` | Exact early-decision stages, suffix-state counts, and safe fallback evidence. |
| `record_euler_examples.py` | Regenerates Euler observations without timing claims. |
| `defect_one_family.py` | Checks the explicit PD and facial formulas for the Reidemeister-I/II-reduced unknot family from the article; this is a correctness experiment, not a timing comparison. |

The recorded environment was CPython 3.12.14 on Linux
`6.18.44-x86_64-with-glibc2.39`. The structural reports record nine logical CPUs.
Machine-specific paths in the JSON describe where the measurements were made;
the scripts do not require those paths to exist on another machine.

## 1. Raw scanner experiment

### What is measured

`benchmark_components.py` calls these functions directly on the same validated
PD code:

| Arm | Function | Output being computed |
|---|---|---|
| `A1`, `A2` | `khovanov_rank` | Baseline exact unreduced and reduced ranks. |
| `full` | `compressed_khovanov_rank` | Exact ranks using shared components and integer multiplicities. |
| `saturated` | `compressed_khovanov_decide` | Unreduced rank capped at three, sufficient for the knot decision. |

Every function constructs its own scanner state. Input loading and diagram
validation occur before timing. Crossing-order selection and scanner work occur
inside the timed call. Reidemeister simplification, Alexander/Jones filters,
the Seifert certificate, and geometric connected-sum factorization are outside
this experiment.

Consequently, a raw-scanner improvement cannot be read as the same improvement
to the default recognizer. The baseline recognizer already factors visible
connected sums and often decides these knots through an inexpensive invariant.
The repeated-Conway examples isolate the scanner's handling of multiplicity;
they do not establish that the former recognition pipeline needed to expand
their entire complexes.

The first five cases receive seven rounds each. Case order is fixed; the order
of the four arms is shuffled in each round using seed `20261007`. `A1` and `A2`
are independent calls to the same baseline. The script checks agreement of the
exact rank and of the saturated threshold after every round.

### Ratio convention

For a sample, the reported runtime ratio of an arm is

\[
 R_{\mathrm{arm}}
 =\frac{T_{\mathrm{arm}}}{\sqrt{T_{A1}T_{A2}}}.
\]

**A ratio below one means the new scanner is faster.** `median_ratios` is the
median of those paired ratios. It is not the ratio of the separate median
timings. `ratio_ranges` contains the observed minimum and maximum; these ranges
are not confidence intervals. The A/A ratio is `T_A2 / T_A1`.

| Case | Crossings | Exact-sharing runtime ratio | Saturated runtime ratio |
|---|---:|---:|---:|
| Conway | 11 | 1.220 | 1.188 |
| Torus knot, three strands and five repetitions | 10 | 1.220 | 1.145 |
| Five-strand stress braid | 36 | 1.312 | 1.284 |
| Two Conway summands | 22 | 0.2438 | 0.2530 |
| Three Conway summands | 33 | 0.00735 | 0.00793 |

The first three cases expose the bookkeeping cost when sharing finds little
benefit. The repeated-summand cases expose the benefit when the complex contains
many equal direct summands. Both outcomes are part of the result.

The final record, `conway_sum_8_no_expansion`, is a separate demonstration with
one call to each new backend. Exact sharing returns the unreduced rank

\[
 2\cdot 33^8=2{,}812{,}817{,}236{,}482
\]

without expanding that many generators; saturation returns `rank_capped = 3`.
It has **no measured baseline arm**, no paired speedup, and no seven-round
uncertainty estimate. The existing geometrically factored baseline also handles
this connected-sum structure efficiently through its own factorization API.

### Reading the other metrics

`metrics` records the last result produced by each arm. `work` is the diagnostic
sum `stats.entries + stats.compositions`; it counts implementation operations,
not represented homology generators, seconds, or bit operations. Compare it
with its underlying fields in `stats` when investigating behavior. This count
alone does not prove an asymptotic bound.

`rank` is an **unreduced** rank. Saturated output deliberately provides
`rank_capped` instead: two identifies the unknot, and three means the exact
unreduced rank exceeds two. The value three is a mathematical saturation
threshold, not a resource limit and not an assertion that the exact rank is
three. Exact reduced ranks and ranks by degree should be taken from the exact
API, not inferred from a saturated result.

## 2. Recognition-function experiment

### What is measured

`benchmark_seifert.py` compares:

- **A:** the baseline `recognize` function with its ordinary reductions,
  factorization, invariant filters, and standard scanner fallback.
- **B:** `seifert_certificate` first; if it is inconclusive, the same baseline
  recognizer is called on the resulting Diagram object.
- **AA1 and AA2:** two more independent calls to A.

Every invocation receives a fresh, uncached Diagram record for a PD code that
has already been validated. The timed boundary includes the whole recognition
call, including its preprocessing. Imports, file I/O, parsing, validation, and
JSON serialization are excluded from both arms. These are recognition-function
timings, not command-line startup measurements.

The original data were collected against the unmodified source snapshot, whose
`recognize` function did not have a `use_seifert` argument. Its archived
`baseline_options` is therefore `{}`. When run against the delivered `fast/`
code, the script detects the new argument and sets `use_seifert=False` for A
and for B's fallback. The standard scanner remains the baseline backend.
This reproduces the comparison without accidentally testing the front end
against itself.

The 20 deterministic inputs comprise eight weaving three-strand braid closures,
four positive three-strand closures, four positive five-strand closures, and
four existing fixtures on which the certificate is inconclusive. The largest
diagrams have 1,000 or 1,004 crossings. All timed arms agreed on every verdict.

Each of nine rounds shuffles both case order and arm order using seed
`2026100703`. A measured pilot chooses the number of calls per timing batch;
the actual number is recorded as `loops` for every case. Input generation and
arm ordering are reproducible, while pilot-selected loop counts and elapsed
times naturally depend on the machine and its load.

### Ratio convention and uncertainty

The structural reports use

\[
 S=\frac{T_A}{T_B}.
\]

**A value above one means the front end is faster.** This is the reciprocal
orientation of the component-scanner runtime ratios. The summary reports the
geometric mean of the nine paired A/B ratios. Its separate median A and median B
times are descriptive timings; their ratio need not equal that geometric mean.
The structural A/A ratio is `T_AA1 / T_AA2`.

The reported 95% interval is a percentile bootstrap of the mean paired log
speedup, using 3,000 resamples and seed `2026100704`. It describes variation in
the sampled run. A small shared-host experiment does not establish a precise
hardware-independent performance ratio. The raw wall and process-CPU samples,
execution order, loop counts, A/A ratios, and observed ranges are retained so
that this limitation can be assessed.

### Original and pinned runs

| Setting | Original run | Pinned robustness run |
|---|---|---|
| Rounds | 9 | 9 |
| Target baseline batch duration | 10 ms | 30 ms |
| Maximum calls per batch | 128 | 256 |
| Cyclic garbage collection | Python default | Disabled after collection |
| CPU affinity | Unmodified | CPU 8 |

The original report predates the additional affinity and GC metadata fields.
Its settings are the script defaults shown above. The pinned report records
those settings explicitly.

| Case | Crossings | Original A/B speedup | Pinned-repeat A/B speedup |
|---|---:|---:|---:|
| Weaving three-strand braid, 500 repetitions | 1,000 | 28.75 | 27.86 |
| Positive three-strand braid, 500 repetitions | 1,000 | 25.97 | 28.88 |
| Positive five-strand braid, 251 repetitions | 1,004 | 53.94 | 44.13 |
| Conway control | 11 | 0.861 | 1.003 |
| Kinoshita–Terasaka control | 11 | 0.918 | 0.883 |
| Hard unknot with eight crossings | 8 | 0.770 | 0.953 |
| Scrambled grid unknot | 6 | 0.478 | 0.470 |

The large homogeneous-family improvements reproduced under changed settings.
The small controls expose overhead: the easiest grid unknot increases from
approximately 22 microseconds to 49–52 microseconds because the baseline already
settles it almost immediately. Moderate differences on tiny controls are harder
to separate from variation: individual A/A ratios remain broad even in the
pinned run. The data support strong gains on these large homogeneous families
and a measurable small-case cost; they do not support precise claims about
every small input or an aggregate speedup across arbitrary workloads.

## 3. Reproduce from the delivered code

The following commands start in the package's `fast/` directory and work without
setting `PYTHONPATH` or installing a package. The scripts resolve imports from
their sibling `fast/` directory. Python 3.10 or later is required by the source
syntax; the archived measurements used Python 3.12.14.

```sh
python ../benchmarks/benchmark_components.py --examples examples --output ../benchmarks/component_benchmark_rerun.json --rounds 7
python ../benchmarks/benchmark_seifert.py --output ../benchmarks/structural_benchmark_rerun.json --rounds 9
python ../benchmarks/defect_one_family.py --max-k 100
python ../benchmarks/plot_results.py
```

The plot is a 6.5-inch-wide publication figure. Its first panel shows the
original structural run's measured weaving-family medians on logarithmic axes;
lines only connect observations. Its second panel shows the recorded
`max_objects_before_elimination` counts for the baseline and exact shared
scanners on one, two, and three Conway summands, with geometric factorization
disabled. Object counts are not process-memory measurements. The regeneration
script computes all plotted values from the JSON files and fits no exponent.

The raw scanner benchmark includes the expensive explicit scan of three Conway
summands. Its duration is much longer than a normal recognition call on the same
diagram because the latter can use filters and visible factorization.

On Linux, inspect allowed CPU indices before reproducing the pinned run:

```sh
python -c "import os; print(sorted(os.sched_getaffinity(0)))"
```

If index 8 is allowed, the archived pinned configuration is:

```sh
python ../benchmarks/benchmark_seifert.py --output ../benchmarks/structural_benchmark_pinned_rerun.json --rounds 9 --target-batch-seconds 0.03 --max-loops 256 --pin-cpu 8 --disable-gc
```

Choose an allowed index on another host. The `--pin-cpu` option requires Linux
affinity support; omitting it runs the portable comparison. The basic scripts
also work on Windows, using the same forward-slash Python paths shown above.

For correctness checks of the full code package, also run from `fast/`:

```sh
python -m unittest discover -s tests -v
```

The defect-one helper uses explicit formulas, no randomness: it compares the
variable-parameter PD code with the braid converter, enumerates all facial
walks, checks the absence of RI/RII moves, checks genus and defect, and verifies
one braid-relation reduction step. The completed run covers all 99 parameters
from 2 through 100. These finite checks validate the formula implementation;
the article's symbolic proof establishes the family for every parameter.

## 4. Scope of the evidence

The mathematical certificate conditions, integer ranks, and diagram families
are deterministic. Timing values, pilot-selected batch lengths, and host
metadata are empirical. The raw scanner and recognition experiments isolate
different costs; neither should be used as a substitute for the other.

The archived timing experiments cover the structural front end and the exact
and saturated component backends. They do not time the later optional Euler
obstruction extension. Its correctness checks belong to the code's test suite;
no Euler-backend performance gain is inferred from these reports.

The article's linear-time homogeneous-family result and conditional complexity
theorems follow from proofs. Measured speedups do not establish a universal
quasi-polynomial guarantee. The implementation retains an exponential
worst-case fallback on unrestricted diagrams.
