# Reproduction and benchmark interpretation

This directory contains raw measurements and independently checkable scalar
Fitting certificates for the accompanying research article. The final source
is in the adjacent `fast/` directory. All scripts use Python's standard library.

## Files

- `run_benchmarks.py` constructs the corpus, runs five backends in interleaved
  order, checks agreement, records input diagrams and orders, and emits the
  final raw data and an actual Conway-diagram certificate.
- `paired_results.json` is the **final** run after lazy normalization was
  implemented. It records every timed call, per-call limits, all input PDs and
  braid words, source hashes, Python/platform details, statistics, and complete
  checkpoint histories for successful summaries.
- `summary.csv` and `summary.json` are derived views of the final data.
- `summarize_results.py` regenerates those summaries and
  `benchmark_audit.json`. The audit checks completed exact/capped agreement and
  compares the final run with the retained earlier run.
- `paired_results_before_lazy.json` and `summary_before_lazy.*` preserve the
  earlier exploratory measurements. That version copied components even when
  no normalization applied. These are historical data, not the performance of
  the delivered source. The final benchmark script runs the delivered source.
- `conway_fitting_witnesses.json` contains two concrete accepted scalar Fitting
  changes of basis from the Conway scan, including every original and
  transformed morphism coefficient.
- `verify_fitting_witness.py` independently checks these witnesses with dense
  binary matrix operations. Its optional replay reconstructs the complete
  scan from the included PD and checks the recorded rank and witnesses.
- `tests.log` records the final integrated test run: **94 tests passed**.

## Commands

From the extracted package root:

```sh
python benchmarks/run_benchmarks.py
python benchmarks/summarize_results.py
python benchmarks/verify_fitting_witness.py --replay
python -m unittest discover -s fast/tests -v
```

The benchmark defaults are three repetitions, a three-second budget per call,
and a ceiling of 50,000 physically stored scanner objects. They can be changed
with `--repeats`, `--seconds`, and `--max-objects`. Limits produce a recorded
resource-limit outcome. A resource limit is never interpreted as a knot verdict.

The comparison uses these backends:

| Name | Computation |
| --- | --- |
| `standard` | Established explicit `FastScan` exact rank |
| `component` | Prior exact serialized component-sharing backend |
| `fitting_exact` | Certified scalar Fitting splitting, exact interval normalization, and component sharing |
| `fitting_decision` | Scalar splitting plus interval length cap two and multiplicity cap three |
| `fitting_decision_dp` | The same decision backend after exact bounded-window order optimization |

Every backend starts from the same greedy order. The time spent constructing
that common initial order is recorded separately; `median_with_initial_order`
adds it back. For the DP backend, optimization is performed inside each timed
call and inside its time budget. Both total time and scan-only time are
reported. The DP objective is `(peak boundary, sum(2^(boundary/2)))`, with window
length ten and two passes. It is a proxy for work and does not guarantee faster
scanning.

All simplification, Seifert, Alexander, and Jones filters and visible connected
sum factorization are bypassed. These are measurements of the raw backends.
In particular, the established factorization path already handles the Conway
sum family effectively; that prior improvement is not attributed to this work.

## Corpus and selection

There are ten named cases: the eight-crossing hard unknot; Conway and
Kinoshita--Terasaka; the provided two-, three-, and eight-fold Conway sums; the
36-crossing stress braid; and the torus diagrams T(3,11), T(4,9), and T(5,8).
Eight additional cases are the first eight valid one-component braid closures
produced by the explicitly recorded random generator with seed 54287.

A nineteenth case, `random_24`, is separately labeled
`selected_split_example`. It was selected during the preliminary probe because
it has a nontrivial scalar Fitting split. It must not be included in claims
about the frequency of such splits in an unselected random sample. The corpus
is a reproducible diagnostic set, not a representative distribution over knots.

The final run contains 285 timed calls. All 279 completed calls give mutually
consistent exact ranks or capped decisions. The six resource-limited calls are
all standard explicit scans of Conway sums: three calls would allocate 64,251
objects, and three would allocate 60,984, exceeding the 50,000-object ceiling.
No timed call in this run was classified by a timeout.

## What the measurements establish

The new scalar changes of basis produce actual direct-sum decompositions on
Conway, Kinoshita--Terasaka, the Conway sums, and the separately selected random
example. For the eight-fold Conway sum, the new exact backend reduces recorded
compositions from 1,411 to 1,022 and the largest connected component from 240
objects to 160. These deterministic changes survive the lazy bookkeeping
rewrite exactly.

The lazy passes avoid constructing component copies until a Fitting split is
accepted, avoid rebuilding a complex when no interval normalization applies,
and reuse verified component inventories. This removes the large avoidable
regression on the stress case: final medians are about 615 ms for the prior
component backend and 613 ms for the new exact backend. The eight-fold Conway
sum has medians about 138 ms and 132 ms, respectively. These are observations
from three repetitions; the sample ranges overlap, so the small differences
do not establish a general wall-clock speedup. Several smaller examples remain
slower under the optional new backend. The established default is therefore
retained.

The broad finite-interval quotient has **zero eligible nontrivial components
on these nineteen actual diagrams**, even after the scalar splits. Its
representation savings are demonstrated separately on synthetic valid
cobordism complexes, explicitly marked `synthetic` in the raw data. One example
has 1,024 objects in a single connected common-nilpotent component; exact
interval sharing reduces this to eight stored objects, and the decision model
reduces it to two. A different mixed-matching example hides sixteen copies of a
three-object complex in one connected 48-object graph; certified Fitting
splitting followed by sharing stores three objects.

These synthetic complexes test the algebraic mechanism. They are not asserted
to arise as scanner stages of the measured knot diagrams.

## Exactness and diagnostic boundaries

`fitting_khovanov_rank` preserves exact total rank and the raw homological
counts. Scalar Fitting changes and full interval decompositions are chain
isomorphisms. In contrast, the decision-only interval shortening preserves
only the final rank capped at three under the stated continuation theorem. It
need not preserve exact rank, gradings, or chain homotopy type.

The default length-two cap uses the even Euler parity of ordinary Khovanov
closures of a nonempty matching. For arbitrary square-zero-action suffix
complexes without that parity property, the universal cap is three. The simple
module with zero nilpotent action distinguishes a length-two interval from a
length-three interval, which is why the stronger cap cannot be used without
its hypothesis. The public diagram entry points require a validated classical
one-component input, as do the established low-level scanners.

A scalar Fitting search is bounded by component size 48, 1,024 binary variables,
16 accepted splits per stage, the first 64 endomorphism-basis vectors, and 16
fixed-seed combinations. Failure to find a split retains the complete original
component; it is not a proof of indecomposability. Cached successful basis
changes are rechecked before use.

Each stage history records `interval_checkpoint`, `unclassified_components`,
`unclassified_objects`, `frontier_points`, and `checkpoint_gap`. A checkpoint
is certified only when every input component is a singleton or was actually
eligible and normalized. Nontrivial components skipped by the interval-size limit prevent a
checkpoint. The initial state is counted as a checkpoint, and the final closed
state is a checkpoint. These diagnostics make the conditional complexity
hypotheses inspectable; they do not assert a quasi-polynomial bound for all
inputs. For example, the stress case has a recorded checkpoint gap of 36, and
the torus examples have gaps as long as their full crossing counts.

The before/after audit compares 76 results and 380 deterministic statistics
across the four component-based backends. It reports zero differences. Source
hashes remained unchanged during the final timed run. The independent witness
verifier also successfully replayed the full Conway scan.
