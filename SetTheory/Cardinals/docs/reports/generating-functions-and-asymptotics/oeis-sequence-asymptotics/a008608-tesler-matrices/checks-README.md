# Exact finite verification for report106

## Scope: what this does, and what it does not do

This is a Python-standard-library-only, fail-closed verification suite for the
finite algebraic constructions accompanying the second-logarithmic-term Tesler
report. It uses Python integers and `fractions.Fraction`, with exact equality.
It uses no tolerances, exponentials, logarithms, floating-point arithmetic,
NumPy, network requests, or probabilistic tests.

**The rational fixtures are deliberately manufactured finite arrays. They are
not approximations of the exponential profile in the analytic proof.** Passing
this suite does not prove any asymptotic estimate, entropy inequality, capacity
theorem, uniform error term, coefficient of `n log n`, or claim of novelty.
Analytic proof review and any separate floating-point sanity checks are distinct
tasks. The suite makes no numerical estimate of an asymptotic constant.

The finite construction corresponds to Sections 2, 5, 7 and 8 of the
accompanying `report106.tex`.
The external small-count reference is [OEIS A008608](https://oeis.org/A008608),
whose entry and indexing were checked on 2 October 2026. OEIS starts at `n=1`:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| a_n | 1 | 2 | 7 | 40 | 357 | 4820 | 96030 |

The extra `n=0` test uses the explicit empty-array convention `a_0=1`; it is not
attributed to an `n=0` entry in OEIS.

## Run

From this directory, using Python 3.9 or later:

```sh
python3 run_corruptions.py
```

That is the complete command. It first runs an unmodified positive control in
each interpreter mode, then runs all 31 corruptions independently in each mode.
It refreshes the two verification JSON logs, the corruption JSON log, and the
text log. Every child has a 180-second timeout. A timeout, unexpected exception,
wrong rejection reason, accepted corruption, or failed positive control makes
the runner itself exit nonzero. Temporary corrupted inputs are written only
beneath this directory and removed afterward.

To run only the exact checks, without creating logs:

```sh
python3 verify_exact.py
python3 -O verify_exact.py
```

Alternate input paths can be supplied with `--fixtures PATH --expected PATH`.
Both input files are mandatory verification obligations even when their default
paths are used. There is no fallback to fabricated defaults or partial success.

The supplied run completed with two passing positive controls and **62 nonzero
corruption rejections**. Machine-generated timestamps in the logs are the
execution host's reported UTC clock, not a claim about publication time.

## Exact checks performed

### 1. Intervals, graph edges, cuts, and throughputs

Every fixture contains all cells `1 <= a <= b <= n`, including zero entries.
Interval `[a,b]` is mapped to directed edge `(a-1,b)` on vertices `0,...,n`.
The code computes cut loads by interval containment and independently computes
netflow by accumulating directed incoming and outgoing edges. It checks:

* cut `i` has load exactly `i`;
* netflow is exactly `(1,...,1,-n)`;
* netflow also equals successive differences of cut loads, with the endpoint
  terms handled separately;
* the source row is `1`, the sink column is `n`, and internal incoming flow is
  outgoing flow minus `1`;
* row and column totals agree, and `1 <= r_j <= j+1`;
* all edge entries and all required margins are nonnegative.

For each input `q`, every cut has load at most its staircase capacity.
The completed fixture must equal `q` with exactly the singleton deficits added.
This is compared with a separately authored snapshot using the equivalent
nonsingleton-complement formula.

### 2. The finite early-cutoff analogue

Each fixture requires `q[a,b]=0` for `a<M`. It checks exactly that the initial
throughputs satisfy `r_j=j+1` for `j<M` (within the graph), both before and after
the moves. These small rational cutoffs test the algebraic mechanism only. They
do not test or replace the analytic choice `M=1024` or its profile-width bound.

### 3. Independent triangle choices and integer table margins

The fixture explicitly supplies each triangle's coefficient changes. The suite
computes its complete linear response. A unit change at vertex `j` must:

* preserve every cut and every netflow;
* increase only outgoing row `j`, by exactly one unit;
* increase only incoming column `j`, by exactly one unit;
* reduce only the distinct long edge `[j,j+1]`, with coefficient `-1`.

For `w_j=q[j,j+1]`, the exact interval `0 <= t_j <= w_j/2` is tested at both
endpoints. The simultaneous all-half-width endpoint is checked as well.
Integer points in `[r_j,r_j+w_j/2]` are found with integer numerator/denominator
floor and ceiling, not floating-point rounding. The suite checks the elementary
lower bound of `floor(w_j/2)` points, and requires each tested fixture to offer
at least one point at every chosen vertex.

The entire Cartesian product of these choices is then exhausted. For every
choice, the suite constructs the simultaneous rational flow, rechecks
nonnegativity, cut loads, netflow and margins, and confirms that all resulting
row and column margins are integers. It checks both actual table distinctness
and actual row-margin distinctness. The rectangular table has allowed cells
precisely when its vertex indices satisfy `i<j`; its margins satisfy
`alpha=(1,rho_1,...,rho_(n-1))` and
`beta=(rho_1-1,...,rho_(n-1)-1,n)`.

The four fixtures are:

| Fixture | n | M | Triangles | Distinct integer margin vectors |
|---|---:|---:|---:|---:|
| rational_four_triangles | 12 | 8 | 4 | 36 |
| rational_endpoint | 5 | 3 | 2 | 1 |
| saturated_edges | 4 | 2 | 2 | 2 |
| no_triangle_boundary | 2 | 2 | 0 | 1 |

The main fixture has overlapping adjacent triangles and extra longer intervals,
so its baseline margins are genuinely rational. The second includes an exact
integer-choice endpoint. The third includes zero completed singleton entries
and exact cut saturation. The fourth tests the empty family of triangle moves,
whose Cartesian product has one element. Across fixtures there are 40 realized
margin vectors. The verifier compares a canonical SHA-256 of each full ordered
margin-vector list with its shipped snapshot. These hashes are regression
snapshots, not authentication or mathematical proof certificates.

### 4. Exhaustive small-size counts by two methods

For every `n=0,...,7`, one algorithm recursively enumerates every nonnegative
integer **nonsingleton** interval array satisfying each cut cap. It sets each
singleton to its uniquely determined residual capacity. At every nonempty
enumerated leaf it independently checks all cuts, all netflows, nonnegativity,
the conversion to a classical Tesler matrix, all hook sums, and the inverse
conversion. It partitions the resulting objects by their throughput vectors.

The independent counting algorithm uses the classical **hook recurrence**:
remove the first row, distribute its hook value among all off-diagonal entries
and its diagonal, and increase each remaining hook by the corresponding
off-diagonal entry. It uses weak compositions and memoization. It never reads
intervals, cut capacities, singleton residuals, or the interval enumerator.

Both counts must equal the independently transcribed expected OEIS term.
In total the enumerator visits 101258 objects including the empty object, of
which 96030 are at `n=7`. This is a finite bijection/indexing/counting check;
agreement at these sizes provides no proof of asymptotic behavior.

## Fail-closed design and adversarial controls

All guards are explicit exceptions. **There are no assertion-based guards**, so
`python -O` cannot remove a test. A successful run emits a structured `PASS` and
exits zero; every error exits nonzero and emits `FAIL` on standard error.
Strict schemas reject missing/unknown keys, incomplete coverage, duplicate
cells or JSON keys, invalid support, booleans masquerading as integers,
noncanonical rational strings, rational floats, NaN, and malformed input.

The corruption runner tests 31 cases in both modes, including bad cut loads,
bad expected netflow, negative edges, inconsistent row/column margins, an
alternative feasible flow that violates the prescribed completion, missing or
altered expected counts, malformed data, invalid cutoffs, incorrect choice
counts, and perturbed triangle rules.

One deliberate cross-coupling adds one third of the next valid triangle to the
first. It still preserves **all cuts and netflows**, and must fail specifically
at `TRIANGLE_INDEPENDENCE`. This distinguishes the single-margin response test
from mere feasibility checks. A cut vector mathematically determines netflow,
so the separate bad-netflow corruption alters the expected netflow obligation;
a feasible fixed-cut flow cannot have a different true netflow.

These are regression and defensive-input tests. They are not an adversarial
security certification of Python, cryptographic signatures of the files, or
protection against simultaneous malicious edits of the verifier and its tests.

## Files

* `verify_exact.py`: read-only exact verifier
* `rational_fixtures.json`: four explicit rational input arrays and triangle rules
* `expected_checks.json`: exact independent snapshots, integer choices, margin
  digests and small sequence terms
* `build_fixtures.py`: transparent deterministic authoring aid for the two input
  snapshots; **not called by any verification/test command**
* `run_corruptions.py`: normal/optimized positive controls and corruption runner
* `verification_normal.json`, `verification_optimized.json`: successful baseline
  outputs, including all finite counts and margin-vector counts
* `corruption_results.json`: each corruption, exit code, expected error code,
  actual diagnostic and execution-host timestamp
* `corruption_run.log`: concise human-readable run log

Do not regenerate expected snapshots just to make a failed test pass. The
authoring aid derives snapshots using direct nonsingleton complements and
cut-crossing row formulas; the verifier uses singleton-deficit completion and
directed edge accumulation. Changing either requires fresh mathematical review.
