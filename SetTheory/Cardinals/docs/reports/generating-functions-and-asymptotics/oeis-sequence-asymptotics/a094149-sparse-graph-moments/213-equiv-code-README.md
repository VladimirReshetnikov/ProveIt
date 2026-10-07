# Report213: exact finite reproduction

This modest, self-contained package freshly computes the A094149 tree-walk
moments `a_k = M_(2k)` through **k = 32**, and independently exhausts normalized
closed tree walks through **k = 8**. It uses Python 3.9 or later and only its
standard library. Nothing is downloaded, installed, compiled, or read from an
external data location. Run the commands from any working directory.

## Complete finite replay

Choose new output directories **outside this source package**, with existing
parent directories:

```sh
python3 -B reproduce.py --out ../finite-replay-normal
python3 -B -O reproduce.py --out ../finite-replay-optimized
```

Each command independently performs the full finite workflow in both normal
and optimized Python, compares every freshly produced result byte with the
published `results/` reference, and exercises all deliberate-failure tests.
The two output directory trees, and their stdout, should match byte for byte.
No absolute paths, elapsed times, platform identifiers, or current timestamps
are put into successful outputs. The `-B` flag avoids bytecode side products.
Existing output directories and destinations inside the source package are
refused. All validation takes place before the requested output is created.
A temporary working directory is cleaned up on success or failure.

The article's separate build driver may call this script. This subpackage does
not build a PDF or an archive and has no TeX, compiler, or nonstandard Python
dependency.

For a single fresh mathematical run without the negative-test harness:

```sh
python3 -B finite_checks.py --out ../finite-single --compare results
```

Omitting `--compare` creates fresh results without comparing a published
baseline; this is useful for authoring, but is not the complete release replay.

## What is computed and checked

1. **Exact first-edge recurrence through 32.** `common.recurrence` generates all
   root-departure rows `F[k,m]` from `F[0,0] = 1`. The cut branch coefficient is
   `E[t,q] = sum_j F[t,j] binom(j+q-1,q-1)`, with `E[0,q] = 1`. Equivalently,
   `F[k,m] = sum_(q=1)^m binom(m-1,q-1) sum_(t=0)^(k-q)
   E[t,q] F[k-q-t,m-q]`. The loop order in the source implements this identity
   and never uses a stored recurrence array as input
2. **Independent walk enumeration through 8.** Starting at vertex 0, a move
   follows any discovered adjacent edge or discovers the next fresh vertex.
   A completed walk must return to 0 after `2k` steps. This generates
   first-appearance-normalized tree walks directly, without the recurrence.
   Every root row is compared with the fresh recurrence. A Dyck direction path
   and discovery-order child choices are checked for uniqueness, and the
   maximum-departure encoding bound is checked on all enumerated walks
3. **Exact branch and partition formulas.** Direct weak-composition enumeration
   checks the allowed root-return cuts in `E`. Set partitions are enumerated by
   restricted growth and their branch-polynomial products reproduce every
   root row through 8. The exact `E` formula and both cut bounds are checked in
   the full triangle `t+q <= 32`
4. **Finite positive-coefficient majorant.** The majorant `G[m,s]` is generated
   through `m+s <= 32` by an integer recurrence that chooses the partition block
   containing the smallest label. All 528 inequalities `F[m+s,m] <= G[m,s]`
   are checked. Through 8, enumerating set partitions and, independently,
   differentiating a bivariate formal exponential using exact rational
   coefficients both give the same `G[m,s]`. This is a finite truncated formal
   computation, not an evaluation of a divergent infinite moment series
5. **The polynomial identity behind A_t.** For `1 <= t <= 32`, `1 <= q <= 64`,
   check `binom(q+t-1,t) = sum_j binom(t-1,j-1) binom(q,j)`. These are the
   coefficient identities for the report's expression for `A_t(x)`
6. **Weighted rotation and exact two-hub correction.** Through 8, vertex
   occurrences counted directly agree with `(2k/m)F[k,m]` for every `m`.
   For every threshold `L > k/2`, direct enumeration verifies that at most two
   vertices qualify and agrees with the exact central-edge two-hub formula.
   Subtracting its count from the weighted sum gives the union, including
   periodic walks with the appropriate exact rational rotation weights
7. **Fresh Bell convolution.** Direct partition products of the lower branch
   weights `binom(q+t-1,t)` equal `binom(k-1,s)B[k-s]` through 8. Independently
   generated Bell numbers then check the complete finite sum
   `sum_(s=0)^(k-1) binom(k-1,s) B[k-s] = B[k+1] - B[k]` through 32
8. **Further consistency.** Root boundaries, the one-defect identity, strict
   moment increase, the Catalan-factorial bound, and the integer form of the
   moment-norm inequality are checked through 32

The first-edge and partition/cut infrastructure is the one stated in Report212
and reproduced in Report213. This is a fresh standard-library implementation,
not an import of its C++ output or its large recurrence arrays. Independent
algorithmic verification by actual walk enumeration ends at 8. Regenerating
higher rows with the recurrence is not a different proof of those rows.

## Files and exact display

- `common.py`: exact recurrence, Bell numbers, branch and majorant helpers
- `finite_checks.py`: independent exhaustive walk generator and mathematical checks
- `reproduce.py`: two-mode positive replay, byte comparisons, and negative harness
- `results/checks.json`: check counts, all small enumerated rows, weighted-rotation
  and two-hub cases, exact selected table values, and a digest of the complete
  freshly generated root array; the large array itself is not distributed
- `results/moments.csv`: all exact moments and Bell values for `0 <= k <= 32`
- `results/selected_table.csv`: selected rows `1,2,4,8,12,16,24,32`
- `results/table.tex`: the selected four-column table, requiring `booktabs`;
  it may need a small font or width adjustment in the surrounding article
- `verification/`: portable, deterministic receipts from the release replay,
  including the 72 negative tests and a comparison of two complete outer runs

Ratios in JSON and CSV are reduced exact numerator/denominator pairs. The
10-decimal displays are formed only after exact arithmetic, using `Decimal`
with 70 digits. CSV has UTF-8 encoding, LF line endings, and fixed column order.
The k=0 fresh convolution is marked `N/A`, because the identity is stated for
k>=1. Small rows can be inspected without a viewer or a third-party library.

## Deliberate corruption and optimization safety

Every correctness guard is an explicit runtime check. An AST scan rejects
Python `assert` statements. The full replay performs **72 negative tests**:
24 named mathematical-value corruptions, seven mutations of actual reference
files, one actual extra Python source file, and four output-safety failures,
each under normal Python and `-O`. The source inventory requires exactly the
three documented Python files and the README; the result inventory requires
exactly the four documented output files.
Reference mutations cover an exact JSON count, duplicate JSON keys, moment and
selected-table CSV values, a TeX change, a missing file, and an unexpected file.
Every corruption must exit nonzero with its intended failure marker and no new
success output. An existing-directory test additionally checks all prior bytes
remain unchanged. The driver pre-write probe can be run separately:

```sh
python3 -B reproduce.py --out ../must-not-exist --self-test-failure
python3 -B -O reproduce.py --out ../must-not-exist --self-test-failure
```

These commands are expected to fail and leave that path nonexistent. The
failure suite tests documented paths, not every conceivable malformed input.

## Scope of the evidence

These are exact finite checks. They do **not** prove the report's limiting
equivalent, its uniform tail bound, an effective error constant, an onset for
an asymptotic estimate, or a numerical radius for the inverse enclosure. In
particular, the ratio is still about 3.22 at k=32, so the table is not presented
as a test of asymptotic accuracy. Those assertions depend on the article's
all-index mathematical arguments. No empirical monotonicity is extrapolated.
