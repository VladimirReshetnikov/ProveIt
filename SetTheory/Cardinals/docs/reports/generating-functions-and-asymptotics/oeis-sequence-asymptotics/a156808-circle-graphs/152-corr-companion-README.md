# Report152 exact companion

This self-contained, dependency-free Python companion checks finite combinatorics
and exact rational coefficient identities used in the first-correction report.
It does **not** prove analytic uniformity, the nonlocal asymptotic error bound,
the split-tree transfer theorem, prime representation uniqueness, or an eventual
integer inverse bound. Those are mathematical proof obligations in the report.

## Reproduce

Requirements: Python 3.10 or later on a POSIX system with `O_NOFOLLOW` and
`O_DIRECTORY` (the recorded run used Python 3.12 on Linux). No installation or
third-party package is required. Run from this directory:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B test_companion.py
python3 -B -O test_companion.py
```

Each checker invocation prints a complete machine-readable JSON result to
standard output and exits with code 0 on success, 1 on verification failure.
Tests print their progress to standard error and a JSON summary to standard
output. The four current release results are in `results/`:

- `check-release-normal.json`: full exact diagnostic data
- `check-release-optimized.json`: byte-identical result from Python `-O`
- `tests-release-normal.json`: 24 passing tests with the normal test runner
- `tests-release-optimized.json`: 24 passing tests with the optimized test runner

For a new retained result, choose an unused filename:

```sh
python3 -B verify.py --output results/check-rerun.json
python3 -B -O test_companion.py --output results/tests-rerun.json
```

`--output` intentionally refuses existing files. It accepts only new `.json`
files strictly inside this companion's `results/` directory. Parent directories
must already exist; no output directory is created implicitly. Output path
components are opened by directory descriptor with `O_NOFOLLOW`; the final file
is opened with `O_EXCL | O_NOFOLLOW`. Paths outside `results/`, `..` traversal,
symlinks, existing output files, source files, and input files are never accepted
as overwrite targets. Shell redirection is outside this program's control; use
`--output` when the program's output protections are desired.

## What is checked

### Local atoms and compatible clusters

For each M in 8, 10, 12, 16, 20, 30, 40 the script constructs X and Y singleton
chords on cyclic distances one and two, and both Z matchings of each pair of
disjoint adjacent endpoint pairs. It verifies uniqueness of the atom list and
counts all ordered support overlaps, including repeated atoms. It separately
counts **unordered distinct compatible atom pairs sharing a chord**, and
exhaustively enumerates all non-elementary two-chord polymers.

The exact tested counts include XZ=M, YZ=3M, YYZ=M and compatible shared-chord
ZZ=M(M−5). For ordered support overlaps, the finite checks include
ZZ=12M³−98M²+210M. Agreement at these finite M is not a proof of this polynomial
identity for all M, or of any asymptotic error estimate.

A sparse rational polynomial calculation combines polymer activities, endpoint
exclusion, and the matching-weight correction to reproduce

F(x,y,z) = x+y+z−x²/2−y²/2−z²−2xy−xz−yz+y²z.

It gives F(−1,−1,−1)=−10, and converts this to −5 in the 1/n normalization when
M=2n. The claim name `prime_first_relative_n` records the numerical substitution
used by the report; the identification with prime counts requires the report's
separate analytic and representation arguments.

### Three-chord interval lemma

All 15 perfect matchings on six endpoints are tested for each block-size pair
0+6, 1+5, 2+4, and 3+3: 60 finite cases in total. X and Y witnesses are recognized
only at linear distances one and two inside a block. Z witnesses use two
within-block adjacent endpoint pairs. Adjacencies across separating gaps are
never assumed. Every matching has a witness.

### Rooted graph classes

For graph orders 2, 3, 4, and 5, the script enumerates every labeled simple graph
and every indexed chord matching. Isomorphism classes are canonicalized using
all vertex permutations. Every connected class is found among the intersection
graphs of the matchings. All automorphisms are then enumerated, and **vertex
orbits**, rather than labeled vertices, are counted as root choices.

The resulting numbers of connected classes are 1, 2, 6, 21; the rooted counts
b0, b1, b2, b3 are 1, 3, 11, 58. Each class's edges, automorphism count, and vertex
orbits are retained in the JSON. The finite fact b3=58 is checked independently;
its use in a second-order expansion remains conditional as described below.

### Rational transfer algebra

For all 45 integer pairs 0≤ell≤k≤8, the first three coefficients of the normalized
factorial ratio are computed by multiplying the exact finite-product series and
compared with the claimed logarithmic expansion. Exact Poisson moments at
parameter 3/2 are generated from the Stirling recurrence, with no numerical
approximation or floating-point fitting.

The first-order shifts are 5/4 for connected graphs and 7/4 for all graphs.
Substituting the prime first coefficient −5 gives −15/4 and −13/4. The component
ratio algebra yields c_n/g_n = 1−1/(2n)−1/n² at the displayed orders.

**Conditional second-order identities:** if the prime expansion has a separately
justified second coefficient beta and the requisite remainder, the checked
transfer expressions are beta+(11/4)alpha+163/32 and
beta+(13/4)alpha+223/32. At alpha=−5 these become beta−277/32 and beta−297/32.
No value of beta is supplied, inferred, fitted, or conjectured.

### Bounded automorphism weights

Every root-fixing automorphism is counted explicitly at one representative of
each vertex orbit, with an exact orbit-stabilizer check. The excess-zero,
excess-one, and excess-two histograms are respectively {1:1}, {1:1, 2:2}, and
{1:3, 2:6, 6:2}, where each key is a rooted automorphism-group order.

With rho=2^(−t) and sigma=6^(−t), these histograms give
b1(t)=1+2rho and b2(t)=3+6rho+2sigma. Rational polynomial Poisson summation
independently reproduces the first-order shift (b2+b1−b1²)/4. Dividing by the
ordinary expansion gives the bounded reciprocal transform coefficient
−1/2+rho−rho²+sigma/2 and amplitude exponent rho−1, for both sampling laws.

At t=1 the connected/all labeled coefficients are −47/12 and −41/12, with
amplitude n! exp(−2); the normalized reciprocal-weight coefficient is −1/6.
At t=infinity the asymmetric coefficients are −17/4 and −15/4, with amplitude
exp(−5/2); the normalized asymmetry coefficient is −1/2. These statements use
the common h_n normalization. The unweighted t=0 specializations are checked
against the main first-order coefficients.

The program verifies the finite histograms and exact algebra only. Uniformity
in t and the asymptotic remainders come from the separately audited supplement.
No unbounded automorphism-group moments are computed or claimed.

### Inverse algebra

With A=log(2u), C=(3+log 2)/2, and beta the generic first relative coefficient,
the script works in exact Laurent polynomials and verifies both residuals for

d0 = 1+C/A,

d1 = (13/24−beta)/A−C²/(2A³).

The constant residual and the coefficient of 1/u are identically zero. The
checked connected and all-graph numerators are 103/24 and 91/24, and their
center difference has multiplier 1/2 in 1/(uA). This calculation does not supply
a numerical error constant, onset, or permission to round the center
unconditionally.

## Claims, tests, and provenance

`claims.json` is a separately transcribed list of exact targets; the checker
recomputes its results and requires equality of the key set and every value.
Values must be reduced rational strings. `--claims path/to/claims.json` permits
an alternate file for independent testing and refuses symlink input paths, special files, and input files larger than one MiB.
There is no “update expected results” mode.

The verifier uses explicit exceptions instead of `assert`, so `-O` cannot remove
checks. The 24-test suite runs complete checker subprocesses in normal and
optimized modes, compares their full outputs, changes claimed local, inverse,
and labeled coefficients and requires failure in both
modes, checks the effect of a changed rooted count, and exercises overwrite,
source/input preservation, path-traversal, and symlink safeguards. Input reads are descriptor-pinned and nonblocking;
additional tests reject FIFO inputs and verify that swapping a parent directory
for a symlink cannot redirect a claims read. Failed claim
verification produces no output file.

`provenance.json` records descriptive input labels and SHA-256 digests, the
commands actually run, and checksums of this companion's deliverables. The
research scripts were read as references; this checker does not execute or
import them. The checked-in JSON is diagnostic evidence, not a substitute for
the report's proof or an independently established asymptotic theorem.

## Release file selection

The release allowlist is recorded as `package_files` in `provenance.json` and
contains the current verifier, tests, claims, this README, provenance, and the
four `*-release-*.json` files. Earlier baseline and intermediate run files may
be retained locally for traceability; they are not current release evidence and
are omitted from the user-facing package. Reference research scripts are never
bundled or imported.
