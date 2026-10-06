# Report154 companion

This is original companion code for *Diagonal poly Cauchy permutations at all
fixed orders*. The finite formulas and their attribution are in Report154.
These programs need no private proof, previous report, or network access.

## Files and dependencies

- `exact_checks.py`: exact finite checks, Python standard library only
- `test_companion.py`: 33 standard-library regression and output-safety tests
- `numerical_diagnostics.py`: optional floating-point diagnostics
- `requirements-numerical.txt`: the optional pin `mpmath==1.3.0`
- `inputs.json`: source, offset, complete official prefix, and snapshot digest
- `claims.json`: what the finite computations check, and what they do not prove
- `results/`: deterministic results from ordinary and optimized Python

`results/run_commands.json` records the six exact command vectors, output
hashes, tool versions, and successful byte-identical final-source replays.

The scripts share `../release_tools.py`, which ships with the report.
The exact checker and the test suite do not require mpmath. Importing the
optional diagnostics module does not import or install mpmath; running it
requires the exact pinned version. No script installs anything.

Python 3.10 or later and POSIX `O_NOFOLLOW`/`O_DIRECTORY` are required.
The release was run with CPython 3.12 and mpmath 1.3.0.

## Run from the report directory

The default is JSON on standard output, without creating result files:

```
python3 -B companion/exact_checks.py
python3 -B -O companion/exact_checks.py
python3 -B companion/test_companion.py
python3 -B -O companion/test_companion.py
```

Use `--output PATH` only for a **new** file in an existing directory. For example:

```
python3 -B companion/exact_checks.py --output /tmp/report154-fresh-exact.json
```

Existing files, directories, final symlinks, hardlinked existing targets,
symlinked ancestors, and paths containing `..` are rejected. Parent directories
are opened without following symlinks and pinned by descriptors. The final
open uses `O_CREAT|O_EXCL|O_NOFOLLOW`; it cannot overwrite an existing target.
The parent directory must already exist. Files are created with mode 0600.
These guarantees assume the shipped code and filesystem owners are trusted;
they do not defend against a privileged actor changing the process or its
already-open directories. An interrupted write can leave a partial newly
created file; subsequent runs will reject that name rather than overwrite it.
The program's guarantees do not extend to shell redirection chosen by a caller.

Both CLI arguments and direct top-level runner arguments are bounded:
`16 <= --max-n <= 64`, `2 <= --order <= 6`. The exact checker defaults to 64
and 6. No validation condition uses a removable Python `assert` statement.
`unittest` assertion methods remain active under `python3 -O`.

## Exact checks and release results

The default run completes 11,993 exact comparisons/conditions:

1. All 4,225 pairs `0 <= n,k <= 64` agree by three routes:
   - unsigned first-Stirling recurrence and `sum_m [n,m](m+1)^k`
   - separately generated first/second-Stirling tables and
     `sum_j j! [n+1,j+1] {k+1,j+1}`
   - integer Leibniz derivative convolution for
     `F_0(z)=exp(z)`, `F_(n+1)(z)=(exp(z)+n)F_n(z)`
2. The entire 17-term official A192563 prefix, at offset zero, agrees exactly.
3. The weighted-partition contraction formula equals the independent formal
   recurrence `H_d = sum_(w=1)^d w Q_w H_(d-w)/d` through `E6`.
   The respective term counts for `E0,...,E6` are `1,2,5,11,22,42,77`.
   All 160 terms, their weights and even degrees are checked. Odd weighted
   degrees contract to zero. The displayed `E1` and `E2` and the coefficient
   `-1/12` in the leading `E1` scaling are separately checked.
4. Bernoulli cumulant polynomials from `p(1-p)d/dp` equal their explicit
   second-Stirling expressions through order 14. Checks include exact rational
   evaluations, endpoints, full bivariate Euler/Bernoulli operator polynomials,
   and Euler-operator identities on monomials through degree 32.
5. The strict and nonstrict sequence thresholds are tested at 64 exact
   equalities and intervening values. 504 exact strict finite brackets test
   the floor/ceiling conclusion, including integral bracket endpoints.
   These brackets are constructed from exact sequence values, not from an
   assumed finite asymptotic error constant.

`results/exact.json` and `results/exact-optimized.json` have identical
mathematical payloads, with SHA-256:

```
c49be8e0a455787b3710d208b6120c82d03e46c1cdb59c5e81994ad1f9aa74c5
```

Their `python_optimization` metadata differ intentionally. The JSON contains
all 65 diagonal integers, every rational contraction coefficient, all 14
Bernoulli polynomials, and per-category check counts. A contraction term
with `coefficient=c`, `b_power=s`, and `kappa_powers={j:m_j}` means
`c * product_j(kappa_j**m_j) / b**s`.

`results/tests.json` and `results/tests-optimized.json` each record 33 passing
tests. These include injected wrong prefix/formula/coefficient values,
deliberate validation failure under `-O`, normal/optimized parity, CLI bounds,
all listed unsafe output classes, and descriptor pinning across an ancestor
rename. No comparison relies on asserts that optimization would remove.

## Optional diagnostics

With mpmath 1.3.0 already available:

```
python3 -B companion/numerical_diagnostics.py
python3 -B -O companion/numerical_diagnostics.py
```

The default uses 100 decimal working digits and prints 70 significant digits.
`100 <= --digits <= 200` and `2 <= --order <= 6` are enforced. The samples
are fixed and bounded: diagonal sizes 20, 50, 100, 200, 500, 1000, and
`(n,k)=(50,25),(50,100),(200,100),(200,400),(500,250),(500,1000)`.
The exact count calculation retains only the current unsigned-Stirling row.
It never serializes a large decimal integer: it records a bit length and
SHA-256 of the exact lowercase hexadecimal representation, avoiding Python's
decimal-conversion digit limit.

Safeguarded Newton iteration obtains the positive saddle from finite sums
of `p_q=exp(r)/(exp(r)+q)`. The ordinary logarithmic derivatives use exact
integer Bernoulli cumulant polynomials, evaluated at those probabilities;
the Euler derivatives use second-Stirling coefficients. No repeated gamma
differentiation supplies the cumulants. The finite log product is separately
compared with its log-gamma expression. Rational Gaussian coefficients are
kept exact until their high-precision evaluation.

For each sample and `R=1,...,7`, results report

```
M_nk = k! F_n(r)/(r^k sqrt(2*pi*b))
P_R = sum_(q=0)^(R-1) E_q
relative_model_error = M_nk*P_R/A_nk - 1
scaled_residual = (A_nk/M_nk-P_R)/(r/k)^R
```

The normal and optimized numerical result files have identical sample data.
All values are floating-point observations, not interval bounds. Finite
agreement does not prove an asymptotic remainder, a uniform constant or
onset, or a finite-X threshold decision. The analytic proof is in the report.
No growing-order or exponentially small remainder is claimed.

## Exact recorded release commands

These commands were run from the report directory, when each result path
was absent. Use new names or stdout when reproducing; existing release
results are intentionally protected from replacement.

```
python companion/exact_checks.py --output companion/results/exact.json
python -O companion/exact_checks.py --output companion/results/exact-optimized.json
python companion/test_companion.py --output companion/results/tests.json
python -O companion/test_companion.py --output companion/results/tests-optimized.json
python companion/numerical_diagnostics.py --output companion/results/numerical.json
python -O companion/numerical_diagnostics.py --output companion/results/numerical-optimized.json
```

The scripts do not record elapsed times, temporary paths, or wall-clock
timestamps in successful results. Deterministic outputs do depend on the
recorded parameters and, for floating point, the pinned library/toolchain.
