# Exact reference computations for coupled contractions and refinement towers

This directory contains a small standalone Python reference implementation
and finite exact regression checks for the accompanying report. All quantities
used in inequalities are `fractions.Fraction` or integers. Python's standard
library is sufficient; there are no third-party dependencies.

Run:

    python3 run_checks.py
    python3 approximate_actions.py
    python3 upper_branch_reference.py --output ../validation/upper_branch_checks.json

The first command runs the unittest suite and recreates the data tables and
validation record. The other commands check the approximate-action, delayed-update,
and upper-branch examples. To run only the tests:

    python3 -m unittest -v test_certified_contractions.py

**Status:** these are exact finite computations. They are not a proof of the
universal mathematical theorems, a proof of primitive recursiveness from the
Python implementation, or an embedded `Prf PRAAx` derivation. Those separate
arguments and formalization obligations are in the report.

## Coupled gain certificate

`GainCertificate(A,w,s)` checks a square nonnegative rational matrix, strictly
positive rational weights, an integer `s >= 1`, and the exact inequality

    A w <= (1 - 1/s) w.

It rejects malformed dimensions, negative gain entries, zero weights, failed
inequalities and floating-point inputs. The boundary `s = 1` is supported:
its nonnegative gain matrix must act as zero on the positive weights.

`derive_weights(A,m,theta)` uses a supplied positive integer `m` and checks

    A^m 1 <= theta 1,     0 <= theta < 1.

It returns

    w = sum_{j<m} A^j 1,
    s = ceil(max_i(w_i)/(1-theta)).

There is no unbounded search for a successful power. The resulting gain
inequality is checked again. The finite identity
`A w = w - 1 + A^m 1` explains the construction.

For a nonnegative residual vector `rho` and any `N >= 0`,
`neumann_supersolution` computes

    z_N = sum_{j<N} A^j rho + s * ||A^N rho||_w * w

and verifies the supersolution inequality `z_N >= A z_N + rho`.
Tests include `N = 0`, zero residuals, a three-dimensional matrix, and
comparison with an independently computed closed-form inverse in dimension
two.

### Affine example

The example uses

    A = [[0, 2], [1/8, 0]],
    w = (4, 1), s = 2,
    T(x,y) = (1 + 2y, 1/4 + x/8).

The box `[0,4] x [0,1]` is invariant and `(2,1/2)` is an exact fixed point.
The unweighted maximum norm does not give the required half-contraction;
the positive weights do. The distinct finite-power construction with
`m=2, theta=1/4` produces `w=(3,9/8), s=4`. This is a correct, less sharp
certificate.

## Nonlinear projective tower

For `n >= 1`, work on `[0,1]^n` with

    d_n(x,y) = max_{i<n} 2^(-i) |x_i-y_i|,
    a_i = 1/(4(i+1)),
    F_(n,i)(x) = a_i + x_i^2/8 + x_(i+1)/8,

where the boundary coordinate `x_n` is zero.

`tower_y(n)` starts at zero and takes exactly `n+4` steps. Each step evaluates
the rational polynomial exactly and rounds each output **down** to `n+8`
fractional binary bits. Rounding is floor, including on negative inputs to
the generic rounding helper; the actual tower stays nonnegative.

The intended report bounds are:

- half-contraction in `d_n`;
- residual `r_n <= 2^(-n-4)`;
- adjacent restriction/update defect `eta_n <= 2^(-n-2)`;
- adjacent solver discrepancy `e_n <= 2^(-n)`;
- coordinate sampler `Q(i,k) = y_(i+k+3)[i]`;
- for `ell >= k`, `|Q(i,k)-Q(i,ell)| <= 2^(-k-2)`;
- equation residual
  `|Q(i,k) - a_i - Q(i,k)^2/8 - Q(i+1,k)/8| <= 2^(-k-4)`.

The tests verify finite instances of these claims through dimension 16. They
also check the commutation defect on a point where the stated upper bound
is attained exactly, zero-tail cases, restrictions skipping levels, and
rounded versus exact orbits in small dimensions. This targets boundary
indices and error-budget conventions rather than merely comparing an
implementation against an identical copy.

`data/coordinates.csv` and `data/coordinates.json` display four coordinates
at precision 10, using levels 13 through 16. Sample values and interval
endpoints have **exact terminating decimal** strings. The radius
`2^(-k-2)` around a sample encloses the infinite fixed coordinate by the
universal theorem proved in the report. The script itself checks the finite
sample computations and their residuals; a finite test cannot establish that
infinite conclusion.

## Why a uniform contraction gap matters

The counterexample uses

    epsilon_n = 2^(-n-2),
    c_n = n mod 2,
    F_n(x) = (1-epsilon_n)x + epsilon_n c_n

on `[0,1]`. Every map is a contraction with exact fixed point `c_n`.
The adjacent map discrepancy is exactly `epsilon_n`, tending to zero,
but the fixed points alternate between zero and one. The ratio of defect
to contraction gap is one. The tests verify these exact identities and
record the example in `data/examples.json`.

## Independent upper branch

`upper_branch_reference.py` constructs a second branch in `[6,8]` without an
exact square-root primitive. It performs a fixed number of rational bisections
for the positive root of `16-z-2/(i+1)`, then runs a fixed backward chain with
terminal value 7. It checks 1,200 pairs of regular-name samples and 120
same-precision equation residuals using exact rational arithmetic. This branch
shows why the uniqueness theorem for the lower solution is restricted to the
unit cube. The universal estimates and the primitive-recursive clock are proved
in the report.

## Additional approximate-action checks

`approximate_actions.py` verifies 3,564 finite instances of the mixed-precision
action contract and checks the delayed-update clock and supersolution examples.
It regenerates `small_gain_checks.json`. These checks complement the main
unittest suite.

## Files

- `certified_contractions.py`: exact programs and certificate checks.
- `test_certified_contractions.py`: 24 unittest methods with finite parameter grids.
- `run_checks.py`: test runner and reproducible table generator.
- `approximate_actions.py`: mixed-precision and delayed-update reference checks.
- `upper_branch_reference.py`: rational-bisection upper-branch construction.
- `data/examples.json`: affine, Neumann, tower and missing-gap examples.
- `data/coordinates.csv`, `data/coordinates.json`: precision-10 coordinate table.
- `validation/unittest.txt`, `validation/results.json`: actual execution results.


