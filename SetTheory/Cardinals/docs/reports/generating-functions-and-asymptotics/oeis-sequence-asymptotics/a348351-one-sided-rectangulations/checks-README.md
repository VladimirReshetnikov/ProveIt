# Exact finite validation for report111

This directory is self-contained. Python 3.9 or later and its standard library
are sufficient. No SymPy, NumPy, floating-point residual, network connection,
private working file, or installed package is needed.

From the report directory:

```sh
python3 checks/verify_report111.py
python3 -O checks/verify_report111.py
python3 checks/mutation_campaign.py
python3 -O checks/mutation_campaign.py
```

The checker reads `report111_fixture.json` by its own script directory, so these
commands also work from a different working directory. Optional `--fixture PATH`
accepts a replacement fixture. The checker never writes to its inputs; its JSON
result goes to standard output. A rejected input exits 1 and emits a single named
`CHECK_FAIL category.detail` diagnostic to standard error. All guards are explicit
exceptions, not `assert` statements, and remain effective under `python -O`.

## Exact arithmetic and fixture format

Algebraic values are canonical triples `[a,b,d]` meaning `(a+b*sqrt(17))/d`,
where all entries are integers, `d>0`, and `gcd(a,b,d)=1`. The implementation uses
`fractions.Fraction` for the two rational coefficients. Field operations are
exact. To order `a+b*sqrt(17)`, opposite-sign terms are compared by their rational
squares; no decimal approximation is used. Integer square roots use `math.isqrt`.

The fixture parser requires the exact top-level field inventory, exact nested
object inventories, exact vector/matrix sizes, exactly 24 distinct colored
edges, exactly 17 OEIS entries, and exactly five named length-three cycles.
It rejects duplicate JSON keys, duplicate edges, noncanonical algebraic triples,
booleans masquerading as integers, floats, nonfinite numbers, and unknown fields.

## What is checked

- The transition table is reconstructed independently from the two weak source
  inequalities: the source-color level change is `1,0,0,-1`; the lower bound on
  `dx` is zero iff `c in BR or d in BG`, otherwise minus one; the lower bound on
  `dy` is zero iff `c in BG or d in BR`, otherwise minus one. All integer solutions
  are compared with the fixture's explicit edge table
- The matrix A, positivity of A squared, its characteristic polynomial, Gamma,
  positive right eigenvector, per-edge probability normalization, stationary
  distribution, conditional and stationary drifts, the bounded Poisson corrector,
  zero martingale drift, and the coordinate increment bound
- Effective martingale covariance, strict positive definiteness, correlation,
  and color dependence of the conditional covariance. A separately computed
  Laurent determinant and implicit Perron Hessian reproduce the same covariance
- The dual edge balance, reversed displacements, stochasticity, stationarity,
  zero drift, a solved dual Poisson corrector, the same effective covariance,
  and all finite killed-kernel duality identities for lengths 0 through 3 between
  the sixteen states with positions (0,0), (1,0), (0,1), (1,1)
- All 17 OEIS values for n=0 through 16 from quadrant-walk counting; independent
  direct enumeration of the four vincular forbidden patterns through n=7;
  the n-minus-one length, unrestricted initial colors, origin endpoint, terminal
  white convention, and finite PF probability-to-count transfer through length 5
- The red zero loop and explicit common-length-three red-return cycles with
  displacements 0, plus/minus E, plus/minus N. Complete initial/terminal connector
  paths for H=1 through 8, all tested box points and colors, and exhaustive small
  variable-padding injections with recovery and collision checks
- Deterministic ascending/central/descending integer schedules, including scale
  boundaries and integers as large as 10^300; exact integer-square-root elementary
  padding; every tested pair of prefix/suffix times in the exact bridge budget
- Squared whitened step bounds, seed radii and the no-skip inequality; exact
  annular geometric sums and largest-scale selection through n=10^300; original
  and dual seed paths; sixteen fully encoded variable-time concatenations whose
  first forward/backward hits uniquely recover both prefixes even when the
  middle segment makes further crossings
- The minimal polynomial X^2+29X+2 of 2cos(theta), its nonsquare discriminant
  833=49*17, both roots in Q(sqrt(17)), and the exact inequalities
  -2<2cos(theta)<0 and its other conjugate<-2

The annular examples use illustrative parameters q=2, H=8, b=4, T=1 and
delta=1/8. They validate the algebra and integer bookkeeping, not numerical
values of the analytic FCLT cutoff R0 or of a valid Brownian crossing time T(q).

The minimal-polynomial/conjugate certificate is the finite algebraic input to the
root-of-unity argument in the article. It is not a numerical test of whether an
arccosine is irrational.

## Source and analytical boundary

The transition rules, colored-walk convention, and published conjecture are from
Asinowski, Cardinal, Felsner and Fusy, *Combinatorics of rectangulations: Old and
new bijections*, Combinatorial Theory 5(1) (2025), article 14, §4.6, pp.39–40;
the weak inequalities also use the preceding walk-model definitions:
https://escholarship.org/uc/item/92s0c9qg . The integer prefix is OEIS A348351:
https://oeis.org/A348351 . These source facts are transcribed into the fixture;
the checker does not download or authenticate external sources.

Finite tests do not prove a statement for all integers, a functional or local
limit theorem, uniform Brownian crossing bounds, the logarithmic asymptotic,
or the arithmetic regular-singularity theorem for G-functions. Those are
mathematical arguments in the report. In particular, passing this checker is
not a computer-assisted proof of non-D-finiteness or of a multiplicative
coefficient equivalent. The scope is finite algebra, indexing, explicit
constructions, and regression protection for those inputs.

## Mutation campaign and preservation

The campaign first copies only the checker and fixture into an isolated temporary
directory. Both pristine baselines must pass before any corruption is tested.
Child interpreters use `-I -S -B`, with and without `-O`, excluding site packages
and user import paths. Normal and optimized pristine JSON results must match.

Each deliberate fixture or implementation corruption is run in both modes and
must fail with its particular named mathematical or schema diagnostic. Merely
exiting nonzero does not count. Syntax errors, import errors, arbitrary crashes,
and timeouts are not accepted as detections. A deliberately syntax-broken
negative control verifies that policy. Source-code mutants must compile first.

The campaign hashes the original checker, fixture, campaign and this README
before and after all isolated runs and requires byte-for-byte preservation.
`mutation_results.json` records those actual hashes and every observed diagnostic.
The validation summary and manifest describe the completed run and exact bytes.
