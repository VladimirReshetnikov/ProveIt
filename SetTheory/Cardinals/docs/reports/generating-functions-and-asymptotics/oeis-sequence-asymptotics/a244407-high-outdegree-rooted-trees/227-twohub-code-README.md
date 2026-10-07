# Report 227 reproduction code

Run commands below from the package root (the directory containing
`report227.tex`). Python 3.10 or later is required; Python 3.12.14 was tested.
The exact suite needs only the Python standard library and no network.

```sh
python -B code/reproduce.py --quick
python -B code/reproduce.py --full
python -B -O code/reproduce.py --full
python -B code/reproduce.py --caps
```

The optional numerical engine needs mpmath (tested version 1.3.0):

```sh
python -B code/reproduce.py --caps --numerics --order 5
python -B -O code/reproduce.py --caps --numerics --order 5
python -B code/reproduce.py --quick --numerics --order 8 --precision 80
```

Use `python -m pip install mpmath==1.3.0` in an environment you control if
needed. SymPy is not required. No packages are installed automatically.

## Output and reproducibility

The runner prints one deterministic JSON result to stdout and wall-clock
elapsed time separately to stderr. It does not write into the source tree.
Failures produce a nonzero exit code; ordinary mathematical checks use
`require()` and explicit exceptions, so `python -O` cannot remove them.
The code also deliberately tests failed guards and the accepted smallest diagnostic index m=1 (including moment orders 1 through 6). A normal and optimized
run with the same Python/package versions and arguments must produce the
same JSON. For example:

```sh
python -B code/reproduce.py --caps --numerics --order 5 > /tmp/report227-normal.json
python -B -O code/reproduce.py --caps --numerics --order 5 > /tmp/report227-optimized.json
cmp /tmp/report227-normal.json /tmp/report227-optimized.json
```

The following confirms the exact suite does not need site packages:

```sh
python -B -S code/reproduce.py --quick
```

Measured exact runtimes in the supplied Linux environment were about
0.1 seconds for quick, 4 seconds for full, and 10.5 seconds for caps.
The optional numerical engine adds roughly 0.3–0.5 seconds at a 60-digit
request. Hardware and Python versions can change these timings.

## Finite coverage and explicit caps

The CLI exposes three fixed profiles:

| Profile | bounded trees N | maximum tested k | colored trees N | coefficients and moments m |
| --- | ---: | ---: | ---: | ---: |
| quick | 32 | 16 | 8 | 160 |
| full | 80 | 32 | 11 | 800 |
| caps | 96 | 32 | 12 | 1000 |

The underlying exact APIs reject coefficient indices above 1,000,
bounded-tree N above 96, outdegree caps above 32, and canonical-tree N above
12. Rooted coefficients may reach 1,002 because J2 at degree 1,000 requires
r[1,002]. The fixture generator separately caps its final index at 96.
These are implementation limits, not mathematical boundaries. Changing a
cap is not a claim that larger inputs have been validated. The `caps`
profile has been run normally and under `-O`, exercising the exact upper
boundaries as well as the intentional over-cap rejection checks.

## What is checked

`exact.py` supplies these independently structured calculations:

1. A logarithmic integer recurrence for rooted-tree coefficients, Euler
   products for H and J2, G=1/(1-R), and F=HG
2. Direct binomial-factor multiplication and a two-variable forest DP,
   cross-checking the one-variable Euler-product computation
3. The defect B in both its positive and signed forms, with exact divisibility
   by two and positivity checked explicitly
4. A self-contained bounded-outdegree multiset DP, which does not use r,
   H, F or B as inputs. Differences of adjacent bounds yield T(N,k)
5. Plateau, first-boundary, forest-truncation, two-hub, and
   T(3k+1,k)=f[2k]-b[k]+2 checks against that bounded DP
6. Sorted nested-tuple enumeration of actual tree types and canonical
   one-colored and two-colored trees. This quotients by automorphisms
   explicitly. It tests the one-mark/depth identity, each ordered degree-pair
   generating function, the pair majorant, orbit-surplus inequalities,
   same-orbit symmetry corrections, and maximum-exact counts
7. Exact depth falling-moment recurrences, independently compared with sums
   over spine lengths through m=16. Decoration moments use exact integer
   convolution numerators. Ratios to leading equivalents at larger m are
   merely numerical diagnostics, with no pass/fail claim of convergence

Full coverage includes 528 plateau equalities, 32 first boundaries, 477
second-sector identities, 26 third-boundary identities, 503 forest
truncations, 726 one-color/depth coefficients, and 1,331 ordered two-color
size/degree-pair coefficients. The latter counts include zero coefficients.
It enumerates 3,047 tree types in total through N=11, including all 1,842
types at N=11. Each profile additionally checks the separate exact-generated
fixture and the externally observed OEIS samples described in
`data/README.md`.

The `caps` profile checks 528 second-sector identities, 31 third-boundary
identities, 559 forest truncations, 936 one-color/depth coefficients,
1,728 ordered two-color coefficients, and 132 pair-majorant coefficients.
It enumerates 7,813 tree types through N=12, with 4,766 at N=12. Defect
coefficients, positivity and signed/positive equality extend through m=1000.

## Optional finite-order numerical engine

`numerics.py` accepts integer orders 0 through 8 and requested decimal
precision 30 through 120, rejecting inputs outside these limits. Every
numerical call self-checks the supported order cap, even when it returns a
shorter requested jet. The reported precision describes arithmetic and
formatted output, not a rigorous guarantee of that many correct digits.

The engine constructs the universal rooted-tree Puiseux coefficients by
Lagrange inversion, composes the analytic subsidiary tails at rho, and
computes finite jets for R, H/(1-R), and the defect B. It produces the d_j
coefficients for f_m, the shifted e_j coefficients for A244407, and the
second-sector relative correction coefficients. Bernoulli-polynomial
Gamma factors and the inverse recurrence are checked with exact Fraction
arithmetic through order 8. The cancellation of B's s^-2 coefficient is
also checked as an exact rational identity after factoring its common
symbolic prefactor. No symbolic package is needed.

Constants are recalculated at two finite tail cutoffs and two precisions;
agreement and equation residuals are numerical checks, not interval bounds.
The output includes rho, beta, C, K, rho*K, L, L/K and both leading and
higher correction coefficients. It compares finite power and Gamma sums
with exact f_m coefficients. Lambert W uses the negative real branch W_-1.
The leading inverse, its finite formal correction, and the root of the
truncated smooth asymptotic expression are separately labeled.

An independent exact f_m recurrence settles the illustrated integer
thresholds within its explicit cap m=512. In the order-5 example at y=f_500,
the smooth root is 500+1.233932509300699...e-10, and the Lambert-centered
finite correction is 500+4.415529018321249...e-11. Both numerical ceilings
are 501; the exact integer comparison gives threshold 500. This is a
warning against unconditional ceiling equality, not a certified numerical
threshold enclosure.

Standalone commands are also available:

```sh
python -B code/numerics.py --order 5 --precision 60
python -B code/numerics.py --order 8 --precision 120
python -B -S code/numerics.py --formal-only
```

Only the last command requires no optional package. Neither exact nor
numerical modules access the network or depend on external data files for
their coefficient calculations.

## Scope

Finite computations test formulas; they do not prove the identities at every
size, uniform error bounds, weak convergence, historical priority, or any
arbitrary-order asymptotic theorem. Moment ratios are not distributional
proofs. Numerical constants and error estimates are not interval-certified.
An approximate smooth inverse cannot, on its own, certify an integer
threshold: a ceiling can be wrong near a jump. The report provides the
mathematical statements and their qualifications.

The standalone fixture generator requires --output to name a NEW file. It uses exclusive creation, rejects existing files and symlinks, and never silently overwrites a fixture.
