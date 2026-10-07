# Report230 reproduction code

Self-contained Python code for the endpoint family

    a_p(0) = 1,
    a_p(n) = sum_{k=0}^{floor(n/(p+1))} (n-pk)^(pk) binom(n-pk,k).

The core uses only Python's standard library and exact `fractions.Fraction`
arithmetic. It has no network calls, external data files, private imports,
SymPy dependency, or machine-specific paths. Python 3.10 or later is recommended.
The checked output was generated with Python 3.12.14 and mpmath 1.3.0.

## Quick start

Run these commands from this directory. Each command also works from any working
directory if its script is given by its actual path.

```sh
python -B selftest.py
python -B endpoint.py coefficients --p 2 --order 4
python -B endpoint.py coefficients --p 3 --order 6 --json
python -B endpoint.py critical --order 4
python -B endpoint.py marked --p 3 --order 3 --cumulant 2
python -B endpoint.py arrays --p 2 --order 3 --json
python -B endpoint.py count --p 2 --n 100 --json
```

`selftest.py` has no optional dependency. It checks exact identities using an
independent finite-difference/factorial-moment construction, direct finite sums
and independently multiplied generating-function coefficients, displayed
coefficients, centered moments, and active validation under both ordinary Python
and `python -B -O`. Test failures use exceptions, not removable assertions.

For numerical diagnostics only, install the optional dependency in an environment
of your choice, for example:

```sh
python -m pip install -r requirements-optional.txt
python -B selftest.py --numerical
python -B diagnostics.py suite
python -B diagnostics.py suite --deep
```

All programs print results to standard output and do not save files on their own.
Use shell redirection to save an output. CLI errors have nonzero exit status.
`--help` describes each command. Exact coefficient commands support text or JSON;
numerical commands print JSON. Rational JSON values are exact strings such as
`"-13/6"`, and polynomial keys are powers. Omitted coefficients are zero.

## Normalizations and interfaces

For fixed integer p >= 2, put q=p+1,

    c = exp(p^2/q) q^(-1/q),  t=n^(-1/q),  lambda=c/t,
    M_p(n) = (1/q) (n/q)^(pn/q) exp(lambda).

`endpoint.fractional_coefficients(p,K)` returns dictionaries for C_0(c),...,C_K(c)
in the normalized expansion

    a_p(n)/M_p(n) = sum_{k=0}^K C_k(c)t^k + O(t^(K+1)).

`endpoint.coefficient_arrays(p,J)` returns `(D,H,U)` indexed 0 through J, where

    Delta_n(r) = sum_{j>=1} D_j(r)n^(-j),
    H_0=1, H_j=(1/j) sum_{s=1}^j s D_s H_{j-s},
    U_j(z)=E[H_j(X)], X~Poisson(z).

`endpoint.defect_polynomials(p,J)` also permits p=1. `endpoint.touchard(d)` returns
T_d(z)=E[X^d]. Defect power sums are built by the elementary telescoping recurrence
for sum_{h=0}^{r-1}h^j; Poisson moments use the Touchard recurrence. None require a
symbolic algebra system.

`endpoint.marked_coefficients(p,J,h)` returns `(L,theta_h_L)`, with L_0=0 and

    L_j=U_j-(1/j) sum_{k=1}^{j-1} k L_k U_{j-k},
    theta=z d/dz,
    h-th defect cumulant = lambda + sum_{j>=1} (theta^h L_j)(lambda)n^(-j).

Here the sum gives algebraic coefficients. Marked-law results in this package are
restricted to p >= 2; residue-conditioned Poisson references are essential.

For the separate critical case p=1, put c=sqrt(e/2), t=n^(-1/2) and

    M_1(n) = (1/2)(n/2)^(n/2) exp(c sqrt(n)-3e/8).

`endpoint.critical_coefficients(K)` returns C_0(c),...,C_K(c) for a_1(n)/M_1(n).
It implements the weighted centered generator: t has weight 2, the centered
variable u has weight 1, and exp(V) is retained through weight **2K+1** before
substituting exact centered Poisson moments. This is a different computation
from substituting p=1 into the subcritical averaging expansion.

`endpoint.exact_count(p,n)` returns a Python integer; n=0 is explicitly 1.
The k=0 contribution is explicitly 1, so evaluation never relies on 0^0.

## Diagnostic commands

```sh
# Complete finite sums, with independent exact-integer and transformed evaluation
python -B diagnostics.py finite --p 2 --n 10000 --order 12 --h-order 12 --dps 90
python -B diagnostics.py finite --p 3 --n 10000 --order 12 --h-order 12 --dps 90
python -B diagnostics.py finite --p 1 --n 10000 --order 4 --dps 90

# Same-residue conditioned Poisson references; explicit window/tail information
python -B diagnostics.py marked --p 2 --n 1000000000 --dps 90
python -B diagnostics.py marked --p 3 --n 1000000000 --dps 90

# Finite Newton iterations from the Lambert-W core
python -B diagnostics.py inverse --p 2 --n 1000000 --order 4 --steps 3
python -B diagnostics.py inverse --p 1 --n 1000000 --order 4 --steps 3
python -B diagnostics.py inverse --p 3 --n 1000 --order 0 --steps 3 --exact-target
```

`finite` evaluates **every** allowed defect 0<=r<=n. It does not use a Poisson
window or Taylor coefficients to evaluate the transformed finite sum. The
original count is an exact integer, and its transcendental normalization is
computed by mpmath. Relative errors mean approximation/exact-normalization minus
one. A reported identity discrepancy of zero means zero at the working precision.

The fractional truncation through t^K and the full sum
`sum_{j=0}^J U_j(lambda)/n^j` are different approximations, even when K=J. The latter
retains higher fractional powers. They must not be conflated in tables or claims.

**Important moderate-n warning:** at p=3,n=10000, the t^12 fractional truncation
has relative error approximately -0.661536, whereas full H order 12 has error
+0.00122912. Formal order alone does not guarantee numerical usefulness. The
warning appears in CLI help and diagnostic output; `suite --deep` reproduces it.

`marked` reports a central window, its number of lattice points, mean/variance,
and total-variation comparisons of laws normalized on that window. Its analytic
Chernoff formulas bound how much the reported TV distances can differ from
complete-law TV distances, including the exact-law tail via Delta<=0. The bounds
are evaluated by ordinary high-precision arithmetic, not outward rounding. They
are TV bounds, **not moment-error bounds**; the moment outputs remain explicitly
labeled central-window diagnostics.

`inverse` uses Y=F_K(n) by default, so its smooth-model target root is known to be
n. `--exact-target` instead uses Y=log(a_p(n)); its index error then includes model
truncation. A specified finite number of Newton steps is taken, with no hidden
root solve. Every iterate checks finiteness, positivity of Q_K and positivity of
F_K'. These checks do not certify convexity or a finite asymptotic onset. Nearest-
integer recovery requires an exact-range input and sufficiently large n;
arbitrary thresholds require a ceiling envelope. No rounding certificate is
provided.

Every transcendental output is a diagnostic, **not certified interval arithmetic**.
The algorithms establish no convergence of the infinite asymptotic series,
optimal truncation, secondary exponential sector, or uniformity in growing p.

## Active resource limits

These are conservative program limits, not mathematical restrictions. Invalid
inputs raise `TypeError` or `ValueError`; booleans are not accepted as integers.
All guards remain active with Python optimization enabled.

- p: 1..64 for defects/counts/finite diagnostics, 2..64 for subcritical generators
- D/H/log-normalizer order: 0..16
- Fractional order: 0..32, also requiring floor(K/(p-1)) <= 16
- Critical order: 0..8
- Marked cumulant index: 1..16
- Exact count n: 0..20000; normalized finite diagnostics require n>=1
- Diagnostic precision: 30..200 decimal digits
- Marked diagnostic: p=2..8, n=1000..10^12, at most 100000 window lattice points;
  both reference means must lie in the retained window
- Newton diagnostic: at most 12 steps, n<=10^12 for a smooth-model target;
  exact-count targets retain the n<=20000 limit

Large exact counts can be expensive. There is no expensive default run: the small
suite uses complete counts at n=300. On the checked environment the numerical
selftest ran in about 0.4 s, the small suite in about 0.2 s, and the deep suite in
about 7 s. Times vary by hardware and are not embedded in the deterministic JSON.

## Included checked output

- `results/diagnostics.json`: `python -B diagnostics.py suite --deep`
- `results/selftest.txt`: `python -B selftest.py --numerical`

The deep results include p=1,2,3 complete sums at n=10000 and p=2,3 marked-law
comparisons at n=10^9. Other residue classes can be checked by changing n.
