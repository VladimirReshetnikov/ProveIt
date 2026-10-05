# Exact verifier for Report 231

The core uses only the Python standard library. It does not import SymPy or any
other external package. Run from this directory with Python 3.9 or newer:

    python -B verify_report231.py

The output is deterministic JSON. To create a receipt, choose a fresh filename:

    python -B verify_report231.py --receipt new-receipt.json

An existing receipt is never overwritten. To check optimization safety:

    python -B -O verify_report231.py --self-test

The normal and optimized commands produce byte-identical JSON. There are no
`assert`-based checks: failed identities and guards raise explicit exceptions.
The self-tests deliberately introduce nonzero polynomial and rational residuals
and verify that rejection still occurs. All Python subprocesses used by external
replay/build tooling should carry `-B` to avoid bytecode-cache side effects.

## Files

- `exact_algebra.py`: custom sparse polynomials over `Fraction`, exact polynomial
  division/GCD, and reduced rational functions
- `formal_series.py`: rational formal power series, reciprocal, composition,
  exponential, Bernoulli numbers, the normalized recurrence, and Stirling product
- `verify_report231.py`: all certificate checks and independent finite counting
- `receipt.json`: deterministic receipt produced by this version of the sources

## What is checked

There are 31 symbolic residual checks, including denominator-cleared polynomial
identities in `n,u,v`; the lower, vertical, and horizontal triangle edges; the
nonsingular `n=1` certificate; each boundary integral; the triangle recurrence;
the affine count substitution; the normalized rational recurrence; all three
order-two elimination coefficients; and the factorial/rising-factorial identities
identifying the actual printed Conjecture 18. The optional `a_0=a_1=a_2=1`
extension has residual `-2160` at `n=0`, which is explicitly excluded.

The count is independently computed for every width 1 through 20 by a
legal-prefix dynamic program and by positive barycentric/Dirichlet integration.
The latter is also compared with the separately expanded signed polynomial for
`h(t)`. Finite-sum evaluations and both recurrences are cross-checked over the
available range. These finite tests are consistency checks, not the recurrence
proof.

Exact asymptotic coefficients of `b_n=a_n/((4n)!/(n!)^4)` are computed through
`n^-12`. The series inputs are independently cross-checked against reversed
polynomials from the already verified rational recurrence. Both general formal
composition and the independent binomial formula check the shift `n -> n+1`.
The Stirling exponential is checked by its differential identity. Six exact
relative correction coefficients for `a_n` are returned.

The accompanying manuscript supplies the transfer/Pfaffian argument and analytic
remainder bounds. This program verifies their stated algebraic consequences; it
does not infer a proof from finitely many counts or numerical asymptotics.
