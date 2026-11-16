# Validation code

Run from the archive root:

```sh
python3 code/validate_finite.py --output evidence/validation.json --dps 100
```

The exact layer uses only `int`, `math`, and `fractions.Fraction`.  It checks:

- rising-factorial splitting and termination;
- the hypergeometric coefficient ratio, formal derivative, and ODE residual;
- Euler and Pfaff transformations coefficientwise;
- Chu–Vandermonde;
- five contiguous relations and the Gauss difference chain;
- the cubic radical/Fuss–Catalan coefficients and truncated cubic equation;
- the general Glasser coefficient identity for several `k`;
- the Legendre polynomial specialization.

The optional numerical layer uses `mpmath` to audit MathWorld equations
(18)–(24) and a sample Euler transformation at high precision.  These
numerical comparisons are regression tests only.  They are not proofs of the
isolated special values, which remain status D in the report.
