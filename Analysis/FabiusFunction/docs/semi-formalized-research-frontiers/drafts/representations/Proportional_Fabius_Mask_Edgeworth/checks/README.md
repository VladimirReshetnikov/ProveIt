# Reproducible numerical checks

Run:

```sh
python check_proportional_tv.py --output numerical_results.json
```

Dependencies: Python 3, NumPy, and SciPy. The result JSON records the versions used.

The script evaluates two exactly specified finite-dimensional distribution families:

1. The untruncated Gamma/Beta model, at hidden fractions 0.3, 0.5, and 0.8 and sizes 200, 1,000, 5,000, and 10,000. This checks the universal correction and records the crossing midpoint shift.
2. A single cap of size 2 among otherwise untruncated exponentials, separately placing the capped coordinate in the hidden and observed blocks, at the same three hidden fractions and sizes 1,000, 5,000, and 10,000. This checks both variance-defect coefficients and cancellation of the mean defect.

The finite-n formulas use Gamma and Beta CDFs and likelihood roots. The script uses log1p/expm1 for the cap correction. The saved JSON includes all TV values, predicted coefficients, scaled differences, coefficient errors, crossing locations, root residuals, and nine regression-check outcomes.

Scope: these are floating-point regression checks. They use neither arbitrary precision nor interval arithmetic, and the finite tolerance thresholds are not rigorous asymptotic bounds. In particular, the computations do not establish the uniform remainder theorem. Small differences in final digits across supported NumPy/SciPy versions are expected. The analytic proof and its review remain the evidence for the theorem.
