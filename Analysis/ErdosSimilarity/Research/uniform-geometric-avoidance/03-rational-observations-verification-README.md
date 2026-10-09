# Exact verification and its limits

Run `python3 verify_recurrence.py` from this directory, or run the script by its absolute or package-relative path. It writes `results.json` next to the script and exits unsuccessfully if a required assertion fails. Only Python's standard library is required.

The recorded run passes **3,380 exact assertions** for three normalized numerator recurrences:

1. `2^(-n) cos(n*pi/2)`, with infinitely many exact zero terms.
2. The real part of `(1/2 + 3i/8)(3/10 + 2i/5)^n`, with rational real state and metric data.
3. `(1/2)(n+1)2^(-n) cos(n*pi/2)`, with repeated complex roots and an exactly solved Lyapunov equation.

All three use the auxiliary denominator perturbation `(1/4)(-1/2)^n`. Its one-dimensional realization is checked against the same alpha, beta, and K bounds as its numerator.

The checks cover positive semidefiniteness via exact principal minors, both quadratic contraction bounds, independent scalar formulas, original-term identities for state coordinates, first-passage thresholds, coordinate ties, denominator bounds, signed envelopes, pairwise separation, and strictly increasing selected original indices. Sixteen samples lie exactly on an energy threshold, so equality is exercised. Quotient boundary tests are checked after positive-denominator clearing, including zero signs.

`results.json` records rational matrices, metrics, initial states, constants, selected indices, exact values, and assertion counts by category. The figure generator reads this output and redraws the plots. All decisions in the verifier are exact; the plots and decimal displays are illustrative.

These are finite algebraic and implementation checks. The all-parameter theorem depends on the written proofs of the polynomial sign bound, conditional routing calculation, compact residual repair, and summable global construction. The package contains no implementation of the complete random routing tree or real quantifier-elimination blocker search, and no Lean or other proof-assistant certificate. See `PROOF_AUDIT.md` for the internal proof audit.
