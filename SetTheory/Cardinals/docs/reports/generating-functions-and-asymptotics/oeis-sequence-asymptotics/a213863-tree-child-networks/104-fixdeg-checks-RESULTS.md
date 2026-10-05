# Exact-check result

Recorded UTC date: 2026-10-02

- Overall suite: PASS
- Normal Python baseline: PASS, 5,655 explicit verification gates
- Optimized (`-O`) Python baseline: PASS, 5,655 explicit verification gates
- Deliberate corruption cases: 25 distinct cases, each rejected in both modes
- Total deliberate corruptions rejected: 50 of 50
- Runtime: Python 3.12.14, SymPy 1.14.0

The machine-readable authority is `results/suite.json`, which identifies the verifier, runner and input manifest by SHA-256. Detailed baseline records are in `results/normal.json` and `results/optimized.json`; the complete console transcript is `results/replay.log`.

The checks cover d=2,...,12 through nine two-step rows; the exact startup; one-step and two-step recurrences; Gram factorization; the repaired contractive gauge; explicit failures of the naive gauge at d=6 and d=10; generic formal profiles through degree five; finite-product specializations for d=2,3,4,6,10; the first two universal endpoint coefficients; and an additional degree-six ternary certificate. The latter includes the exact gamma normalization and verifies the logarithmic n^-1 coefficient alpha^3/243-3/16.

All deliberate algebraic mutations update the temporary copy's input digest, so they must be rejected by mathematical verification rather than merely by integrity checking. Mutations also test duplicate keys, nonfinite JSON values, an unexpected field, boolean schema values, unsafe expression syntax, truncated coefficients and reduced startup coverage. Both source files were scanned for assertion statements before execution; none were present.

These are exact finite algebra and regression checks. They do not certify the analytic convergence argument or any numerical limiting amplitude. Those distinctions are stated in the report and package README.
