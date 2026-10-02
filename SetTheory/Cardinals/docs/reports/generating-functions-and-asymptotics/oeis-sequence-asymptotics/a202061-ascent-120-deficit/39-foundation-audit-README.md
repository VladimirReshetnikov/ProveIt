# Independent verification

`audit.md` reviews the six unchanged mathematical proof notes reproduced in
`../derivation/`. Its original source-directory reference records provenance;
all needed files are included in this package. Check the source hashes with:

    (cd ../derivation && sha256sum -c ../audit/source-sha256.txt)

`integrated-report-review.md` records the review of the standalone TeX report.
The independent scripts do not import the original implementation:

    python independent_checks.py
    python staircase_checks.py

The historical author-replay log includes an optional SciPy stationary-point
diagnostic. The packaged `../block_formula.py` omits that nonessential numerical
optimization and retains the exact binomial/operator comparison, so the release
requires only SymPy and mpmath. The package also adds a complete discriminant
coefficient check to the exact certificate. No proof claim depends on the
removed optimization.

High-precision tail and tilt outputs in the independent scripts are explicitly
numerical diagnostics. Exact field identities, rational intervals, finite
integer checks and the mathematical audit are identified separately.
