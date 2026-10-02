# Exact enumeration and complete asymptotics for A113226

This package contains the full research report, editable LaTeX source, exact integer data through n=1000, an executable finite-order asymptotic generator, validation code, and mathematical/source review records.

## Results

A closed exponential generating function proves the exponential and stretched-exponential forms of Bevan–Cheon–Kitaev Conjectures 13 and 14. The report identifies the exact amplitude and exponent, gives a full Poincare expansion in powers of n^(-1/3), supplies four explicit corrections, relates the logarithmic derivative to the known A136127 sequence, and gives controlled Lambert-W inverse expansions.

The known combinatorial model, bijections, cumulant sequence, and its prior leading asymptotic are credited. The literature search is scoped. No complete exponentially small transseries, convergence, canonical analytic interpolation, or certified finite-n error constants are claimed.

## Read first

- `a113226-asymptotics.pdf`: polished full report
- `a113226-asymptotics.tex`: editable source
- `proof.md`: mathematical proof revision pinned by the separate review
- `root-mathematical-review.md`: proof review and its exact scope
- `root-prior-art-check.md`: source and known-transform verification

The review is not conventional external peer review or machine-checked formal verification. Its independent coefficient check uses separately hand-expanded Gaussian perturbations and does not import the main generator.

## Reproduce

Python 3.11 or newer with the pinned packages in `requirements.txt` is sufficient. No network access is needed after dependencies have been installed.

Run the quick reproducibility check:

    bash replay.sh

It regenerates the asymptotic coefficient, independent coefficient-audit, and numerical validation JSON files. It also regenerates exact counts through n=100, checks them against the released n=1000 data, independently checks insertion enumeration through n=40, and performs brute permutation enumeration through n=8. It deliberately does not rerun the entire n=1000 calculation.

For the full exact data and the original larger insertion check:

    python3 exact_recurrence.py --n 1000 --check-n 65 --brute-n 8

This overwrites `exact_values.json` deterministically. Integer arithmetic is exact. The claimed O(N^2) complexity counts arithmetic operations, not bit operations.

For any requested finite algebraic order:

    python3 asymptotic_coefficients.py --order 6 --dps 70

This implements the general formula, rather than extrapolating a fixed list. Larger orders can have substantial symbolic resource cost. This command overwrites `asymptotic_coefficients.json`; the released/default table is order 4. Restore it with the default replay if byte comparison with the release is desired. Decimal evaluations use high precision but are not interval certified.

To rebuild the PDF using a standard pdfLaTeX installation with AMS, geometry, booktabs and hyperref:

    bash build.sh

The script includes an optional compatibility branch for the original execution environment. On an ordinary complete TeX Live installation, the standard branch is used. PDF metadata timestamps may differ after rebuilding; exact byte reproduction is required for mathematical JSON outputs, not for a fresh PDF build.

## Files and verification

- `exact_recurrence.py`, `exact_values.json`: cumulant/EGF recurrence and complete exact data
- `asymptotic_coefficients.py`, `asymptotic_coefficients.json`: arbitrary finite-order symbolic Gaussian expansion
- `validate_asymptotics.py`, `validation.json`: scaled residual and inverse comparisons
- `root_coefficient_audit.py`, `root_coefficient_audit.json`: separate first-two-coefficient calculation
- `manifest.json`: SHA-256 integrity hashes of the packaged files
- `quality_checks.json`, `short_replay.log`: release checks

The exact data agree with all 21 terms displayed in OEIS, the published insertion rules through n=65, and brute avoidance through n=8. The report's integer-threshold result is a ceiling envelope when a valid error bound is available, not unconditional rounding of a truncated inverse.
