# Verification summary

The analytic argument was checked independently of its derivation. The integrated review covered the following points:

- The density normalization and the exact relation a_n = 4^n n! [u^n] f(u)
- The complete list of finite singular-value preimages in the disk needed for coefficient extraction
- Single-valued continuation in the slit disk and the cubic logarithmic multiplier
- The keyhole-contour and beta-integral proof of the fixed-order late-coefficient remainder
- The factor of three from sheet tracking, the physical median, the exact Stokes jump, and integrable growth of the lateral lips
- Both Lambert-function inverse expansions and their remainder scales
- The Rouché argument, Lagrange–Bürmann generator, all-fixed-sector remainder, inverse jump coefficients, and the distinction between the physical inverse and the lateral-inverse average

No fatal mathematical gap was identified. This is an analytic review, not a machine-formalized proof.

## Finite reproducibility checks

The exact replay verifies 22 displayed OEIS terms, matches 31 coefficients independently from the hypergeometric germ, generates terms through index 500, and compares the generated integer file with the retained baseline. A second numerical replay checks density integrals, Stokes-sector integrals, and the two inverse approximations. Explicit finite assertions check density relative errors below 10^-50, the four-term Stokes-integral error below N^-4 for the tested N >= 5, late-index inverse errors below 2/n^2, and original-moment inverse errors below 0.1/n^3. These conservative thresholds are finite sanity checks, not universal error bounds or interval certificates. The inverse-sector family in equations (36c-h) is covered by analytic review and is not numerically tested by these scripts.

The final PDF has 12 pages. All rendered pages were visually inspected, with no clipping, overlap, missing glyphs, or broken equations found. Its final three-pass LaTeX compilation produced no warnings or overfull boxes. The final checksums are in SHA256SUMS.

## Scope

Every inverse-power expansion is asserted for a fixed number of retained terms. The auxiliary-parameter inverse-sector series is convergent in the explicitly proved disk. The note does not classify all farther-sheet singularities or supply uniform growing-order, optimal-truncation, or Stokes-smoothing estimates.
