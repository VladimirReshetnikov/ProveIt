# Verification record

Prepared for the 28 September 2026 manuscript.

## Mathematical review

The full analytic argument is conventional mathematics. Its assumptions and
parameter ranges were checked during preparation, but it has not been
independently peer-reviewed or formalized in Lean.

The proof review specifically checked the following interfaces:

- variance normalization and the finite-prefix cumulant parameter rho=q^(2m);
- the existence of a block of order 1/epsilon comparable coefficients;
- polynomially weighted high-frequency Fourier integrability;
- the exact-variance moment-generating-function inequality;
- preservation of unimodality under uniform convolution and the infinite limit;
- the Gaussian polynomial envelope, including zeros outside compact support;
- use of a deeper absolute density expansion before dividing by the Gaussian;
- integrated polynomial errors, avoiding unproved logarithm-free remainders;
- continuous and uniform treatment of Renyi order alpha=1;
- the distinction between an asymptotic series and a convergent series;
- the finite-prefix range rho<=rho_0<1 and the separate unresolved rho->1 regime.

None of these analytic claims is inferred from the numerical table.

## Exact calculations

Executed successfully:

    python code/coefficients.py --order 8 --output data
    python code/test_exact.py

The coefficient run performs exact rational arithmetic. It verifies
normalization and unchanged variance for all constructed density polynomials;
checks the Shannon coefficients against the Renyi specialization at alpha=1;
checks zero polynomial coefficients at alpha=0; and checks the claimed degree
bound in alpha through order eight.

The independent regression file has four tests, all passing:

1. Minimal supported order and rejection of invalid orders.
2. Hermite product moments appearing in the quartic calculation.
3. Direct low-weight cumulant construction of the finite-prefix Shannon
   coefficients through degree four and Renyi coefficients through degree three.
4. The quartic infinite-prefix Renyi polynomial.

The low-order finite-prefix check does not use the coefficient generator's
exponential recurrence. The recorded output is in data/test_results.txt.
The check at alpha=0 concerns the formal power coefficients; the actual
order-zero divergence is positive and exponentially small, as the article proves.

## Floating-point diagnostics

Executed successfully:

    python code/numerics.py --output data
    python code/plots.py

Two runs use 2^17 and 2^18 spatial points, with 4096 and 8192 Fourier modes.
Ratios checked: 0.80, 0.85, 0.90, 0.93, 0.95, 0.97, 0.98, 0.99.

Largest absolute grid/spectral change in the entropy diagnostic:
approximately 2.12e-15.
Largest clipped negative mass: approximately 2.234e-15.
Largest variance discrepancy: approximately 1.188e-12.

The calculations use a quadratic replacement for a very small sinc-product
tail, ordinary floating-point FFTs, clipping, and a bounded integration window.
They are NOT certified error enclosures. Common systematic errors could survive
grid refinement. Figures suppress residuals below 1e-13 rather than interpret
those values as an asymptotic rate measurement.

## Tested environment

Python 3.13.5
SymPy 1.14.0
NumPy 2.3.5
SciPy 1.17.0
Matplotlib 3.10.8
pdfTeX 1.40.26

## Publication checks

The complete source compiled with latexmk and halt-on-error enabled.
The final PDF has 20 A4 pages, zero rotation, and extractable nonblank text
on every page. The final log has no overfull boxes, undefined references,
undefined citations, or outstanding cross-reference rerun requests.

All 20 pages were rendered at 120 dpi. An all-page contact sheet was inspected;
the title page, nonlinear-transfer proof page, figure page, and final
bibliography page were also inspected at full rendered size. Final renders
were pixel-identical to the inspected renders after the calculation replay.
All reported font rows are embedded and subset; no Type 3 font was reported.
No standalone font files are included in the archive.

These publication checks do not establish mathematical correctness. Likewise,
the exact symbolic tests do not establish the analytic remainder theorem.

## Not performed

No Lean build, external theorem-prover check, independent peer review, interval
entropy enclosure, or exhaustive publication-priority search was performed.
No source repository file was changed.
