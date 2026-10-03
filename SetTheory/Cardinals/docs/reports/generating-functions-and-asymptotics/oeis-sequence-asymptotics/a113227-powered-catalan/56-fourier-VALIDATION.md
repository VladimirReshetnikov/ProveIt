# Validation of the Fourier sector addendum

## Mathematics

The independent component cross-reviews and integrated review found no unresolved mathematical gap. See mathematical-verification.md for the precise scope and final source hash. The companion report and its prior audit are included.

## Numerical and symbolic checks

- Exact reciprocal-product/Stirling coefficients and Gaussian saddle coefficients through c_4 reproduced
- Seven exact-Bessel central saddle integrals evaluated with 70 decimal digits, including principal and complex modes
- All displayed 26-digit integral ratios agree under 160-to-192-node Gauss--Legendre refinement
- Nine complex-weight checks at moduli 200, 500, and 1000 and arguments 0, 0.4, and 1.2 radians reproduce the third coefficient with the expected shrinking error
- Exact recurrence counts at n=80,160,320 compared with exact-Bessel lattice sums at 180 digits; observed relative differences are approximately 1.83e−29, 1.81e−57, and 2.92e−115

These are non-certified diagnostics. The analytic proof, rather than the numerical tests, establishes the theorem and remainder scales.

## Document validation

The ten-page PDF was rendered and every page visually inspected. The final status and reference edits were re-rendered and inspected. No clipping, overlap, missing symbols, or overfull boxes were found. Its equations and prose preserve the reviewed mathematical source.

## Reproduction

A clean directory replay of bash run_checks.sh completed successfully. All numerical and symbolic outputs and the rebuilt PDF were byte-identical to the originals. The 27-file pre-replay baseline verified without a mismatch. Final source notes and this validation record were then added to the release manifest; no executable or mathematical source changed after replay.

The frozen ZIP was subsequently unpacked, its entire SHA-256 manifest verified, its quadrature consistency checks repeated, and its PDF rebuilt again. The final PDF remained byte-identical. Run bash run_checks.sh to repeat the full computation, or bash build.sh to rebuild only the PDF.
