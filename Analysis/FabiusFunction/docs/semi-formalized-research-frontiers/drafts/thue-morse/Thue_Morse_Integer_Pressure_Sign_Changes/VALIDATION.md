# Validation

Date: 1 October 2026

## Analytic proof
The finite Fourier matrix and the zero-weight Perron argument were checked directly against the pinned source. The complex column-norm bound, harmonic Fourier coefficient estimate, positive-axis continuation, Pringsheim argument, equal sign radii, primitive imaginary-axis continuation and tensor-product modulo-four argument were checked by direct derivation. The final written theorem preserves these hypotheses.

## Exact arithmetic
- 19 orders: every m=2,...,20
- 2090 positive-order Fourier response equations checked exactly in the production recurrence
- 1064 stored pressure coefficients independently recomputed from the stored normalized eigenvalue, tangent differential equation and full formal logarithm
- 105 coefficients for m=2,...,6 independently reconstructed from the characteristic polynomial of the original phase matrix
- The independent characteristic checker also ran under python -O; it uses explicit exceptions rather than removable assertions
- A fresh replay at m=20 matched all eigenvalue/pressure coefficients and all 200 exact Fourier residuals
- The m=2 degree 12 coefficient is exactly -35360872/93555

The proof of infinitely many signs uses no finite numerical extrapolation. Finite computations certify only the displayed first-negative table.

## Document QA
The seven-page PDF was built with three LaTeX passes. Every page was rendered and visually inspected. The compiler log contains no overfull or underfull boxes and no warnings. All PDF fonts are embedded, and text extraction was checked.

The manuscript is ordinary mathematics with exact finite arithmetic, not an external referee report or formal proof.

