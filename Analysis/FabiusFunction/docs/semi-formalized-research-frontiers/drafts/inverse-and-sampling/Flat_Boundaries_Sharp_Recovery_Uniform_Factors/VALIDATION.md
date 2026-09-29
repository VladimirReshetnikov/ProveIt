# Validation record

## Mathematical status

Full conventional proofs are in `article.tex`. They have not been independently
peer reviewed or checked in Lean/Rocq. Finite tests are supplementary checks,
not proofs of the general theorems.

The main analytic dependencies were separately checked during construction:

1. Finite uniform sums have exact polynomial endpoint densities.
2. Conditional Jensen contracts weighted derivative-score moments.
3. A fixed long prefix supplies a uniform score moment of order q > 2;
   this gives convergence, not merely a one-sided bound, for J_r(f_N).
4. In the finite Hellinger lemma, M > 2r makes the endpoint majorant
   integrable. Conditioning at radius h^(-epsilon) handles all-moment
   perturbations without assuming exponential tails.
5. Fatou provides the infinite-law lower bound; common-convolution
   contraction and the convergent prefix information provide the matching
   upper bound.
6. Support leakage is superpolynomially small but nonzero; chi-square
   relative to the unsmoothed law can be infinite and is not used.
7. The unknown-variance lower-bound pair has one variance exactly zero and
   both parameter vectors converge to the all-zero boundary.
8. The finite-prefix phase diagram is stated for fixed symmetric all-moment
   perturbations with a first unmatched even moment, not arbitrary kernels
   with unspecified tails.

## Executed exact checks

Runtime: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0.

- 2,100 rational shifted-power inverse-bound checks: passed.
- 16 exact Lagrange/Vandermonde tangent checks: passed.
- First six uniform cumulant identities: passed.
- Explicit two-factor moment matches and variance compensation: passed.
- Hellinger constants 1/144, 1/129600, 1/192, and 7/829440: passed.

Full output: `verification_results.json`.

## Executed numerical diagnostics

- 60-decimal arithmetic.
- 20 Hellinger integrals for one, three, four, and five equal-width
  background uniforms; added uniform widths from 1/8 down to 1/128.
- Piecewise integration split at the spline knots and their shifted copies.
- One-uniform Hellinger distance checked against its exact closed form.
- Three-uniform endpoint-profile integral and five-uniform J_2 integral
  independently evaluated for comparison.
- Four-uniform logarithmic slope approaches the predicted 1/192.

Numerical integration is NOT interval-certified. The reported many-digit
values are numerical diagnostics, not rigorous numerical enclosures. No
numerical J_r(up) value, simulated minimax risk, or computational proof of
an asymptotic theorem is claimed.

Full data: `data/hellinger_diagnostics.csv`.

## PDF build and inspection

- Compiled with pdfLaTeX; three final successful halt-on-error passes.
- Final output: 21 A4 pages, including title and contents.
- Final log: no undefined citations/references, missing-character warnings,
  overfull boxes, underfull boxes, or duplicate-destination warnings.
- All 21 pages rendered to images and inspected in page montages.
- Main theorem, boundary theorem, and numerical-table pages additionally
  inspected at individual-page resolution.
- Programmatic PDF check found no text spans outside the page rectangles.
- Fonts are embedded in the PDF. No standalone font files are distributed.

Rendered images and TeX build intermediates are working files and are not
included in the delivery archive. The source can regenerate the PDF using
the provided build command.
