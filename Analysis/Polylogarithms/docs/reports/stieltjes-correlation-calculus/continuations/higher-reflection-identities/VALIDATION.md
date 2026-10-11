# Validation record

Prepared 11 October 2026.

## Article and source build

- The final article has 32 pages, including the title, contents, analytic verification appendix, and references.
- The modular source was compiled with pdfLaTeX through latexmk.
- The standalone TeX was copied into an isolated directory containing no modular source files and compiled independently.
- The two final PDFs have identical extracted text.
- Both final TeX logs contain no unresolved references, LaTeX warnings, overfull boxes, or underfull boxes.
- Every page of the assembled article was rendered and visually inspected. The contents and references were adjusted to avoid orphan continuation pages, and the affected final pages were inspected again.

## Mathematical review

The completed beta–Hurwitz germ and the logarithmic-square/cubic cancellation received a separate analytic derivation and sign check. The centered-polynomial necessity proof, its algebraic-coefficient corollary, and the finite moment formula were reviewed from their formal and analytic arguments. The all-order Tornheim normal form and the short quartic difference were independently checked. The geometric theorem was proved through fixed-contour Hermite interpolation and checked against independent separated finite-part quadrature, including derivative pairs.

These are research checks within preparation of this report, not external refereeing or proof-assistant verification.

## Reproduction records

The delivered JSON files record completed runs of all five scripts. Their methods, working precisions, and asserted tolerances are documented in `verification/README.md`. In particular:

- The ordinary-constant beta cancellation agrees with independent endpoint-subtracted quadrature to an observed absolute discrepancy of about `1.25e-60`.
- The four quartic Tornheim ray comparisons have observed discrepancies below `8.2e-34`.
- The derivative-pair reflection comparisons have observed discrepancies below `6.4e-51`.
- The centered moment comparisons for indices 0 through 6 lie within the proved analytic tail-truncation envelopes; floating-point rounding has not been enclosed by intervals.
- The geometric limit records compare `C-T-Q` at positive gaps. Those quantities are genuine finite-separation remainders, not equality errors.

The analytic and exact-algebraic proofs establish the general results. Decimal agreement and finitely many symbolic checks are not substituted for those proofs.
