# Completed validation

Date: October 1, 2026.

## Numerical and exact checks

The final driver run completed with Python 3.13.5 and mpmath 1.3.0:

    python verify.py --max-m 256 --output results

It generated all A097356 counts through N=66048 using exact integers,
matched the first 54 A097356 terms and first 17 A206226 terms to the
inspected OEIS entries, and passed all 66048 adjacent monotonicity checks.
Nine evaluations of the closed D1 formula agreed with the independent
coefficient operator. The first inverse coefficients were also compared
with their closed formulas.

All exact rational assertions passed. In particular:

    -0.01618049251495 < kappa_3 < -0.01618049246590
     0.27622943999435 < kappa_4 <  0.27622944004564

The coefficient signs use the analytic series-tail bounds in Appendix A.
The contour proof and asymptotic remainder argument are written proofs,
not claims established by the numerical tests.

At m=256, the relative error of the square-subsequence approximation
through D4 was 1.6903752493862398e-15. This is a computed accuracy result,
not a universal numerical error bound for all m or all truncations.

## Source and PDF checks

The final PDF has 27 A4 pages. It was compiled repeatedly with pdflatex
until cross-references stabilized. The final log contained no undefined
references, undefined citations, overfull boxes, or underfull boxes.
All page layouts were reviewed in raster contact sheets, with individual
inspection of key theorem and reference pages; the bibliography was
reflowed to remove an otherwise nearly empty final page. The modified
final pages were rendered and inspected again.

All four Python source files passed Python byte-compilation checks.
The ZIP contains no build auxiliary files, cached bytecode, downloaded
third-party paper PDFs, or standalone font files.

## Remaining boundaries

No effective least m0 for the three-exception theorem is established.
No all-orders uniform inverse formula across switching layers is claimed.
No full exponentially improved or resurgent transseries is claimed.
No Lean/Coq formalization or global first-discovery priority is claimed.
