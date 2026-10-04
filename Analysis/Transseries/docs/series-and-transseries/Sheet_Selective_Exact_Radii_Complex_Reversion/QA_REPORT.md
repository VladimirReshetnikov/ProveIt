# Build and verification report

Final build and inspection: 4 October 2026.

## Compilation

- The final article has 25 A4 pages: a title page, one contents page, and
  23 numbered article/reference pages.
- It was compiled with pdfLaTeX in three passes by the included build script.
- The final pass reported no LaTeX warnings, undefined citations or references,
  multiply defined labels, duplicate destinations, or overfull/underfull boxes.
- The theorem, lemma, proposition, and corollary cross-reference types were
  checked after introducing shared-counter aliases.
- Font inspection found embedded Type 1 fonts and no Type 3 fonts.
- No standalone font files are part of the package.

## Rendering

- Every final PDF page was rendered with PyMuPDF and inspected in contact sheets.
- Selected title, critical-theorem, formula, example, table, and reference pages
  were also rendered at a larger scale for spot inspection.
- No clipped text, overlapping formulas, missing glyph boxes, or unreadable
  figure labels were observed.
- A programmatic text-boundary check found no text blocks crossing a page edge.
- Both PNG figures are embedded in the PDF and supplied as build dependencies.
- The final bibliography starts on its own page; the contents fits one page.

## Executed mathematical checks

`verify.py` passed all exact assertions:

1. Quadratic-phase inverse residual through amplitude degree 9.
2. General first three Puiseux coefficients through local degree 4.
3. Critical point and stationary critical-value expansion through parameter
   degree 2.
4. Logarithmic-core normalized log-unit expansion through inverse-core degree 3.
5. Exact rational Taylor lower bounds proving log(10)<2.303 and
   log(5000)<8.52, together with the rational comparison used to prove the
   greater-than-10^1081 foreign-sheet scale.

The numerical tests use 110 decimal digits. The recorded and freshly regenerated
verification JSON objects matched exactly. Both freshly generated figures also
matched the recorded PNG files byte-for-byte in the tested environment.
The exact environment is in `results/build_environment.json`.

## Limits of verification

The analytic proofs are ordinary mathematical arguments, not Lean proofs.
Finite symbolic tests do not prove the general theorems. The high-precision
numeric values, root calculations, and curve samples are not interval enclosures.
The rational inequalities for the coarse foreign-sheet scale are an explicit
exception: those small auxiliary checks use exact arithmetic.

The comparison with ProveIt was targeted, and no complete independent literature
priority search or peer review was performed. No external repository was altered.
