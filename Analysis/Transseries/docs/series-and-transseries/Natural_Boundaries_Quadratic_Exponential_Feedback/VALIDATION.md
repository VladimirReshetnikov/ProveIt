# Validation record

## Environment and executed commands

- Python: 3.13.5.
- mpmath: 1.3.0, configured to 120 decimal digits.
- LaTeX engine: pdfTeX 1.40.26.

Executed `python verify.py` with default exact order 16, followed by three
successful `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
passes. The recorded outputs are delivered with the article.

## Exact checks

The independent formal calculations agree through degree 16: forward fixed
point, two-sided compositional inversion, signed Lagrange-block coefficients,
and the literal formal kernel residual. Finite-action Taylor prefixes were
checked for cutoffs 1 through 8. The frequency ranges, uncancelled block masses,
Schroeder generating equation, contraction constants, derivative estimate,
and action-truncation constant were checked with rational arithmetic.

The exact contraction constant is 32/225, the image bound is 17/465,
the derivative bound is 3746/12405 < 1/3, and the action-truncation constant
is 7680/5983.

## Numerical diagnostics

The program evaluates the one-pole analytic-curve multiplier and a two-pole
oscillatory model at orders 10, 20, 40, and 80. The heat coefficients themselves
are rational and computed exactly; the logarithmic/complex normalizations use
120-digit arithmetic. Boundary inverse diagnostics use 96 actions, including
the rational point 2*pi*i/257.

These diagnostics are not interval certificates and are not used as proofs
of a natural boundary. The exact-function action-truncation bound does not
include the floating-point evaluation error.

## PDF checks

The final PDF has 23 A4 pages. It was rendered with the PDF skill renderer,
and all pages were inspected in contact sheets, with full-page inspection of
the title, mathematics/tables, and source/reference pages. The final changed
reference pages were re-rendered and inspected after the citation and layout
corrections.

The final LaTeX log has no errors, no undefined references or citations, and
no overfull boxes. One benign underfull-box warning remains in the abstract.
No clipped text, overlapping mathematical displays, or broken glyphs were
observed in the rendered pages. The PDF is not an accessibility-tagged PDF.

## Mathematical status

The proofs were developed and checked within this research session, but not
independently refereed or Lean-verified. The numerical and exact finite checks
do not establish the infinite analytic conclusions. The source includes a
proof-dependency audit and explicitly separates inherited results, proposed
new theorems, diagnostics, and further questions.
