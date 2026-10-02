# Recorded verification

The following checks passed on the delivered source:

1. Exact integer dynamic programming through n=20000. The first 54 A097356 terms
   and first 24 terms of each of A206226, A206227, and A206240 match the reference
   OEIS prefixes. Monotonicity was checked through n=20000.
2. Independent first-order coefficient formulas and Gaussian top-degree identities
   match the all-orders coefficient engine through P4 at high working precision.
3. Exact SymPy simplifications verify the rational d0/eta formulas and Q1/Q2 phase
   transforms. Output: `data/symbolic_checks.txt`.
4. Exact rational intervals enclose the unique saddle and certify the upper-envelope
   correction, negative pre-square correction, and opposite boundary signs at
   distances three and four. Output: `data/certified_signs.txt`.
5. Sampled shell, phase, boundary-defect and threshold-inverse comparisons were
   computed from exact partition counts. The outputs are in `data/`.
6. The PDF was compiled with pdflatex/latexmk, all LaTeX labels and references were
   checked, and the final log has no overfull boxes or undefined references.
   The 29-page PDF was rendered for inspection; the title page, mathematical
   layouts, table pages and references were visually checked.

## What these checks do not establish

Finite enumeration does not prove the asymptotic theorems. High-precision decimals
are not rigorous interval bounds unless explicitly identified as such. The rational
certificate checks sign inequalities, not the full saddle-point proof. The eventual
three-term classification and the uniform inverse error are conventional theorems
proved in the article, without a certified numerical starting threshold/error radius.
No Lean/Rocq verification, independent peer review, or bibliographic-priority
certification is claimed.
