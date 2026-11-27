Identifying Dirichlet characters from short windows of zeros
27 November 2026

Read zero_windows.pdf for the complete theorem and proof. Theorem 1 gives
uniform local linear independence for any fixed number of primitive
characters. The first two corollaries identify sparse products and abelian
number fields. The matching bound allows zero occurrences to be omitted
or moved. All logarithms are natural, and all zero lists count multiplicity.

Files
  zero_windows.tex                Complete LaTeX source with linked references.
  zero_windows.pdf                Compiled paper.
  example/verify_quartic.py       Interval-arithmetic certificate for conjugate
                                  quartic characters of conductor 5.
  example/quartic-output.txt      Output reproduced during preparation.

Rebuild with a standard TeX Live installation:
  pdflatex -halt-on-error zero_windows.tex
  pdflatex -halt-on-error zero_windows.tex

Run the example with Python 3 and mpmath 1.3.0, assertions enabled:
  python3 example/verify_quartic.py

Inputs inspected
  lsernau/grh-lean
  revision 72fead102f663d5c7a407964a13dc0cf9d977207
  grh/src/Statements.lean and grh/src/Main.lean
  Independent verification: https://math.mit.edu/~drew/shortgrh/

  VladimirReshetnikov/ProveIt
  revision 1a50d416ba30b91595db12d7437f0328a32b0468
  Analysis/GeneralizedRiemannHypothesis/Article
  Principal comparisons: sections/src.tex, sections/rec.tex, sections/zer.tex

The general theorem is proved in the paper. The enclosure script verifies
the individual quartic example. The constants in the general recovery
height are not evaluated numerically.
