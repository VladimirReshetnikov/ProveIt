Sparse equations for Gaussian singular moduli
Trace congruences at the factorial threshold
27 November 2026

The paper proves an unconditional lower relative density bound of
0.9999969821615212 for full support at Gaussian prime conductors. It
settles the two conductors singled out by the ProveIt article and
certifies all 38,178 prime conductors below 456,193.

Files
  gaussian-singular-moduli.tex     standalone LaTeX source
  gaussian-singular-moduli.pdf     compiled paper
  check.py                        coefficient checks and conductor census
  density.py                      exact rational densities and tail bounds
  verification.txt                expected output of the default checks
  SHA256SUMS                      hashes of all other files

Rebuild the paper in a standard TeX Live installation with pdfLaTeX:
  pdflatex -interaction=nonstopmode -halt-on-error gaussian-singular-moduli.tex
  pdflatex -interaction=nonstopmode -halt-on-error gaussian-singular-moduli.tex

Reproduce the checks with CPython 3.9 or later and its standard library:
  python3 check.py
  python3 density.py

For the exact numerator and denominator of each density endpoint:
  python3 density.py --fractions

The two default checks were run for this release. They use no network,
third-party packages, stored class polynomials, or numerical approximations.
The finite verification concerns coefficients, residue classes, and interval
tests. Arbitrarily large polynomial exponents are covered by the proof.

Repository version used
  https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/Article/sections/smd.tex
