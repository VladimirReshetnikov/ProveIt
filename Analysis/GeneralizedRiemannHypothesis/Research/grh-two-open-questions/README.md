# Two open questions from the ProveIt GRH article

The two papers begin with explicit questions in the same repository snapshot. They can be read independently.

## Four-point prime variances

Read `zero-stencils/zero-stencils.pdf` for the result about zeta zeros. It classifies four equally spaced observations of the smoothed prime error and identifies the first exceptional filter. For an exceptional filter with a limiting variance, the paper determines the form of every subsequential limit of the squared-multiplicity measure. It also gives a discrete model attaining the possible ambiguity while preserving the ordinary zero-counting main terms.

The result for positive spectral measures is unconditional. The identification of the actual prime variance uses the repository's Riemann hypothesis input. The convergence of the squared-multiplicity count for the zeta function itself is an open question.

From within `zero-stencils/`, run `python3 verify_stencils.py` to reproduce `checks.txt`. The script uses mpmath (tested with version 1.3.0) for interval arithmetic. The TeX source includes `first-resonance.tex`.

## Symplectic compressions

Read `symplectic/symplectic.pdf` for the unconditional finite-field theorem. For any two nondegenerate frame sizes, it gives the exact optimal test for a symplectic block against a uniform matrix and the limiting distance for every offset from complementary dimension. It includes a recurrence for the exact finite probability.

From within `symplectic/`, run `python3 distance.py 2 6 4 10` to calculate the distance over the field of order 2 for a 6 by 4 block in ambient dimension 10. The result is 1120959/8634368. Run `python3 verify.py` to reproduce `verification.json` by counting row pairs. This verifier uses the Python standard library.

## Source snapshot and reproducibility

The pinned ProveIt commit is `35e2a5a634924e57ac6b77bd73a28570dd1a362b`. The relevant files in `Analysis/GeneralizedRiemannHypothesis/Article/sections/` are `zer.tex`, `spn.tex`, and `src.tex`. Both papers cite the exact source statements, distinguish them from the extensions, and give references to related earlier work. The upstream Lean development was treated as a cited input. Neither paper is a Lean formalization.

- [Project at the pinned revision](https://github.com/VladimirReshetnikov/ProveIt/tree/35e2a5a634924e57ac6b77bd73a28570dd1a362b/Analysis/GeneralizedRiemannHypothesis)
- [Prime variances and inverse theorems](https://github.com/VladimirReshetnikov/ProveIt/blob/35e2a5a634924e57ac6b77bd73a28570dd1a362b/Analysis/GeneralizedRiemannHypothesis/Article/sections/zer.tex)
- [Finite frames and matrix compressions](https://github.com/VladimirReshetnikov/ProveIt/blob/35e2a5a634924e57ac6b77bd73a28570dd1a362b/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex)

To rebuild either paper, enter its directory and run `pdflatex` twice on the main TeX file with the same name as the PDF. A standard TeX Live installation supplies the packages. All included source files must be kept together within their respective directories.
