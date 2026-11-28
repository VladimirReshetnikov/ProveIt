# Choosing Selmer twists by cyclotomic interpolation

The nine-page paper gives two paper-proof replacements in the readable theta-lift proof of Dirichlet GRH and ordinary RH. The first is an interpolation theorem whose root-of-unity order bound is independent of the number of variables and the polynomial degrees at fixed total reference valuation. The second gives a missing-dimension bound of order b^(-4) within the existing translate budget. The paper traces both changes to the main inequality and the zero-free half-plane.

## Files

| File | Contents |
| --- | --- |
| theta_simplifications.pdf | Paper with clickable links into the pinned Lean sources |
| theta_simplifications.tex | Complete LaTeX source in one file |
| check_torsion_grid.py | Exact cyclotomic distance, interpolation, tensor-product and band examples |
| check_spanning.py | Exact rational rank and trace checks on all 256 subsets of a finite group, and the sharpness example |
| GreedyCoverAffine.lean | A Lean proof of the discrete affine recurrence after clearing denominators |
| sources.json and check_sources.py | Pinned Git blobs and a script to compare their bytes to an upstream checkout |
| verification.txt | Results and versions for the checks run on these files |

## Reading the argument

Pages 2–4 state and prove the uniform interpolation theorem. Page 5 applies it to every power of one character and extends it to bounded power series. Pages 6–7 give the rank estimate. Page 8 puts the two replacements back into the determinant proof. Page 9 links the results to the upstream declarations.

The interpolation argument and Hilbert-space estimates are paper proofs. The Lean file checks the mean-to-sequence iteration used on page 6. The unchanged baseline proof and its independent checks are linked in the paper. An integrated Lean port of the replacements has yet to be built.

## Reproduction

Run in this directory with Python 3.10 or later. The spanning check requires SymPy. The other Python checks use only the standard library.

~~~sh
python3 check_torsion_grid.py
python3 check_spanning.py
lean GreedyCoverAffine.lean
latexmk -pdf -halt-on-error theta_simplifications.tex
~~~

The separate Lean file uses only Std. It was checked with Lean 4.32.0. For the source manifest, point the checker at the root of an upstream lsernau/grh-lean checkout containing both grh and grh-compact.

~~~sh
python3 check_sources.py /path/to/grh-lean
~~~

The pinned revision is 72fead102f663d5c7a407964a13dc0cf9d977207. Its own full project uses Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
