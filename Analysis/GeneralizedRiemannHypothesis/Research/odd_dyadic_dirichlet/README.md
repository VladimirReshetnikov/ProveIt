# Odd dyadic filters at zeros of Dirichlet L-functions

The eight-page paper determines the exact sharp gain and both minimizing points for every odd number of dyadic filters from five onward. It identifies the three active exponents, calculates a parity-dependent asymptotic expansion, and proves a frequency law for near-extremal residues at the zeros of each fixed Dirichlet L-function. The character modulo one gives the Riemann zeta case.

## Contents

- **odd_dyadic.pdf** and **odd_dyadic.tex** are the paper and its editable source.
- **code/verify_finite.py** and **data/finite_certificate.txt** give the exact integer interval proof for the eight small cases. The paper proves every odd case from 21 onward analytically.
- **figures/dyadic_contacts.pdf** is the vector figure included by LaTeX.
- **code/illustrate.py** generates the figure and **data/odd_constants.csv**. The CSV tabulates the minimizers, gains, angles, and frequency coefficients for odd indices from 3 through 81. Its decimals are high-precision approximations. The known three-filter case is included for comparison.

## Reproduction

From this directory, the following commands reproduce the certificate, regenerate the illustration and data, and build the paper.

~~~sh
python3 code/verify_finite.py > finite_run.txt
diff -u data/finite_certificate.txt finite_run.txt
python3 code/illustrate.py
pdflatex -interaction=nonstopmode -halt-on-error odd_dyadic.tex
pdflatex -interaction=nonstopmode -halt-on-error odd_dyadic.tex
~~~

The finite verifier uses only Python 3 and its standard library. The optional illustration requires mpmath, NumPy and Matplotlib. The supplied vector figure suffices to compile the paper without Python. A LaTeX installation with Latin Modern, AMS packages, geometry, booktabs, graphicx, xcolor, fancyhdr and hyperref is sufficient.

## Predecessor

The problem and even case come from the report *Sharp constants for dyadic pole detection* in ProveIt, commit **b9a7c196e4aed3d93d4f222efef677a50efe912b**, at **Analysis/GeneralizedRiemannHypothesis/docs/incoming/dyadic_pole_detection_2026-11-26.zip**. SHA-256 of that source archive is **9713056b28bfd1c04fbe84f5864583d729de547e2a3026b98f4125e0fe474a1b**. The source report explicitly leaves the odd constants from five onward and their minimizers open.

The Dirichlet critical-line input is the published Lean development **lsernau/grh-lean** at **72fead102f663d5c7a407964a13dc0cf9d977207**. The final section of the paper identifies the exact claims used and the independent verification record. The new minimax and frequency theorems are proved in the paper. The included software checks the finite inequalities and reproduces numerical illustrations.
