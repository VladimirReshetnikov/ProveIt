# Vector and Tensor Fields over the Surreal Numbers

An n-dimensional framework for admissible calculus, differential geometry,
and multiscale field equations. Prepared September 22, 2026.

## Contents

- `article.pdf`: the compiled 31-page article.
- `article.tex`: the complete, self-contained LaTeX source, including references.
- `code/verify.py`: exact finite symbolic and rational-arithmetic checks.
- `data/verification.txt`: the recorded successful verification output.
- `Makefile`: optional build, check, and clean targets.

## Mathematical scope

The article separates finite tensor algebra over a set-sized real closed
surreal field, smooth Hahn-valued fields on real manifolds, and intrinsic
surreal-coordinate geometry. Its principal bridge is multivariable smooth
Taylor--Hahn prolongation. It develops vector fields and arbitrary finite
rank tensors, coordinate changes, exterior calculus, admissible metrics,
Levi--Civita connections, curvature, Hodge duality, integration, compact de
Rham base change, standard-part reduction, near-real flows, and nonlinear
Hahn lifting from an invertible real linearization.

The support and function-class hypotheses are part of the statements. In
particular, an arbitrary map into the surreal numbers is not thereby a
smooth field, and pointwise metric invertibility does not ensure an inverse
in the selected smooth coefficient algebra. The article includes explicit
examples illustrating these distinctions.

## Build the PDF

Use a standard TeX Live or MiKTeX installation with pdfLaTeX. No font files,
images, external bibliography files, or network downloads are needed by the
source. Required packages are listed in the source preamble; they are common
LaTeX mathematics and layout packages, including Latin Modern, AMS packages,
mathtools, mathrsfs, microtype, geometry, booktabs, longtable, fancyhdr,
xurl, hyperref, and cleveref.

From this directory run:

```sh
pdflatex -halt-on-error -interaction=nonstopmode article.tex
pdflatex -halt-on-error -interaction=nonstopmode article.tex
pdflatex -halt-on-error -interaction=nonstopmode article.tex
```

Alternatively, run `make pdf`. The shipped PDF was built successfully with
no undefined references, missing citations, or overfull boxes in the final
LaTeX log. Its pages were rendered and visually inspected.

## Reproduce the finite checks

Python 3.10 or later and SymPy are required. The recorded run used Python
3.13.5 and SymPy 1.14.0. From this directory run:

```sh
python3 code/verify.py
```

The script uses exact symbolic expressions and rational Fourier coefficients.
All seven check groups passed, totaling 5,533 exact assertions. Most of those
assertions enumerate Hodge-star signs. The tests cover specific finite
identities, not arbitrary infinite supports or all possible fields.

These checks are not a Lean formalization or a proof of the infinite-support
and existence theorems. The article supplies mathematical arguments and
identifies its imported results separately. Neither finite computation nor
successful typesetting is presented as a substitute for those arguments.

## Repository relationship

The targeted read-only repository review was pinned to:

```text
VladimirReshetnikov/Surreal
d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0
```

Appendix B identifies the material reviewed and the limits of that inspection.
No repository files were changed and no Lean build was performed. The
bibliography distinguishes repository drafts, published sources, and recent
preprints. No exhaustive novelty or priority claim is made.
