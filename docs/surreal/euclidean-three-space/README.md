# Analytic Geometry and Trigonometry in Surreal Three-Space

A 34-page mathematical article, prepared September 22, 2026, in relation to
VladimirReshetnikov/Surreal. The repository sources inspected are pinned to
commit d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0; the article contains a
bibliography and source ledger. No repository files were modified.

## Files

- `surreal_three_space.tex`: self-contained LaTeX source, with bibliography.
- `surreal_three_space.pdf`: compiled article with linked contents and references.
- `verify_identities.py`: exact symbolic checks for selected displayed identities.
- `verification.txt`: actual check output; all 19 test groups passed.
- `requirements.txt`: the SymPy version used for the checks.

## Scope

The article develops spatial affine geometry, projections, quadrics, rotations,
quaternions, screw motions, finite-angle trigonometry, spherical triangle laws,
polar duality, reconstruction and exceptional SSA families, spherical centers,
Ceva, branch-correct solid angles, finite-polygon area, curvature, parallel
transport, holonomy, and multiscale degeneration estimates.

It localizes surreal coordinates to set-sized real-closed Hahn fields and makes
the required analytic structure explicit. Areas and lengths may have arbitrary
surreal scale. Geometric directions use canonical finite angles. A uniform
relative area estimate also handles arbitrarily thin infinitesimal triangles.

The development does not assert an unrestricted integration or measure theory,
a general surreal arithmetic implementation, or completed Lean formalization.
The symbolic tests check finite algebra and formal coefficients, not every proof
or any of the imported foundational theorems. No mathematical priority claim is
made.

## Build the PDF

With a reasonably complete TeX Live or MiKTeX installation:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_three_space.tex
```

Alternatively, run the following command three times to settle the contents,
page references, and citations:

```text
pdflatex -interaction=nonstopmode -halt-on-error surreal_three_space.tex
```

No external figures, font files, BibTeX database, or shell escape are required.
The delivered PDF was compiled with pdfTeX 1.40.26. Its rendered pages were
inspected, and the final compilation has no unresolved references or overfull
boxes.

## Run the selected symbolic checks

```text
python -m pip install -r requirements.txt
python verify_identities.py
```

The recorded run used Python 3.13.5 and SymPy 1.14.0. The script returns a
nonzero exit code if any test group fails. Positivity, domain restrictions,
branch selection, strong summability, and model-theoretic transfer still rely
on the mathematical arguments in the article; they are not inferred merely
from a zero symbolic residual.
