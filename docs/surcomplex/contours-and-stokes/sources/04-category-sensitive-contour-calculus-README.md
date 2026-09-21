# Jordan Separation, Cauchy Theory, and Stokes Formulae on the Surcomplex Plane

A Category-Sensitive Contour Calculus — September 21, 2026.

## Files

- `surcomplex_contours.pdf`: the complete article.
- `surcomplex_contours.tex`: editable, self-contained LaTeX source, with bibliography.
- `verify_examples.py`: exact symbolic checks of the worked examples.
- `verification.txt`: output of the recorded successful check run.

## Scope and provenance

The article builds on the two supplied manuscripts `surcomplex_analysis(3).tex`
and `surcomplex_analytic_geometry.tex`, and on the published sources cited in the
bibliography. It distinguishes their imported results from deductions proved in
this article. The separating-torus theorem in Section 8 explicitly depends on
the supplied finite-algebra deformation and support-controlled normal-form
theorems, as well as classical local residue transformation.

The article does not assert an unrestricted contour integration theory in the
full fine topology, an exhaustive novelty certification, or a formally verified
proof of its general theorems. The symbolic checks validate examples only.

## Build

A standard TeX Live installation is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_contours.tex
```

Alternatively run `pdflatex surcomplex_contours.tex` twice. No separate BibTeX
file or external figures are needed.

## Exact example checks

Python 3.10 or later and SymPy are required:

```sh
python -m pip install sympy
python verify_examples.py
```

The recorded run passes 167 exact symbolic checks, including agreement of two
residue computations on 121 monomials. No arbitrary Hahn-field evaluator or
external service is used by the script.
