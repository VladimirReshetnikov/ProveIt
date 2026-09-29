# Elliptic Equilibrium and Boundary-Corrected Transseries for Hyperbolic Fekete Designs

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `article.pdf`: the 26-page article.
- `article.tex`: editable LaTeX source, with bibliography included.
- `verify.py`: independent symbolic and numerical diagnostics.
- `verification/`: recorded JSON and CSV results plus the two figure PDFs.
- `verification.log`: complete recorded verification output.
- `PROVENANCE.md`: pinned repository source and literature provenance.
- `requirements.txt`: Python packages needed for reproducing the checks.

## Mathematical scope

The paper answers the equilibrium-measure and constant-potential portions of
`question:design-limit` in the repository's Common-Digit Fabius Zonoids report.
The exact elliptic-capacity structure is classical and is credited as such.
The finite-design analysis proves explicit bounds, bounded total gap defect,
a dimension-uniform dilute boundary correction, and a determinant transition
with three finite-size correction orders. It also develops convergent
capacity and bulk transseries and a certified inverse-capacity expansion.

The microscopic first-gap asymptotics for fixed interval length remain open.
The complete joint MacMahon / finite hyperbolic superfactorial crossover is
not claimed. No theorem in this package is represented as Lean-verified,
independently refereed, or established as a worldwide first result.

## Rebuild the article

Keep `verification/` beside `article.tex`. A standard TeX Live installation
with the packages named in the preamble is sufficient. No private macros,
external bibliography files, downloaded fonts, or network access are needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Reproduce the checks

Use Python 3.10 or later. The recorded run used Python 3.13.5, NumPy 2.3.5,
SciPy 1.17.0, mpmath 1.3.0, and SymPy 1.14.0. Install the dependencies in a
virtual environment, then run:

```sh
python -m pip install -r requirements.txt
python verify.py --output verification --figures > verification.log
```

Omit `--figures` to reproduce only the checks and data. All assertions passed
in the supplied run. Symbolic checks use exact rational arithmetic; selected
quadratures and small-dimensional optimizations use 80 decimal digits;
larger optimizations use double precision. Numerical diagnostics are not
interval-certified values or substitutes for the analytic proofs.

## Reading guide

Sections 3–5 give the continuum equilibrium and its transseries/inversion.
Sections 6–7 give finite certificates and exact product formulas.
Section 8 proves the dimension-uniform boundary theorem; Section 9 derives
the determinant transition. Section 10 records computations, Section 11
proposes ten research directions, and Section 12 separates formalization
obligations. Appendix A records provenance and Appendix B gives exact
coefficient tables.
