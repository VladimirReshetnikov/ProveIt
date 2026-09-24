# Elliptic addition and Jacobi continued fractions

Research report, 19 September 2026.

## Result and scope

`article.pdf` is the complete mathematical report; `article.tex` is its editable
LaTeX source. The main theorem proves a consistently indexed, non-torsion version
of Paul Barry's 2023 Conjecture 4, and derives the corresponding coordinate
formulas of Conjecture 3. The proof gives an explicit expression for every
continued-fraction tail and shows that removing one layer equals elliptic
translation. It is not an inference from the computational tests.

The related Somos-4 and division-polynomial identities were already proved by
Liu, Wang, and Zhang in August 2026. They are recovered here, not claimed as new.
Broader elliptic-curve/continued-fraction theory is also established literature.
The literature audit does not certify that this is the first proof of the
corrected conjecture. No proof-assistant formalization or peer review is claimed.

Main hypotheses: a field of characteristic zero; the curve
`Y^2+aXY+bY = X^3+cX^2+dX` is nonsingular; `b != 0`; and `P=(0,0)` has infinite
order. The ordinary infinite regular Jacobi fraction needs the last hypothesis.
The algebraic generating function and the polynomial Hankel identity survive
specialization to torsion; the ordinary regular fraction does not. Explicit
order-three and order-four examples demonstrate the distinction.

## Contents

- `article.tex`, `article.pdf`: proof, examples, literature discussion, appendices.
- `verify.py`: exact verification using only Python's standard library.
- `verify_symbolic.py`: optional symbolic audit with SymPy.
- `verification.log`, `symbolic_verification.log`: output of the delivered runs.
- `data/verification.json`, `data/symbolic_verification.json`: machine-readable results.
- `data/*_moments.csv`: q_n and mu_n through index 40, for four named curves.
- `data/*_hankels.csv`: Hankel, modified Hankel, and normalized values through index 12.
- `data/*_points.csv`: elliptic points through 12P, with exceptional values marked.
- `LITERATURE_AUDIT.md`: exact source versions and the boundary of the priority claim.
- `requirements-symbolic.txt`: optional symbolic dependency.
- `Makefile`: verification and PDF build commands.

The four examples are `barry`, `infinite_order`, `order_three`, and `order_four`.
All CSV fractions are exact, not decimal approximations. In point CSVs, the
alpha_m/beta_m coordinate formulas apply only for m >= 2 and nonzero X_m.
The exceptional outer values are alpha_0=1, alpha_1=-1, beta_1=1.

## Reproduce the computations

Use Python 3.10 or newer. Run with assertions enabled (do not use `python -O`).
No network access or third-party package is needed for the principal audit.

```sh
python verify.py --output data
```

The default grid has 108 integer parameter choices; two singular curves are
skipped for the group-law tests. The delivered run checked 106 nonsingular
curves, 544 nondegenerate layers through m=8, the Hankel/division identity through
n=9 on every curve, four longer example tables, and 84 finite Catalan-sum
checks. All passed. The finite tests include torsion cases and stop regular
series stripping at a zero coefficient without claiming termination.

For optional symbolic verification (tested with SymPy 1.14.0):

```sh
python -m pip install -r requirements-symbolic.txt
python verify_symbolic.py
```

Sixteen polynomial/rational-function checks passed. This script writes its
summary to `data/symbolic_verification.json`.

The written proof also contains the nonvanishing, formal-limit, and generic
specialization arguments that finite computation alone cannot establish.

## Compile the article

A TeX distribution with the packages named in `article.tex` is required,
including newtx, amsmath, amsthm, tcolorbox, hyperref, and cleveref. All text and
bibliography entries are in the source; there are no external figures or .bib
files to retrieve. The supplied PDF was compiled and visually inspected.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The third run resolves pagination changes caused by inserting the contents.
Equivalent targets are `make pdf`, `make verify`, and `make symbolic`.
`make clean` removes only generated LaTeX auxiliary files, not the report or data.

The archive contains no external copyrighted paper PDFs, no installed font
files, no checksum files, and no LaTeX build intermediates.
