# Exact Dynamics of a Three-Dimensional Keller Map

**Degree growth, Newton faces, shear spectra, and arithmetic escape**  
Prepared for Vladimir Reshetnikov, 30 September 2026.

The article studies the exact map in ProveIt's
`Algebra/JacobianConjecture` development, at reference commit
`a866ff9a2cdb9c5f436bb1d82ea5dca59dfee38d`.

## Results

The baseline iterate degrees satisfy
`d(0)=1`, `d(1)=7`, `d(n+2)=6*d(n+1)+d(n)`, giving first dynamical degree
`3+sqrt(10)`. Every positive weighted degree and the upper Newton geometry
of every iterate are computed. On the positive-weight wall, initial forms
are explicit monomials times powers of `xz+3y`.

For `T_h(x,y,z)=(x,y,z+y^2*h(x*y))`, a nonzero polynomial `h` of degree `m`
gives `F_h=F o T_h` with first dynamical degree
`(2*m+7+sqrt(4*m*m+32*m+61))/2`, outside characteristic three.
All these characteristic-zero maps are in one tame left-right equivalence
class and have generic degree three. Their first dynamical degrees are
unbounded. Characteristic three has a separate, completely proved phase law.

A monomial-dominance escape theorem gives precise logarithmic orbit
asymptotics and maximal arithmetic degree for a Zariski-dense set of integral
initial points. This does not assert that each such orbit is Zariski dense,
or that every rational point with a Zariski-dense orbit is covered.

## Contents

- `article.pdf`: the 23-page article.
- `article.tex`: self-contained LaTeX source with embedded bibliography.
- `code/verify_results.py`: thirteen groups of exact checks.
- `code/degrees.py`: integer-arithmetic degree calculator using proved formulas.
- `data/verification.json` and `data/verification.txt`: recorded verification.
- `data/calculator_checks.json`: independent comparison of the calculator with
  the matrix recurrences and characteristic-three formulas.
- `data/build_review.json`: compilation and rendered-page review record.
- `SOURCES.md`: source and attribution ledger, including retrieval limits.
- `STATUS.md`: exact claim and verification boundaries.
- `requirements.txt`, `Makefile`, `SHA256SUMS`: reproduction and integrity files.

## Reproduce

Use Python 3.10 or later. The delivered verifier ran with Python 3.13.5
and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python code/verify_results.py
python code/degrees.py 20
python code/degrees.py 20 --shear-degree 2
python code/degrees.py 20 --shear-degree 2 --characteristic 3
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Do not use Python's `-O` optimization flag for the verifier: assertions
are its checks. The calculator needs only the Python standard library.
For characteristic specialization, pass the **actual degree after reduction**;
an omitted shear degree denotes `h=0`, whereas degree zero denotes a
nonzero constant shear. Polynomial degrees are not degrees of reduced
polynomial functions on a finite set.

The TeX build uses standard packages including `newtxtext`, `newtxmath`,
`amsmath`, `amsthm`, `mathtools`, `microtype`, `tcolorbox`, and `cleveref`.
No font files are bundled.

## Research status

Complete arguments are supplied, but the new results are unrefereed and not
formalized in Lean or Rocq. The original map, determinant, collision,
generic-degree computation, and shear construction are prior work.
The baseline dynamical-degree value was suggested in a public Zenodo record;
the present work supplies an independent all-iterate proof and extensions.
An exhaustive historical-priority claim is not made.
