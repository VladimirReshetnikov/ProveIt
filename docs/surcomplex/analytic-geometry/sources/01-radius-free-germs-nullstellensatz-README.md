# Infinitesimal Analytic Geometry over the Surcomplex Numbers

**Radius-Free Hahn Germs, a Nullstellensatz, and Conservation of Singular Zeros**

Research continuation dated September 21, 2026. The PDF contains 31 pages.

## Contents

- `surcomplex_analytic_geometry.tex`: self-contained LaTeX source, with an embedded bibliography.
- `surcomplex_analytic_geometry.pdf`: compiled article.
- `verify_examples.py`: exact symbolic checks for the examples.
- `verification_report.txt`: the recorded successful run of all 258 checks.
- `build.sh`: rebuilds the PDF and reruns the checks.
- `requirements.txt`: Python dependency for the example checks.
- `README.md`: this file.

The supplied source manuscript, `surcomplex_analysis(3).tex`, motivated the
several-variable research direction. It is cited in the article but is not
needed to compile or understand this self-contained continuation.

## Main mathematical content

For a nonzero divisible set-sized ordered subgroup Gamma of the surreal
numbers, the article studies A_n = C{z_1,...,z_n}((t^Gamma)). Each Hahn
coefficient is an ordinary convergent germ, but the coefficient family need
not have any common ordinary convergence radius.

The article proves support-controlled division and preparation; Noetherianity,
regularity, and a strong infinitesimal Nullstellensatz; conservation of the
finite algebraic length of arbitrary isolated complete intersections under
positive-support perturbations; perfect residue duality and a trace--Jacobian
identity; invariance of the finite zero scheme under enlargement of the Hahn
workspace; faithful flatness of the inclusion into formal-coefficient Hahn
series; and a quantitative root correspondence using inverse-Jacobian
valuation loss. The strict scalar factor-two threshold is shown to be sharp.

Two detailed two-variable examples cover coupled root splitting and infinite
residue cancellation. The second example genuinely lacks a common ordinary
convergence radius and uses a higher-rank exponent group.

## Rebuild

A normal TeX installation with `pdflatex` and the packages named in the source
is sufficient. There is no separate BibTeX step and no external figure asset.

On a Unix-like system, run:

```sh
sh build.sh
```

Or compile manually, running `pdflatex` three times to resolve the contents,
references, and hyperlinks:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analytic_geometry.tex
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analytic_geometry.tex
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analytic_geometry.tex
```

For the independent example checks, use Python 3.10 or later and SymPy:

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The script fails with an exception on a failed check and writes the report
beside itself. It uses exact arithmetic, not floating-point root estimates.

## Proof and novelty status

The proofs in the article rely on explicitly identified classical inputs:
Hahn--Neumann summability, ordinary analytic and formal Weierstrass division,
classical local residue duality, ordinary finite-family trace identities, and
standard Noetherian commutative algebra.

The proposed novelty concerns the exact radius-free Hahn-germ and explicit
support-controlled deformation package. The article acknowledges close
antecedents in non-Archimedean analytic structures and multidimensional
residue theory. It does not claim that those general subjects or their basic
theorems are new, that a named published conjecture has been solved, or that a
literature search can certify priority. Independent expert review is still
appropriate before publication or reliance on the results in further work.

The 258 symbolic checks concern the worked formulas only. They do not
implement arbitrary Hahn fields and are not formal verification of the
Noetherian, flatness, residue, or stability proofs.
