# Surcomplex Polynomial Algebra

**Factorization, Root Geometry, Multiscale Stability, and Residue Duality**  
Research exposition dated September 21, 2026.

## Contents

- `surcomplex_polynomial_algebra.pdf` — the typeset article.
- `surcomplex_polynomial_algebra.tex` — standalone LaTeX source with internal bibliography.
- `verify_examples.py` — reproducible exact symbolic checks, with explicit failure messages.
- `verification.txt` — successful execution report and the precise tested ranges.
- `requirements.txt` — the tested SymPy version.
- `literature_audit.md` — source roles, attribution, and literature-review limits.

The article develops finite-degree polynomial algebra over No[i]. It proves
modulus-geometric and valuation-geometric analogues separately, with special
attention to all-scale reduction, critical-point counts, coefficient precision,
root-cluster stability, support-controlled factor lifting, and residue duality
through collisions. It also includes finite CRT/Hermite interpolation,
resultants, polynomial maps, ramification, and a finite-data Nullstellensatz.

## Build the PDF

From this directory, with a standard LaTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_polynomial_algebra.tex
```

Alternatively, run `pdflatex surcomplex_polynomial_algebra.tex` repeatedly until
cross-references stabilize. The source uses ordinary TeX packages, including
AMS mathematics, Latin Modern, geometry, microtype, hyperref, cleveref, aliascnt,
and longtable. It requires no external image or bibliography file and no
network resources during compilation. The supplied predecessor manuscripts
are cited but are not required as build inputs.

## Reproduce the finite checks

The checks were run with Python 3.13.5 and SymPy 1.14.0. The script uses
Python 3.10-or-newer syntax.

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

An alternative report path may be supplied with `--output PATH`.
The successful run completed 478 exact assertions. Generic monic polynomials
were tested through degree 6 for residue/trace and related identities, with
trace-discriminant determinants through degree 4. Other checks cover 27
center/scale charts of a factored degree-7 example, the worked cubic and
quartic, finite Hensel recursions, Hermite jets, collision residues,
branch-value discriminants, and exact uncertainty witnesses.

## Mathematical status

Classical algebra and real-closed/valued-field ingredients are explicitly
identified. The supplied manuscripts are credited for their definitions,
analytic antecedents, and reused examples. This is not a claim to solve a
named published conjecture or to certify historical priority. The proofs have
not been independently refereed or checked in a proof assistant.

The symbolic checks are checks of finite formulas and examples, not a
verification of arbitrary surreal supports, arbitrary-rank Hahn fields,
transfinite summability, or universal mathematical statements by sampling.
