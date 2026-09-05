# Gaussian Coefficients in Combinatorial Coefficient Calculus

A 35-page, self-contained q-binomial extension of the ProveIt article
*Combinatorial Coefficient Calculus*.

## Contents

- `q_binomial_coefficient_calculus.tex` — complete standalone LaTeX source.
- `q_binomial_coefficient_calculus.pdf` — compiled article with linked contents,
  equation references, bibliography, and PDF bookmarks.
- `verify_identities.py` — documented exact-arithmetic verification program.
- `verification_results.txt` — output from the delivered program: 10,267 exact
  checks passed, followed by a separate optional numerical experiment.
- `README.md` — this file.

## Build the article

From this directory, with a TeX installation containing the packages declared
in the preamble (including Libertinus, mathrsfs, microtype, and cleveref):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex
```

Alternatively run `pdflatex` repeatedly until all references stabilize.
No external bibliography database, figures, repository checkout, custom style
file, or network access is required. Font files are not distributed here.

## Run the checks

Python 3.10 or later:

```sh
python3 verify_identities.py
```

The core exact checks use only Python's standard library. The optional final
experiment uses `mpmath` when installed and otherwise prints a skip notice.
It evaluates the moving-base asymptotic expansion at 70 decimal digits;
those numerical results are not interval-certified bounds.

The exact tests compare different constructions, including finite products,
polynomial recurrences, direct subset/permutation enumeration, divided
differences, formal series substitution, and cyclotomic congruences. The code
uses recurrences as independent checks of the article's closed formulae.
Finite tests do not replace the general mathematical proofs and are not Lean
formalization.

## Scope and provenance

The linked parent source and its broader Fabius/Rvachev companion were read
from the live `main` branch on 4 September 2026. This is a standalone extension,
not an edit to the repository and not an immutable snapshot of that branch.
The bibliography records the parent directory, related primary papers, and
DLMF references. No priority claim is made for classical identities.

The article distinguishes ordinary coefficient normalization, geometric
Newton bases, Jackson differentiation, and ordinary series composition. Its
asymptotic assertions specify their parameter domains; the moving-base
expansion is a Poincare expansion, not a claim of a complete exponentially
improved transseries.
