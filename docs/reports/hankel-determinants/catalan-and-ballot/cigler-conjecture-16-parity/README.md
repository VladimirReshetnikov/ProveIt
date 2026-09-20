# A parity factorization and sharp stabilization for Cigler's Hankel polynomials

**Outcome:** a complete proposed proof of Conjecture 16 in Johann Cigler,
*Hankel determinants of middle binomial coefficients and conjectures for some
polynomial extensions and modifications*, arXiv:2111.14492v3, Section 6,
pages 21–22. The article also determines the first coefficient at which the
conjectured stabilization fails.

**Status:** AI-assisted research draft, dated 20 September 2026. The argument
has not been independently refereed or checked in a proof assistant. A bounded
literature search did not identify a later solution of this specific conjecture;
this is not a guarantee of novelty or priority. See `STATUS.md` and `SOURCES.md`.

## Why this is a different problem from the supplied manifest

The related manifest entry, **Product formulas for ballot-polynomial Hankel
determinants**, concerns Cigler's **Conjectures 13–15 in Section 5**, for the
moments `a_n(t)`. This package concerns **Conjecture 16 in Section 6**, for
`c_n(t)`. It neither reproduces nor relies on the claimed proofs in that entry.
The supplied manifest itself has not been modified.

## Main result

Let `D_k(n;t) = det(c_{k+i+j}(t))_(0 <= i,j < n)`, where the `c_r(t)` are given
by the explicit binomial formula in equation (1.1) of the article. Set

\[
\mathcal H_k(n;t)=(-1)^{k\binom n2}t^{-\binom n2}D_k(n;t),
\qquad a=\lfloor k/2\rfloor,\quad b=\lfloor(k-1)/2\rfloor.
\]

For every `k >= 1` and `n >= 0`, this is a reciprocal integer polynomial of
exact degree `(k-1)n`, with constant and leading coefficients 1 and strictly
positive coefficients throughout its support. For `k >= 2`,

\[
\mathcal H_k(n;t)=\frac{1}{(1-t)^a(1-t^2)^{ab}}
-\binom{n+a}{a-1}t^{n+1}+O(t^{n+2}).
\]

Here the expansion is formal at `t=0`. It proves that coefficients stabilize
through degree `n` and that the first failure is always at degree `n+1`, with
exact deficit `binomial(n+a,a-1)`. For `k=1` the polynomial is identically 1.

The proof factors the original determinant according to the parities of `k`
and `n`. The two auxiliary factors are principal minors of powers of simple
tridiagonal matrices. Coefficientwise total nonnegativity gives positivity;
explicit, fully derived alternants give stabilization. No unproved Schur
identity is used.

Further proved consequences include fixed-size determinant evaluations, a
nonminimal recurrence at each fixed shift, uniform convergence on compact
subsets of the open unit disk, and product formulas at `t=1`.

## Contents

- `article.pdf` — the typeset article with complete proofs, examples, and audits.
- `article.tex` — standalone LaTeX source; the bibliography is included inline.
- `code/hankel.py` — source moments, fraction-free determinants, independent
  banded-matrix computation, parity and alternant formulas, coefficient extraction.
- `code/verify.py` — main exact integer and polynomial regression suite.
- `code/verify_additional.py` — exact recurrence and specialization checks.
- `data/*.json`, `data/*.log` — recorded results and example coefficient arrays.
- `STATUS.md`, `SOURCES.md` — logical scope, limitations, and source audit.
- `requirements.txt`, `Makefile`, `LICENSE` — reproducibility and source license.

## Reproduce the checks

From this directory, with Python and SymPy available:

```sh
python -m pip install -r requirements.txt
python code/verify.py
python code/verify_additional.py
```

Or run `make verify`. Do not use Python's `-O` option; both verification drivers
reject optimized mode because they use assertions. The recorded run used
Python 3.13.5 and SymPy 1.14.0. All mathematical arithmetic in the checks is
exact; timing measurements are not mathematical evidence.

The main suite passed 1,248 original-Hankel/parity evaluations, 864 auxiliary
corner/alternant evaluations, 90 full polynomial comparisons with every
main-theorem assertion, and 84 auxiliary first-defect checks. Separately, the
supplementary suite passed 234 product evaluations at `t=1` and 126 recurrence
residual checks. The ranges are recorded explicitly in the JSON files.

A **separate experimental** rectangular-Schur formula passed 1,248 exact
integer evaluations. It remains a conjecture in this package and is not a
proof dependency. Finite tests of any of the formulas are not proofs for all
indices; the all-index proofs are in the article.

The drivers regenerate their JSON files. To capture new console transcripts,
redirect their output to the corresponding `data/*.log` files.

## Rebuild the PDF

A TeX installation with the standard packages named in `article.tex` is needed:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Equivalently, run `make pdf`. No bibliography database or external figure file
is required. `make clean` removes LaTeX auxiliary files but preserves the PDF.

## Small usage example

```python
import sys
sys.path.insert(0, "code")
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ
from hankel import parity_formula, auxiliary_closed, stable_coefficient

R, t = ring("t", ZZ)
p = parity_formula(4, 2, t, auxiliary_closed)
print(p)
print(stable_coefficient(4, 3))  # 8; the actual cubic coefficient is 4
```

Use `parity_formula` at exceptional numerical parameters such as `t=0`.
`normalized_source` is deliberately a quotient computation and cannot evaluate
`0/0` before polynomial cancellation. At `t=1` and `t=-1`, `auxiliary_closed`
falls back to the nonsingular principal-minor definition.
