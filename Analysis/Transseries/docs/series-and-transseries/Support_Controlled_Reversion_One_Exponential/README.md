# Support-Controlled Reversion and the Exact One-Exponential Substitution Group

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Start here

Read `reversion_and_one_exponential.pdf` (23 A4 pages). Its self-contained
editable source is `reversion_and_one_exponential.tex`; no files from the
ProveIt repository are needed to compile it.

The article addresses three specifically labeled questions in the ProveIt
transseries volume:

| Repository label | Article result |
| --- | --- |
| `plt:rmk:ext-open-burmann` | Theorem 3.2: integer-indexed Hahn Lagrange inversion, with a finite outer index bound at every power exponent. |
| `plt:rmk:ext-open-denominators` | Theorem 4.1 and Corollary 4.2: Newton iterates preserve the normalized support monoid; the optimal universal Puiseux denominator is the original denominator. |
| `plt:rmk:ext-open-resurgence` | Theorem 6.1, Corollary 6.4, and Section 7: obstruction to unrestricted one-exponential closure, maximal admissible sublinear substitution group, and exact-core inversion. This settles a formal algebraic component, not general resurgence. |

Theorem 8.1 gives the exact leading block in every inverse exponential sector
for a single primitive exponential perturbation. Section 9 develops the
inverse of X + log(X) + exp(-X), including rational coefficients, sharp pole
orders, and an all-orders uniform geometric remainder bound. Section 11
contains nine further research questions.

## Scope and status

The main mathematical arguments are human-readable proofs in the article.
The general Hahn and Lagrange mechanisms are classical; the article does not
claim global literature priority or discovery of transseries inversion.
The repository comparison is targeted, not an exhaustive audit of every file.
The bibliography and stable source labels identify the material inspected.

The canonical raw-source web snapshot and live package README were inspected.
Caching and active repository editing can produce different snapshots, so no
unverified commit hash, current TeX/PDF parity, or exhaustive novelty claim
is asserted.

No new Lean, Coq, or other proof-assistant module was compiled. The Python
checks are finite regression tests, not formal proofs. Numerical tests use
high precision but not interval arithmetic; the stated analytic remainder
bound has a separate proof in the article.

## Build the PDF

A standard TeX installation with pdfLaTeX, Latin Modern, and the packages
listed in the source is sufficient. From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error reversion_and_one_exponential.tex
pdflatex -interaction=nonstopmode -halt-on-error reversion_and_one_exponential.tex
pdflatex -interaction=nonstopmode -halt-on-error reversion_and_one_exponential.tex
```

On a POSIX system, `sh build.sh` performs the three passes. The delivered PDF
was compiled in three final passes with no LaTeX warnings or overfull boxes.
All pages were rendered with Poppler for visual inspection; the cover,
contents, and bibliography were rechecked after the last layout adjustment.

## Reproduce the checks

Python 3.10 or later is required. The recorded run used Python 3.13.5,
SymPy 1.14.0, and mpmath 1.3.0. The dependency versions are pinned in
`requirements.txt`.

```sh
python -m pip install -r requirements.txt
python verify_results.py
```

The program checks mixed rational-exponent reversion modulo t^4, agreement
with three Newton steps in the denominator-6 lattice, and the first six
mixed-example coefficients, their pole orders and leading blocks. It also
checks the defining implicit equation through exponential order six and
compares 24 numerical truncations against the proven error bound.

It writes or replaces `verification_report.txt` and `numeric_checks.csv` in
its own directory. It exits with an exception if an asserted check fails.
It does not access the network, modify the repository, or edit the article.

## Files

- `reversion_and_one_exponential.tex`: complete article source.
- `reversion_and_one_exponential.pdf`: compiled article.
- `verify_results.py`: exact symbolic and high-precision numerical checks.
- `verification_report.txt`: execution receipt and six explicit rational coefficients.
- `numeric_checks.csv`: all 24 numerical comparisons.
- `requirements.txt`: pinned Python dependencies.
- `build.sh`: three-pass PDF build.
- `README.md`: this guide.
