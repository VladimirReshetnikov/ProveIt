# A proof of Barry's Hankel--Somos-6 conjecture

Research note prepared on 19 September 2026. Start with **article.pdf**;
**article.tex** is the editable source.

## Result

Let G(0)=1 and

    G(x) = 1 / (1 - x(1+r*x)/(1-x) - x^2(1+s*x)/(1-x) - t*x^3*G(x)).

Put H_0=1 and H_N=det(g_{i+j}) for 0 <= i,j < N, where g_n=[x^n]G(x).
The manuscript proves, for N >= 6,

    H_N H_(N-6) = alpha H_(N-1) H_(N-5) + gamma H_(N-3)^2,

    alpha = t^2 (r+2)^2,
    gamma = t^3 ((s+t)(r+s+t+2)^2 + t(r+2)^3).

This is Barry's Conjecture 7 from arXiv:2211.12637. The expanded coefficient
printed there equals the compact formula above. Barry uses h_n=H_(n+1).
The proof also establishes a homogeneous four-parameter form and a polynomial
seven-parameter Hankel theorem that makes exceptional specialization rigorous.

The bilinear identity remains meaningful at zero determinants. A quotient
recurrence with a zero divisor does not. The verifier never divides by a
Hankel determinant to generate the tested sequence.

## Files

- `article.tex`, `article.pdf`: complete manuscript and bibliography.
- `code/verify.py`: independent exact numerical checks; standard library only.
- `code/symbolic_certificates.py`: 16 finite algebraic certificates; uses SymPy.
- `data/verification_summary.json`: full-run summary and environment details.
- `data/verification_cases.json`: all 1,128 parameter cases and their outcomes.
- `data/symbolic_certificates.json`: symbolic check results.
- `data/examples.json`, `data/example_*.csv`: exact example moments and determinants.
- `data/*_stdout.txt`: saved program output.
- `STATUS.md`: literature-search scope, attribution, and validation limits.
- `references.bib`: optional BibTeX data; the manuscript has an embedded bibliography.
- `Makefile`, `requirements-symbolic.txt`: build and verification helpers.

## Reproduce the calculations

Use Python 3.10 or later. The archived full run used Python 3.13.5.

```sh
python code/verify.py
```

Every H_N is computed independently from its matrix by Bareiss elimination,
with row pivoting and exact-division checks. Small matrices are cross-checked
against the permutation definition of the determinant. Original-family moments
are also compared with a separate tree-grammar recurrence.

The full suite has 10,248 recurrence checks in 1,128 cases; 553 cases include
zero Hankel determinants. Five additional examples add 75 recurrence checks.
A quick run is available:

```sh
python code/verify.py --quick
```

By default, the quick run writes to `data/quick_run/` so it does not overwrite
the archived full-run reports. An explicit `--output PATH` selects a different
destination. The regular full run overwrites the main data reports with the
new run. Elapsed time and Python version may differ; exact values should not.

For the optional symbolic checks:

```sh
python -m pip install -r requirements-symbolic.txt
python code/symbolic_certificates.py
```

These finite tests are not the all-index proof. The all-index proof is in
Sections 5--7 of the manuscript.

## Build the PDF

A TeX Live installation with pdfLaTeX, latexmk, newpx, AMS math packages,
tcolorbox, booktabs, fancyhdr, titlesec, listings, hyperref, and cleveref is used.
No external font files or downloaded images are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make pdf`, `make verify`, or `make symbolic`. The default
`make` target builds the PDF and runs the standard-library numerical checks.

## Validation and attribution

This is an unrefereed, AI-assisted research manuscript, not an independently
reviewed or proof-assistant-verified publication. The core genus-two identity
is due to Alfred J. van der Poorten (2005), not newly claimed here. The article
provides its own algebraic derivation of the needed identity and an explicit
application to Barry's conjecture, including a polynomial extension through
singular cases. No earlier direct resolution was found in the bounded search;
that is not a guarantee of priority. See STATUS.md.

The original Example 8 has a parameter-label discrepancy: its displayed
sequence corresponds to (r,s,t)=(-3,-2,1), not (-2,-2,1). Both are included
as separate reproducible examples. This discrepancy is not a counterexample
to the conjecture.
