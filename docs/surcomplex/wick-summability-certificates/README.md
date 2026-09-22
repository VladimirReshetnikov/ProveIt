# Finite Certificates for Surcomplex Wick Summability

**Valuation balancing, connected obstructions, and multiscale Gaussian perturbations**  
Research manuscript dated September 22, 2026.

## Contents

- `article.pdf` — the 27-page typeset paper, including full proofs, examples,
  bibliography, and research-status discussion.
- `article.tex` — self-contained LaTeX source; references are included inline.
- `code/wick_certificates.py` — exact strict-feasibility solver over finite-rank
  lexicographically ordered rational value groups. Returns either a balancing
  vector or an independently checkable nonnegative integer obstruction.
- `code/verify.py` — reproducible finite tests using only the Python standard library.
- `data/verification.json` — actual recorded results: 7,684 passing finite cases,
  seed 20260922, and sample positive and negative certificates.
- `RESEARCH_AUDIT.md` — repository snapshot, inspected material, literature
  comparison, and limitations of the novelty search.
- `VERIFICATION.md` — what was checked, what was not, and how to reproduce it.
- `Makefile` — optional build and test commands.

## Main result

For a finite polynomial interaction `P = sum_a g_a x^(alpha_a)` and a symmetric
Hahn covariance matrix `C`, the full family of Wick diagrams is strongly Hahn
summable exactly when there is a valuation vector `p` with

    v(g_a) + alpha_a . p > 0       for every interaction type a,
    v(C_ij) - p_i - p_j > 0       for every nonzero covariance entry.

Equivalently, every nonzero nonnegative integer solution of the color-incidence
equations has positive valuation weight. A finite Hilbert basis suffices to test
this condition. A failed strict-feasibility problem supplies an integer
obstruction. Every pairable external monomial has the same domain.

For vertex valences at least two, connected vacuum diagrams have exactly the same
diagramwise domain. For positive-definite real covariance, the criterion reduces
to one inequality per interaction monomial. The article includes an explicit
mixed-quartic instability and an isotropic cancellation example explaining why
arbitrary cancellation-aware regroupings are outside this exact criterion.

## Build the paper

A standard TeX Live installation with pdfLaTeX and the packages listed in the
preamble is sufficient. No external images, font files, BibTeX run, or network
access are required.

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
```

Without `latexmk`, run `pdflatex -halt-on-error -interaction=nonstopmode article.tex`
three times so that the table of contents, references, and hyperlinks stabilize.

## Run the checks

Python 3.10 or later, standard library only:

```sh
python3 code/verify.py
```

This overwrites `data/verification.json` with a new run. Mathematical results and
sample certificates are deterministic for the stated seed; elapsed time varies.
Do not run with Python's `-O` optimization flag, since internal certificate checks
use assertions.

Run a standalone sample obstruction:

```sh
python3 code/wick_certificates.py
```

In your own code, put the `code` directory on the Python import path. The example
in Section 12.1 of the article shows the API. Edge indices in Python are zero-based.
Zero covariance entries must be omitted, not assigned an artificial infinite
valuation.

## Research and implementation status

This is a candidate-new theorem package with mathematical proofs, not a claim to
have resolved a named longstanding conjecture. Wick combinatorics, normal-form
arithmetic, and the finite-dimensional tools are credited as classical.

The work is unrefereed and not proof-assistant verified. The exact theorem package
was not located in the material successfully inspected, but the priority search
and repository archive audit are incomplete. In particular, the contents of the
18 ZIP archives in `docs/new` were not exhaustively accessible. See Section 13 and
`RESEARCH_AUDIT.md` before making a claim of historical or repository-wide absence.

The software is a finite certificate solver, not a general Hahn-series or surreal
CAS. It assumes exact valuations and the nonzero incidence pattern are supplied.
The mathematical theorem permits arbitrary-rank divisible ordered abelian groups;
the software handles finite-rank lexicographic rational vectors. Its
Fourier–Motzkin elimination can be exponential and has an explicit row guard.
A resource-limit exception is not an infeasibility certificate.

No changes were made to the GitHub repository. No third-party articles, fonts,
repository archives, or source files are redistributed in this package.
