# q-Binomial Coefficient Calculus

**Gaussian Kernels, Bell Polynomials, Basis Changes, Parameter Jets, and Inversion**  
An extension of *Combinatorial Coefficient Calculus*  
September 4, 2026

## Contents of this archive

- `q_binomial_coefficient_calculus.tex`: standalone LaTeX source.
- `q_binomial_coefficient_calculus.pdf`: compiled article (55 pages).
- `verify_identities.py`: deterministic exact-arithmetic verification program.
- `validation_report.txt`: the successful verification output, with 10,912 checks in 36 groups.
- `README.md`: this file.

The article contains 16 chapters, a formula atlas, a reproducibility appendix,
and a bibliography. It is a mathematical extension, not a replacement of the
canonical source document; no repository files were changed.

## Main developments

The common mechanism is finite geometric products -> logarithmic power sums ->
ordinary Bell polynomials. It connects Gaussian coefficients with convolution,
inversion, symmetric functions, q-Stirling arrays, Jackson differentiation,
ordinary composition, and Lagrange inversion.

Further developments include recurrence-free coefficients of Gaussian
polynomials through divisor sums; Bernoulli cumulants at q=1; exact all-order
root-of-unity expansions by deflation; weighted Gaussian sums; geometric
extrapolation with complete error response and exact absolute-weight norm;
repeated-root filters for logarithmic error terms; and extensions to Gaussian
multinomials and balanced factorial ratios. Every theorem has a proof in the
article or is explicitly reduced to a result proved there. Established identities
are not presented as claims of historical novelty.

## Build the PDF

Use a TeX installation with Libertinus and the packages listed in the preamble.
The source has an internal bibliography and all mathematical macros; it does not
require the repository's shared notation file, any external figures, BibTeX, or
network access during compilation. No font files are included in this archive.

Run these commands from the directory containing the source, in PowerShell,
Command Prompt, or a POSIX shell:

```text
pdflatex -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex
pdflatex -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex
pdflatex -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex
```

Or use:

```text
latexmk -pdf q_binomial_coefficient_calculus.tex
```

## Reproduce the exact checks

Python 3.9 or later, standard library only:

```text
python verify_identities.py
```

A failed equality raises an AssertionError. A successful run prints the counts
for every test group. The program recomputes all checks and does not read the
saved report. It uses exact integer/rational polynomial arithmetic, including
arithmetic modulo cyclotomic polynomials for roots of unity; it uses no numerical
tolerances and makes no network requests.

The finite checks audit signs, shifts, and normalizations. They supplement the
proofs, do not establish general theorems by testing, and do not assert Lean
formalization.

## Source provenance

Requested canonical source:

https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Combinatorial_Coefficient_Calculus

The directory metadata read for this extension identified the source TeX file
with Git blob SHA `ffbe7c117db3fbeb3c0ae804e84422bb2dc6a89b`.
This identifies that file's content, not the repository's latest commit or
formalization status. The original source is not included in this archive.
