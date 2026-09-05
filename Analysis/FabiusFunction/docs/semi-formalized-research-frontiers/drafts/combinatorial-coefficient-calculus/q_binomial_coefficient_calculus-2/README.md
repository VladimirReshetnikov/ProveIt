# q-Binomial Coefficient Calculus

Gaussian weights, Bell expansions, interpolation, reversion, and root-of-unity jets

A self-contained mathematical extension to Vladimir Reshetnikov's
Combinatorial Coefficient Calculus in the ProveIt repository.
Prepared September 4, 2026.

## Contents

- q_binomial_coefficient_calculus.tex: complete LaTeX source, with an inline bibliography.
- q_binomial_coefficient_calculus.pdf: rendered 29-page article, including title, contents, and references.
- verify_identities.py: independent finite exact-arithmetic regression checks.
- verification_report.json: aggregate report for the included successful run.
- verification_algebra.json, verification_coefficients.json,
  verification_inversion.json, verification_roots.json: per-group reports.
- requirements.txt: the SymPy version used for verification.
- Makefile: build and verification commands.
- SHA256SUMS.txt: checksums of the package files other than the checksum file itself.

## Main topics

The article develops Gaussian coefficients as elementary and complete symmetric
functions; finite and infinite q-binomial theorems; Vandermonde and terminating
q-Chu–Vandermonde identities; divisor-sum formulas for coefficients in q;
Gaussian convolution and weighted inversion; Newton interpolation on two
lattices and an explicitly normalized q-Stirling basis change; ordinary Bell
composition and Riordan matrices in q-factorial coordinates; Jackson product
rules and the quantum-plane binomial theorem; product-weighted univariate and
coupled bivariate Lagrange inversion; distinct q-Catalan families; Bernoulli–Bell
formulas for every derivative at q=1; cyclotomic factorization, q-Lucas, and
all-order root-of-unity derivatives; and exact geometric extrapolation weights.

The central device is an explicitly finite partition kernel applied to the
logarithm of a product of q-shifted factorials. The source-interface crosswalk
uses theorem labels rather than unstable page numbers.

## Build the PDF

A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. No separate bibliography, images, custom font files,
or network access are required to build the article.

Run from the extracted directory:

    pdflatex -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex
    pdflatex -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex
    pdflatex -interaction=nonstopmode -halt-on-error q_binomial_coefficient_calculus.tex

The repeated passes stabilize the table of contents and cross-references.
On a system with GNU Make, `make pdf` performs these passes.
The included PDF was compiled with pdfTeX 1.40.26 and visually inspected.

## Reproduce the checks

Python 3.10 or newer is required. The included run used Python 3.13.5 and SymPy 1.14.0.
Install the verification dependency, then run:

    python -m pip install -r requirements.txt
    python verify_identities.py --group all

Individual groups are `algebra`, `coefficients`, `inversion`, and `roots`.
The script uses exact polynomial, rational, and algebraic arithmetic, rejects
floating-point inputs in its assertion function, and requires no network access
once SymPy is installed. It rewrites the JSON reports next to the script.

The included run passed 2,693 assertions:

    algebra          484
    coefficients     356
    inversion        802
    roots           1051

These are finite regression checks, not universal formal verification.
The mathematical arguments are provided in the article. No Lean files were
added or compiled, and the repository itself was not modified. Classical
identities are not claimed as discoveries; derived formulas are proved without
an assertion of historical priority.

## Source and references

Canonical base package:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Combinatorial_Coefficient_Calculus

The article follows the canonical TeX source and its stated provenance, not an
assumption that the retained historical PDF is synchronized. The bibliography
also cites the NIST DLMF and primary papers by Formichella–Straub,
Harman–Hopkins, and Cigler. The base manuscript is not reproduced in this archive.
