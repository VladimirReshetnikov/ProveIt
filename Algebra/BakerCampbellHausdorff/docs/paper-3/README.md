# The Baker–Campbell–Hausdorff Formula
## Complete Expansions, Structural Proofs, and Applications

Prepared September 16, 2026.

The main deliverable is `paper.pdf` (38 pages). Its self-contained LaTeX source
is `paper.tex`. Appendix C has a 54-entry claim-by-claim map to the mathematical
content of the English Wikipedia article, pinned to revision 1368909113
(August 11, 2026). Repeated instances of an identity are grouped.

## Reading the paper

Sections 2–4 establish the formal theorem, the complete word-coefficient and
Dynkin formulas, and every displayed term through degree six. Sections 5–7
derive the exponential differential, the Poincare integral, every bidegree of
the BCH expansion, Bernoulli recursions, quantitative convergence estimates,
and the source article's nonconvergence example. The remaining sections treat
Lie groups, exact special cases, Zassenhaus factorization, product formulas,
geometry, and quantum-mechanical identities with explicit operator domains.

All-orders descriptions include a finite formula for each BCH word coefficient;
a finite formula for each bidegree; all orders in Y, including the full
quadratic part; a finite nonrecursive rooted-tree formula for each Zassenhaus
exponent; a globally convergent ordered-simplex expansion for bounded
operators; all-order splitting errors; coframe and metric expansions; and
complete displacement-operator matrix elements.

Appendix A proves the ordered PBW theorem used in the algebraic development.
Appendix B lists all 72 nonzero associative word coefficients through degree
six. General foundations of analysis, such as the inverse function theorem,
ordinary differential equation uniqueness, and basic Hilbert-space spectral
theory, are assumed. Historical priority claims and theorems merely linked in
the source article's “See also” list are not treated as mathematical assertions
requiring proofs in this paper.

## Essential qualifications

Formal identities, convergence of a specific series, and existence of some
logarithm are different assertions. The paper preserves those distinctions.
It also corrects the coframe interpretation (W, not ad_X, is the coframe
matrix), states the hypotheses under which a pullback or the Killing form is
a nondegenerate metric, and does not infer bounded exponential identities
from a domain-free manipulation of unbounded operators.

The article contains mathematical proofs, supplemented by finite exact
checks. It has not been independently peer reviewed or certified by a proof
assistant. The numerical convergence bounds supplied are sufficient bounds,
not claims of optimality. No novelty claim is made for the individual results.

## Build the PDF

A normal TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. No external images, custom fonts, BibTeX database,
or internet access are needed to compile the source.

    latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

Alternatively, run `pdflatex paper.tex` three times to resolve cross-references.
A small Makefile supplies `make paper`, `make verify`, and `make clean`.

## Reproduce the exact verification

Python 3.10 or later, standard library only:

    python3 code/verify_bch.py --degree 10 --out data

On systems where Python is named `python`, substitute that command. The
program uses `fractions.Fraction` throughout; it does not require SymPy,
NumPy, Wolfram Language, a network connection, or a computer-algebra package.
It works with sparse noncommutative polynomials modulo terms of degree above
the selected cutoff. The degree-10 run passed all 26 checks. In particular,
word-logarithm expansion, Dynkin projection, the Poincare operator formula,
and a Bernoulli differential recursion agree exactly; two independent
Zassenhaus recursions and the rooted-tree formula agree; the ordered products
and the ordered-simplex expansion have the asserted coefficients.

The command accepts degrees from 6 through 14, but complexity and memory use
grow exponentially. The supplied result is degree 10, not a claim that all
higher selectable cutoffs were run. For requests above degree 10, the
coproduct and ordered-simplex checks are capped at degree 10, while the other
general computations use the requested degree. The displayed BCH polynomial
is checked through degree six; the explicitly displayed Zassenhaus terms and
symmetric cubic term are checked at their stated degrees.

Finite-degree agreement does not prove an all-orders identity, an analytic
convergence theorem, or a domain statement for an unbounded operator. Those
claims are addressed by the proofs in the paper.

## Data format

- `data/bch_words.json`: degree cutoff and BCH coefficients. A key such as
  `XXY` means the associative word X*X*Y, not a nested commutator. Coefficients
  are exact rational strings. Missing words have coefficient zero.
- `data/zassenhaus_words.json`: exponent C_n, indexed by n, in the same word
  representation, for 2 <= n <= 10. Factor order is
  exp(X) exp(Y) exp(C_2) exp(C_3) ... .
- `data/zassenhaus_tree_polynomials.json`: each C_n as a polynomial in the raw
  homogeneous coefficients A_j defined in equation (10.12). A key `2 3`
  means A_2*A_3 in that order. This is not multiplication of integers.
- `data/symmetric_bch_words.json`: log(exp(X/2) exp(Y) exp(X/2)), through the
  indicated cutoff, in associative words.
- `data/verification_results.json` and `data/verification_report.txt`: actual
  verification results, exact-check names, counts, elapsed time, and limits.

`source_manifest.json` identifies the scope reference and the scholarly
references. `quality_report.json` records the PDF/build and finite-check
status. No third-party article PDFs or font files are redistributed.
