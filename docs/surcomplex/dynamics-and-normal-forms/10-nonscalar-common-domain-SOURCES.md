# Sources and provenance

Prepared 22 September 2026. These links are bibliographic references; no
third-party source manuscripts or PDFs are redistributed in this package.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Commit: `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`

Document catalogue:
https://github.com/VladimirReshetnikov/Surreal/blob/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/README.md

Principal source:
https://github.com/VladimirReshetnikov/Surreal/blob/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/surcomplex/dynamics-and-normal-forms/article.tex

Title: *Surcomplex Dynamics: Linearization Thresholds, Periods, and Normal Forms*.
Date in source: 21 September 2026; extended 22 September 2026.
Source blob SHA: `a95e062f525e90df1f8e36e5342b8a6c2dca6614`.

The source was read through the GitHub connector at the pinned commit.
Inspected portions cover the abstract and provenance, support and halo
machinery, homological divisors, coefficient-category classification,
depth-dependent radius estimates and the nonscalar limitation, scalar
fixed-complexity tree estimates, and verification discussion. Relevant
labels include `dyn:thm:radius-depth` and `dyn:q:commongerm`.

The catalogue and these selected portions were read; no claim is made to
have independently audited every report, every Lean declaration, or all
retired manuscripts in Git history. The negative novelty comparison is
particularly well anchored because the principal report explicitly
identifies the nonscalar common-domain case as open at this snapshot.

## External primary literature

### Fauvet, Menous, Sauzin

Frédéric Fauvet, Frédéric Menous, David Sauzin,
*Explicit linearization of multi-dimensional germs and vector fields through
Ecalle's tree expansions*, arXiv:2507.13216v2.

- Metadata: https://arxiv.org/abs/2507.13216v2
- HTML: https://arxiv.org/html/2507.13216v2
- First submitted: 17 July 2025.
- Version inspected: 13 September 2026.

The HTML text was inspected, especially the tree formulas, admissible-cut
properties, and divisor estimates. The article explicitly credits those
methods and distinguishes the fixed-complexity rational-rank bound from
control uniform across tree complexities.

### Carletti

Timoteo Carletti, *The Lagrange inversion formula on non-Archimedean fields.
Non-Analytical Form of Differential and Finite Difference Equations*,
arXiv:math/0110135, 12 October 2001.

https://arxiv.org/abs/math/0110135

Only primary abstract/search metadata were available for the comparison.
A full-text audit of this paper was not performed.

### Higman

Graham Higman, *Ordering by divisibility in abstract algebras*,
Proceedings of the London Mathematical Society (3), 2 (1952), 326–336.

https://doi.org/10.1112/plms/s3-2.1.326

The classical word well-quasi-order result is an imported theorem. The
article derives the positive-word Hahn support lemma from it.

### Neumann

B. H. Neumann, *On ordered division rings*, Transactions of the American
Mathematical Society 66 (1949), 202–252.

https://www.jstor.org/stable/1990552

Primary journal bibliographic record checked; historical attribution for
the generalized-series support mechanism.

### Gonshor

Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*, London
Mathematical Society Lecture Note Series 110, Cambridge University Press,
1986.

https://www.cambridge.org/core/books/an-introduction-to-the-theory-of-surreal-numbers/312AE504A3E88E804054BFB390446374

Publisher bibliographic record checked. Classical surreal normal forms and
their arithmetic are imported background, not newly proved in this package.

## Evidence categories

1. The article contains the mathematical arguments. These are unrefereed
   and not proof-assistant checked.
2. verify.py and its transcript check finite combinatorial and exact
   polynomial identities only.
3. Successful PDF compilation and visual inspection establish document
   construction and layout, not mathematical correctness.
4. The literature search is targeted. No exhaustive priority claim is made.

No Lean formalization, Wolfram verification, or external peer review of
the new analytic theorem was performed or is implied.
