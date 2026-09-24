# Sources, repository comparison, and novelty boundaries

Research date: 22 September 2026. References below identify consulted primary
sources and the portions actually used. Bibliographic entries also appear in
the article. Third-party texts and font files are not included in this package.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned revision: `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`.
The pin was obtained through the connected GitHub recursive-tree read. Reads
of the comparison documents used that revision, not an unpinned latest branch.

The targeted audit included the root README, documentation catalogue, directory
listings, substantive passages of the holonomic manuscript, and related README
scope statements. It did not include a complete line-by-line review of every
report, Lean declaration, historical manuscript, archive, or branch. No blanket
claim that no equivalent result can occur anywhere in the repository is made.

### Direct question addressed

`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`
and its local README:

https://github.com/VladimirReshetnikov/Surreal/tree/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions

The definitions use the same characteristic-zero Hahn coefficient field and
strong-entireness convention. The report proves linear differential rigidity
and explicitly distinguishes it from nonlinear differential algebraic
rigidity. Question 15.1 asks about the nonlinear case. This package gives an
answer for all first-order algebraic equations, a sufficient condition in
higher order, and a weighted multivariable extension. It does not answer all
of Question 15.1. The question is identified as a repository question, not as
a separately established historical conjecture.

### Adjacent material distinguished

Documentation catalogue:
https://github.com/VladimirReshetnikov/Surreal/blob/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/README.md

Tail-spans and differential transcendence:
https://github.com/VladimirReshetnikov/Surreal/tree/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/surreal/tail-spans-and-differential-transcendence

The tail-span report's README states all-order independence results for
specific constructions, with scalar or fixed-ordinary-domain analytic
derivations and specified smaller base fields. Those are not claimed new
here. The new general two-jet consequence instead assumes strong entireness
and permits the entire Hahn field as the constant field. Existing quadratic-
exponent and infinite-rank examples are explicitly credited; only their
new first-order nonlinear consequence is proposed as an addition.

Analytic-geometry and product-birthday README files were read for context,
not used as proofs of the new results. The existing holonomic theorem is
credited as a predecessor; the new proof does not assume its linear escape
argument extends to nonlinear recurrences.

## Primary literature consulted

### Hahn and surreal foundations

V. Mantova and M. Matusinski, *Surreal numbers with derivation, Hardy fields
and transseries: a survey*, arXiv:1608.03413v2.
https://arxiv.org/html/1608.03413v2

Section 2 was consulted for normal forms and the relation to Hahn expansions.
Hahn-field support algebra and Conway normal forms are standard ingredients,
not proposed new contributions. The article gives its own elementary
finite-product support argument; the full positive-support geometric-series
lemma is an imported standard ingredient in the domain example.

### Classical central-index methods

W. K. Hayman, *The local growth of power series: a survey of the Wiman–Valiron
method*, Canadian Mathematical Bulletin 17 (1974), 317–358.
https://doi.org/10.4153/CMB-1974-064-0

Publisher metadata and abstract were consulted. The classical method is
credited as a conceptual precedent; no theorem from an unread full text is
used in the proof. The exact initial-polynomial reduction in this manuscript
is not presented as the invention of central-index reasoning.

### Nonlinear Newton and indicial methods

J. Cano and P. Fortuny Ayuso, *Power series solutions of non-linear q-difference
equations and the Newton–Puiseux polygon*, Qualitative Theory of Dynamical
Systems 21 (2022), article 123.
https://doi.org/10.1007/s12346-022-00656-0

The publisher's full HTML introduction and Section 2 were consulted, including
initial and indicial polynomials. The equation/operator and generalized-series
setting differ from the present arbitrary-rank Hahn-coefficient strong-entire
problem. No novelty is claimed for Newton or indicial-polynomial techniques.

### Non-Archimedean nonlinear value distribution

P.-C. Hu and Y.-Z. Luan, *Non-Archimedean meromorphic solutions of functional
equations*, arXiv:1311.5291v1 (2013).
https://arxiv.org/abs/1311.5291

The PDF's parsed text was consulted for the field hypotheses and Theorems 1.1,
1.3, and 1.5. The field is complete and algebraically closed with a nontrivial
non-Archimedean absolute value. The paper supplies important nonlinear
predecessors, not a cited proof of the present arbitrary-rank statement.
The remote PDF screenshot service returned errors; no claim of successful
visual inspection of that third-party PDF is made. No figure or table from
it is used or reproduced.

P.-C. Hu and C.-C. Yang, *Meromorphic Functions over Non-Archimedean Fields*,
Mathematics and Its Applications, Springer Dordrecht, 2000.
https://doi.org/10.1007/978-94-015-9415-8

Publisher metadata and description were consulted, not the complete monograph.
Consequently this search cannot certify that rank-one special cases of the
newly formulated theorem were previously unknown.

### Tropical differential algebra

J. Giansiracusa and S. Mereta, *A general framework for tropical differential
equations*, manuscripta mathematica 173 (2024), 1273–1304.
https://doi.org/10.1007/s00229-023-01492-5

The publisher's HTML was consulted for the differential-enhancement and
tropicalization framework. It is credited as a relevant broader precedent.
The manuscript makes no claim of equivalence to that full theory or of a new
tropical fundamental theorem.

## What the search supports

The inspected sources did not identify the exact arbitrary-rank strong-family
first-order theorem, its explicit nonlinear finite exclusion certificate,
or the positive-weight Euler formulation as stated in this package. That
supports a **proposed contribution**, not certified historical priority.
Some search results were poorly targeted. No exhaustive MathSciNet, zbMATH,
full-book, or citation-network audit was performed.

The detailed written proofs are offered for independent scrutiny. They have
not been checked in Lean or by an independent referee. The unrestricted
higher-order nonlinear question remains outside the proved conclusions.
