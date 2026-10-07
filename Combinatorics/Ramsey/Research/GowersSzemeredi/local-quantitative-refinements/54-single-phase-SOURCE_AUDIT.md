# Source, novelty, and proof audit

**Manuscript:** A Single Quadratic Phase Across All Translates  
**Date:** 6 October 2026  
**Scope:** a local strengthening of Gowers's Section 8, not an end-to-end bound.

## Repository source control

Repository: `VladimirReshetnikov/ProveIt`.
The formal statement and edited Gowers transcription used for the interface
were read at commit

    6a6d7961c3c261da7dc18def13fff30b12dd5c04

Exact source objects established by the connected GitHub reads:

| Source, relative to Combinatorics/Ramsey/ | Blob SHA |
|---|---|
| Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex | `41085a0efde8c1932e86e80c791984f52841c22e` |
| Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.pdf (metadata) | `db4a37e25a5b7800c925d08f1d38eae9aee8d923` |
| Lean/GowersSzemeredi/Sections08_09.lean | `0fb6e0a1de3f046f436747603f7eeb06f8d1f074` |
| Research/GowersSzemeredi/local-quantitative-refinements/36-symmetry-certification-SOURCE_AUDIT.md | `71ca9b26b3520c3ed125fa271881c78df507eda9` |

The research README was also read in selected ranges through the then-current
`main` branch, with returned blob
`b2e25fa0558ef2c17b052bd4ba1a670d7a1cc5ce`. Its entire content and every pending
research manuscript were not read. Treat this as a scoped overlap check rather
than a complete corpus-wide novelty audit.

Repository URLs:

- https://github.com/VladimirReshetnikov/ProveIt/tree/6a6d7961c3c261da7dc18def13fff30b12dd5c04/Combinatorics/Ramsey
- https://github.com/VladimirReshetnikov/ProveIt/blob/6a6d7961c3c261da7dc18def13fff30b12dd5c04/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections08_09.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6a6d7961c3c261da7dc18def13fff30b12dd5c04/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs08QuadraticBias.lean

### Read scope and conclusions

Directory listings, selected research-index ranges, and the complete returned
Section 8–9 statement module were inspected. The edited Gowers TeX was read in
selected ranges, notably lines 1390–1495 containing the Section 8 motivation,
Proposition 8.1 and the beginning of its proof; nearby Section 7 text was also
read. The proof module was located by repository search, which returned the
`proposition_8_1_holds` declaration and odd-modulus comment. Its full Lean proof
was not audited or run.

The source 36 symmetry audit was read to avoid presenting its global
multilinear-symmetry program as new. Its results are not proof dependencies for
this article. A repository search for “spectral overlap” returned no matching
result, but a search miss does not establish absence of a related theorem.

The existing formal Proposition 8.1 is already proved in the inspected source.
Its odd-modulus hypothesis is a prior correction, not a discovery claimed here.
The new result replaces translate-dependent phases by one global quadratic
polynomial and strengthens the density-dependent correlation bound. It does not
repair an unproved existing Proposition 8.1.

## Primary literature consulted

### 1. Original Section 8 baseline

W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional
Analysis 11 (2001), 465–588. DOI: `10.1007/s00039-001-0332-9`.

- https://doi.org/10.1007/s00039-001-0332-9
- https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The public PDF's parsed text and a rendered image of journal page 511
(PDF page 47, zero-based index 46) were inspected. Proposition 8.1 there gives
translate-dependent quadratic polynomials and coefficient `1/sqrt(2)` under the
stated derivative-energy hypothesis. The repository transcription and formal
statement provide the corrected odd-modulus interface used in the article.
No copy of Gowers's paper is redistributed in the package.

### 2. Classical graph extremal value

T. S. Motzkin and E. G. Straus, *Maxima for graphs and a new proof of a theorem
of Turán*, Canadian Journal of Mathematics 17 (1965), 533–540.
DOI: `10.4153/CJM-1965-053-6`.

- https://doi.org/10.4153/CJM-1965-053-6
- https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/maxima-for-graphs-and-a-new-proof-of-a-theorem-of-turan/AC3CC45896B053B75C856F25829CA95C

The bibliographic record and theorem description were checked. The article
includes the complete short extremal-value proof, and credits this theorem
rather than claiming a new clique bound.

### 3. Caution about equality classifications

Q. Tang, X. Zhang, C. Zhao, and P. Zhao, *On the maxima of Motzkin–Straus programs
and cliques of graphs*, Journal of Global Optimization 84 (2022), 989–1003.
DOI: `10.1007/s10898-022-01187-3`.

- https://link.springer.com/article/10.1007/s10898-022-01187-3

The publisher abstract was inspected. It reports errors in earlier proposed
maximizer classifications. No result from the subscription full text is invoked.
The cycle equality classification in the present article is proved directly by
a nonnegative graph certificate and the four-vertex-path identity.

### 4. Contemporary global benchmark, not a dependency

J. Leng, A. Sah, and M. Sawhney, *Improved bounds for Szemerédi's theorem*,
arXiv:2402.17995v2 (2024).

- https://arxiv.org/abs/2402.17995v2

Abstract and metadata were inspected. The result for k >= 5 is cited only to
separate the local claims here from global quantitative bounds. Its proof was
not audited as part of this work.

### 5. Contemporary finite-field benchmark, not a dependency

L. Milićević, *A quasipolynomial inverse theorem for the U^k(F_p^n) norm in the
high characteristic*, arXiv:2609.33733v1, submitted 27 September 2026.

- https://arxiv.org/abs/2609.33733v1

Abstract and metadata were inspected. It states a high-characteristic
quasipolynomial inverse theorem via Freiman multihomomorphisms. It is not used
in any proof here, and no comparison with all constants in that preprint is
claimed.

## Attribution ledger

**Standard ingredients, no priority claimed:** Fourier inversion and Parseval;
character orthogonality; correlation/ambiguity-function power identities;
quadratic refinements on finite abelian groups; probability affinity and
phase-preserving square-root lifting; the Motzkin–Straus extremal value;
triangle and Cauchy–Schwarz inequalities; elementary capped-mean selection.

**Proposed contributions developed and proved in this manuscript:**

1. The exact mixed, nonnegative-weight common-frequency formulation and its
   Section 8 consequence: one global quadratic phase on every translated
   window, with spectral-overlap and balanced-amplitude denominators.
2. The integrated offset-energy classification, explicit equality families,
   and constructive dimension-free stability estimates, including the optimal
   change from exponent 1/2 to 1/4 between character orders four and five.
3. The four-frequency obstruction to universal square-root function recovery,
   and the explicit locality, erasure/noise, and common-phase abundance
   consequences.

These descriptions identify what this work develops relative to the inspected
interface; they are not certificates of first publication in the entire
literature. The exact normalized cycle ceilings are special cases of the
classical graph theorem. The self-contained cycle equality and sharp-exponent
proofs may overlap broader stability theory not located by this scoped search.

**Not claimed:** a new end-to-end inverse theorem; an improved final Szemerédi
bound; completion of a previously unproved Proposition 8.1; a resolution of a
named global conjecture; optimal numerical stability constants; an optimal
balanced-indicator coefficient; complete independent peer review; or a verified
Lean development.

The eleven research questions are explicitly proposed questions. They are not
represented as a list of previously published open problems.

## Mathematical self-audit

- Normalized group averages and unnormalized Fourier sums are distinguished.
  The original derivative coefficient has the extra factor N.
- Forward and backward derivative signs were checked algebraically and by an
  independent direct-sum numerical test.
- The frequency is chosen after averaging over translates. The theorem gives
  a common polynomial but does not promise positive correlation on every
  individual translate.
- General weights are nonnegative. Negative weights would invalidate the
  triangle-inequality energy argument as used here.
- The core theorem is denominator-free. Quotient forms assume positive input
  energy; empty windows, zero functions, or nonpositive beta are handled
  separately when recovering the original formal proposition.
- The denominator for balanced functions is `sigma = E |f|^2`, not `||f||_2`.
  The bound `B sigma <= 4/27` is proved by one-variable optimization. Exact
  half-density is not asserted possible for odd N.
- Even groups use circle-valued quadratic refinements. The Z/2 example proves
  that the original classical polynomial target cannot always be retained.
- Order two counts a graph edge twice; order one is a sum of squares. The
  four-cycle has different equality geometry from every cycle of length >=5.
- The triangle-free identity separates two nonnegative terms and explicitly
  selects a positive-weight edge; no compactness or asymptotic constant is
  hidden in the stability proof.
- The stability construction includes outside-orbit mass and both endpoint
  and bipartition imbalances. The case of zero leaf mass is defined.
- The repaired function retains L2 norm, not necessarily the pointwise bound,
  a real-valued condition, or the balanced-indicator condition.
- The four-frequency example proves sharpness of exponents, not the leading
  constants in the upper modulus.
- Local-to-global conclusions retain the coverage factor |P|/|G|; a singleton
  counterexample shows why it cannot be discarded.
- The simultaneous-offset theorem claims existence of clique-supported
  maximizers, not that every maximizer is clique-supported.
- Numerical checks use tolerance 1e-10 and are labeled regression tests. Exact
  graph/product-group checks are finite validations, not exhaustive proofs of
  the unrestricted theorems.

All these are authorial self-checks. Independent mathematical review and formal
verification remain appropriate before treating the proposed refinements as
established repository infrastructure.
