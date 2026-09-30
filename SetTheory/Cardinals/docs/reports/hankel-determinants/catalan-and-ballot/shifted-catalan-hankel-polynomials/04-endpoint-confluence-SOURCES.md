# Sources, provenance, and contribution boundary

Research date: 29 September 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:
`1ee53d57de253d16cdaad79d1f54bbd95d76d682`

Primary source path:
`SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/shifted-catalan-hankel-polynomials/article.tex`

Source article blob:
`e5a4d81408c80f0385ae66c26fbd11bba7dfdb09`

The directory's README and relevant portions of its article were retrieved
through the GitHub connector. The mathematical source was explicitly read
at the pinned commit. The source is a three-part, AI-assisted research report,
not a formally checked theorem library.

### Relevant source statements

Part II, Section 22 discusses fixed-parameter exponential-sector asymptotics
and expressly warns that those estimates need not remain uniform as roots
approach an endpoint or each other.

Part II, Section 24.4 asks for locally uniform repeated-root limits for
c_N = 2 + 2 cosh(tau/N), normalized by
(-1)^(tN) N^[t(t+1)/2], and the analogous left-endpoint limits with exponent
t(t-1)/2. It requests a confluent determinant treatment and error bounds.
The same subsection separately proposes collisions of distinct nonendpoint
roots on the N^-1 scale.

Part III concerns cyclotomic recurrence multiplicities for a single repeated
root. Its results are not claimed as contributions of this new article.

### Relation of this article to the source

This article resolves the **endpoint portion** of Section 24.4 and extends it
to simultaneous endpoint clusters with arbitrary fixed multiplicities and
internal collision patterns. It additionally establishes exact evenness in
the centered inverse size, the full first interaction coefficient, an
all-orders coefficient generator, a uniform effective error estimate, and
a sharp necessary-and-sufficient outward stability criterion.

The nonendpoint collision problem is not resolved here. The proofs use
classical moment and Christoffel identities, re-proved in the article; they
do not assume the repository's newer sector-degree or resonance theorems.
Thus the present theorem does not inherit an unexamined proof obligation
from those later repository claims.

## Primary external literature consulted

1. Christian Krattenthaler, *Hankel determinants of linear combinations of
   moments of orthogonal polynomials, II*, Ramanujan Journal 61 (2023),
   597–627. https://arxiv.org/abs/2101.04225
   The arXiv abstract and full PDF were consulted. This is the principal
   source for the classical fixed-size Christoffel identity, confluence,
   and recurrence background. Formula pages were also visually inspected.

2. Eugene Strahov and Yan V. Fyodorov, *Universal Results for Correlations of
   Characteristic Polynomials: Riemann-Hilbert Approach*, Communications in
   Mathematical Physics 241 (2003), 343–382.
   https://arxiv.org/abs/math-ph/0210010
   Used for broader characteristic-polynomial determinant and universality
   context, not as an assumed proof of the results in this article.

3. Gernot Akemann and Yan V. Fyodorov, *Universal random matrix correlations
   of ratios of characteristic polynomials at spectral edges*, Nuclear
   Physics B 664 (2003), 457–476.
   https://arxiv.org/abs/hep-th/0304095
   Used for hard-edge and ratio-of-characteristic-polynomials context.

4. NIST Digital Library of Mathematical Functions, Section 18.11,
   especially the Mehler–Heine-type formulas in 18.11(ii).
   https://dlmf.nist.gov/18.11
   Used to identify the classical one-variable endpoint-limit background.

## Novelty and evidentiary limits

The literature check was bounded, not exhaustive. A classical identity is
not relabeled as new simply because it is re-proved. The proposed contribution
is the explicit combined theorem package stated in this article, addressing
a precisely identified repository question. No global priority claim or
claim of having settled a famous external conjecture is made.

The 810 checks are recorded executions. Their number is not a count of
universal theorems. The exact all-parameter arguments are in the article;
the numerical diagnostics are not formal or interval certificates.
