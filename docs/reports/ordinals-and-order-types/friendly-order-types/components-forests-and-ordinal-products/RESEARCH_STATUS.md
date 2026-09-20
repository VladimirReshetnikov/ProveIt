# Research status and source check

Date of source check: 19 September 2026.

This report merges two independently produced research reports, originally
delivered as `cartesian-products-of-ordinals` and
`incomparability-components-and-forests`. Both carried out their own
literature audits on the same date and against the same sources, and both
reached the same conclusion. Where their statements of status differed in
strength, the more cautious statement is kept below.

## Source of the open direction

Isa Vialard, *Ordinal Measures of the Set of Finite Multisets*, MFCS 2023,
LIPIcs 272, article 87. Official version:
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2023.87

Relevant locations: Definition 3.3 (the invariant o_perp), Theorem 3.4 (the
multiset-width transfer), Proposition 4.1(1) (the binary ordinal-sum law),
Definition 4.4 (the alternative friendly-subset characterization),
Theorem 4.5, Corollary 4.7 (limit saturation), and the conclusion on printed
page 87:11.

Isa Vialard, *Measuring well quasi-orders and complexity of verification*,
PhD thesis, Universite Paris-Saclay, defended 3 July 2024. Author-hosted
version consulted:
https://isavialard.github.io/home/mwqo.pdf

Relevant locations in this version: Definition 5.3.2 and Theorem 5.3.3
(the friendly definition and the multiset-width transfer, printed p. 74);
Section 5.4, printed pages 74--76; Theorem 5.4.8(3), already giving the
both-limit product case; conclusion printed page 109, explicitly asking about
compositional friendly-type computation and a further structural
interpretation. Hosted versions have different pagination; theorem numbers
and the cited author-hosted version identify the results used here.

The older arXiv version, https://arxiv.org/abs/2302.09881, uses the terminology
"maximal safe order type." The report uses the published friendly definition,
not a claim based on an omitted prepublication statement. General infinite
formulas not used in the proofs are deliberately not imported from earlier
source versions.

The author publication list, https://isavialard.github.io/home/, was also
consulted. Exact-phrase searches for "friendly order type," "maximal safe
order type," product, finite, and incomparability did not locate the exact
formulas developed here, nor a later treatment of the component formula.
Search results were incomplete and sometimes irrelevant; this is not an
exhaustive priority search.

Dzamonja, Schmitz and Schnoebelen, *On Ordinal Invariants in Well Quasi
Orders and Finite Antichain Orders*, Trends in Logic 53 (2020), 29--54, is
cited only for the standard rank conventions.

## Claims made

- Proofs of the finite component formula, the graphic-matroid reading, the
  classification of maximum friendly subsets, and the forest certificates.
- Proofs of the product component lemma, the finite Cartesian-product
  formula (by two independent routes, both retained), the lexicographic
  substitution law, and the finite disjoint-union identity.
- A proved specific obstruction to product compositionality from (o,h,w,f),
  together with the weaker three-element and extremal separations.
- A proved mixed-product formula relative to explicitly cited background.
- A complete classification of finite Cartesian products of ordinals.
- The transfinite sum law, the evaluation of every wpo with finite
  incomparability components, the realization of every ordinal at ordinary
  width two, and the infinite graph-only obstruction.
- An exact bivariate generating function and fixed-rank counting polynomials
  for naturally labelled posets.
- Reproducible finite and symbolic computational checks, with exact scope.

## Claims not made

- No proof that these exact results have never appeared elsewhere. The
  elementary ingredients may be known in other terminology.
- No claim that the invariant, the multiset-width transfer, the both-limit
  case, the binary sum identity, or the finite disjoint-union special case
  is new; all of these are Vialard's or consistent with published formulas.
- No claim that Vialard stated the exact restricted questions in this report,
  or that the literature labels the finite statement as a named conjecture.
- No claim that the unrestricted compositional research program is solved.
  A wpo may have infinite incomparability components, and the ranks of those
  connected pieces are not computed here.
- No claim of peer review, Lean verification, formal verification, or
  independent expert review.
- No inference of transfinite ranks by taking suprema of finite-grid ranks.
- No exhaustive minimality claim for the counterexample.
- No conjectural formula for infinite connected wpos on the strength of the
  finite experiment.

## Recommended mathematical audit points

The finite component upper bound distinguishes points that are selected from
points removed incidentally. A friend must be present in the current
residual, not merely in the original poset. Isolated vertices of the
incomparability graph count as components; the empty poset has f = 0 and its
multiset order has width 1 = omega^0, not 0. Protected roots must be minimal
*inside their component*, not necessarily globally minimal. Forest roots of a
later component may be removed while an earlier component is processed; they
remain roots of the certificate forest but not necessarily elements of the
final residual. Empty substitution fibers require deleting their base
vertices and taking the induced base order first. The product formula
requires both factors to have at least two elements, and the endpoint flags
record global least and greatest elements, not minimal and maximal ones. The
outer addition in a transfinite sum is ordinal addition, not natural or
cardinal addition, taken in the displayed order. The product cut requires
every L point below every U point, not just that L is a downset. The finite
upper-tail lemma needs T upper and |T| equal to the final finite coefficient.
The mixed theorem excludes the single-chain case. The N=1 corner uses
monotonicity without any claimed legal corner selection. Right predecessor
must not be confused with left ordinal subtraction. The hereditary CNF
implementation is restricted to ordinals below epsilon_0; the theorem is not.

Two adjacent cautions must be kept distinct. Section 9.3 warns that numerical
suprema of finite grids do not compute a transfinite rank - a caution about
method. Proposition 10.6 proves that on infinite wpos the isomorphism type of
the incomparability graph does not determine the invariant at all - a theorem
about what such data could contain. They are different statements and the
article separates them explicitly.

## Verification limitations

The two finite engines are genuinely independent implementations, and the
residual dynamic program uses only the defining recursion, never the
component formula or the non-cut lemma. Their agreement is a finite test over
explicit bounded ranges, not a proof for all finite orders and not a
verification of any transfinite statement. The corner simulations replace
limit cutoffs by the integer two and test only move legality, witnesses,
counts and residuals. The ordinal module implements the proved formulas
symbolically; it is not an independent oracle for the rank of an infinite
tree. The generating-function script is a consistency check on saved counts,
not an independent enumeration. Certificates are algorithmically verified,
but the English proofs have not been formalized or externally refereed.
