# Research status and source check

Date of source check: 19 September 2026.

## Source of the open direction

Isa Vialard, *Ordinal Measures of the Set of Finite Multisets*, MFCS 2023,
LIPIcs 272, article 87. Official version:
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2023.87

Relevant locations: Definition 3.3, Theorem 3.4, Proposition 4.1,
Theorem 4.5, Corollary 4.7, and the conclusion on printed page 87:11.

Isa Vialard, *Measuring well quasi-orders and complexity of verification*,
PhD thesis, Universite Paris-Saclay, defended 3 July 2024. Author-hosted
version consulted:
https://isavialard.github.io/home/mwqo.pdf

Relevant locations in this version: Section 5.4, printed pages 74--76;
Theorem 5.4.8(3), already giving the both-limit product case; conclusion
printed page 109, explicitly asking about compositional friendly-type
computation. Hosted versions have different pagination.

The older arXiv version, https://arxiv.org/abs/2302.09881, uses the terminology
"maximal safe order type." The report uses the published friendly definition,
not a claim based on an omitted prepublication statement.

The author publication list, https://isavialard.github.io/home/, was also
consulted. Exact-phrase searches for "friendly order type," "maximal safe
order type," product, finite, and incomparability did not locate the exact
formulas developed here. Search results were incomplete and sometimes
irrelevant; this is not an exhaustive priority search.

## Claims made

- Proofs of the finite component formula and the product component lemma.
- A proved specific obstruction to product compositionality from (o,h,w,f).
- A proved mixed-product formula relative to explicitly cited background.
- A complete classification of finite Cartesian products of ordinals.
- Reproducible finite and symbolic computational checks, with exact scope.

## Claims not made

- No proof that these exact results have never appeared elsewhere.
- No claim that the both-limit case or the binary sum identity is new.
- No claim that Vialard stated the exact restricted questions in this report.
- No claim that the unrestricted compositional research program is solved.
- No claim of peer review, Lean verification, or independent expert review.
- No inference of transfinite ranks by taking suprema of finite-grid ranks.
- No exhaustive minimality claim for the counterexample.

## Recommended mathematical audit points

The finite component upper bound distinguishes points that are selected
from points removed incidentally. The product cut requires every L point
below every U point, not just that L is a downset. The finite upper-tail
lemma needs T upper and |T| equal to the final finite coefficient. The
mixed theorem excludes the single-chain case. The N=1 corner uses
monotonicity without any claimed legal corner selection. Right predecessor
must not be confused with left ordinal subtraction. The hereditary CNF
implementation is restricted to ordinals below epsilon_0; the theorem is not.
