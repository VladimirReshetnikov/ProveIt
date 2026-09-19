# Research status and source audit

## What is established in the manuscript

1. **Finite component formula:** friendly order type is |P|-c_perp(P).
   A forest-potential proof gives the upper bound; connected-prefix linear
   extensions give the matching lower bound and an explicit witness.
2. **Graph interpretation:** the same value is graphic-matroid rank and
   incidence-matrix rank over every field. This is equality of numerical ranks,
   NOT identification of the friendly-sequence tree with a matroid.
3. **Finite substitution:** nontrivial incomparability components of the index
   merge their nonempty fibers; isolated index points retain internal fiber
   components.
4. **Product structure:** a Cartesian product of two nontrivial posets has a
   unique nontrivial incomparability component, plus at most its least and
   greatest points as isolated components. For finite factors this gives
   |A||B|-1-b(A)b(B)-t(A)t(B).
5. **Well-ordered sums:** friendly order type is the ordinary ordinal sum of
   the friendly order types of the blocks. All wpos with finite incomparability
   components therefore have an explicit ordinal-sum evaluation.
6. **Limits of extension:** omega disjoint-union omega and (omega+1)
   disjoint-union omega have isomorphic abstract incomparability graphs but
   friendly order types omega*2 and omega*2+1, respectively. Connectedness and
   maximal order type together also do not determine the infinite value.

Each statement has a proof in article.tex/article.pdf. These are unrefereed
mathematical proofs, not formally verified derivations.

## External dependency

The general identity width(M^r(P)) = omega^(friendly_order_type(P)) is due to
Isa Vialard. It is Theorem 3.4 of the published 2023 paper below. The present
article applies it and does not claim to supply its general proof.

The binary ordinal-sum rule was already published. The article records and
proves the extension to arbitrary well-ordered sums and combines it with the
finite component formula.

## Problem provenance

The conclusion of Vialard's 2023 paper asks how friendly order type relates to
other concepts and whether it can be computed compositionally for more
operations. The 2024 doctoral thesis repeats this research direction.
The finite structural problem chosen for this article is a specialization of
that program, not a separately documented named conjecture.

## Primary sources inspected

1. Isa Vialard, “Ordinal Measures of the Set of Finite Multisets,” MFCS 2023,
   LIPIcs 272, article 87, pp. 87:1–87:15.
   DOI: https://doi.org/10.4230/LIPIcs.MFCS.2023.87
   Landing page:
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2023.87
   Relevant parts: Definitions 1.6 and 3.3; Theorem 3.4; Proposition 4.1;
   conclusion on printed page 87:11.

2. Isa Vialard, “Measuring well quasi-orders and complexity of verification,”
   doctoral thesis, Université Paris-Saclay, 2024.
   Author copy: https://isavialard.github.io/home/mwqo.pdf
   Relevant parts: Sections 5.3–5.4 and conclusion, printed pp. 109–110.
   This is the 124-page author-hosted version. Other circulating thesis copies
   have different pagination; the article's references concern this copy.

3. Sergio Abriola, Simon Halfon, Aliaume Lopez, Sylvain Schmitz,
   Philippe Schnoebelen, and Isa Vialard, “Measuring well quasi-ordered finitary
   powersets,” arXiv:2312.14587v2, 17 July 2024.
   https://arxiv.org/abs/2312.14587
   Used for research context, not the proofs of the new formulas.

The author's current publication page was also checked:
https://isavialard.github.io/home/

## Search scope and priority

Searches on 19 September 2026 included:

- "friendly order type"
- "friendly order type" "components"
- "friendly order type" finite posets
- "multiset" "width" "incomparability" "components"

No statement of the finite component formula was located in the materials
inspected. Search coverage was targeted rather than exhaustive. There may be
unindexed literature, equivalent formulations, subsequent work, or informal
knowledge not found by the search. Priority is therefore unverified.

## Computational status

All actual audit counts and outputs are provided. No n=8 exhaustive run is
claimed. Product checks above nine product points compare graph structure,
not exact residual ranks. Finite computations are supporting checks and are
not evidence for the transfinite induction beyond the proof itself.

## Questions not answered

- A general evaluation formula for arbitrary infinite connected wpos.
- A classification of all supports of friendly bad sequences, as opposed to
  their maximum size for finite bases.
- A formal proof-assistant verification or external referee assessment.
- A bibliographically certified claim of first discovery.
