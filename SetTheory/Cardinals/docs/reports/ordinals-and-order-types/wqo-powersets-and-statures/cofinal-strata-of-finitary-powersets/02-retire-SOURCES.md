# Source record and research positioning

Prepared 24 September 2026. This is a scoped source review, not an exhaustive
literature or repository audit.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9

Relevant package:
SetTheory/Cardinals/docs/reports/ordinals-and-order-types/
wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets/

Read via the connected GitHub interface:
- README.md: uniform height formula; nonuniform maximal-order-type scope;
  explicit exclusion of a nonuniform height claim; persistent-coordinate
  counterexample; bibliography and implementation description.
- PROOF_AUDIT.md: the exact scope and dependencies of the earlier result;
  explicitly emphasizes the equal-fibre requirement in its height proof.
- references.bib: primary literature pointers, checked separately online.

The repository's reports index and large-cardinal synthesis were also sampled
in selecting the research direction. They are not logical dependencies.
The nonuniform theorem in this package is proved without assuming the
correctness of any unrefereed repository theorem.

The article does not claim that the entire repository was checked line by
line. Its targeted comparison is supported by explicit scope statements in
the named package. A uniform theorem is reproved as a special case; it is not
relabeled as new.

## Primary literature consulted

1. S. Abriola, S. Halfon, A. Lopez, S. Schmitz, Ph. Schnoebelen, I. Vialard,
   Measuring well-quasi-ordered finitary powersets.
   https://arxiv.org/abs/2312.14587v2
   https://arxiv.org/html/2312.14587v2
   Version 17 July 2024. Definitions and non-functionality context in
   Sections 2--3; compositional elementary-WQO results in Section 5;
   extension programme in Section 6. The template's placeholder DOI is not
   used as a real publication identifier.

2. M. Džamonja, S. Schmitz, Ph. Schnoebelen,
   On Ordinal Invariants in Well Quasi Orders and Finite Antichain Orders.
   https://arxiv.org/abs/1711.00428
   Background survey; 2020 book-chapter publication and updated preprint.
   No maximal-order-type lexicographic-product formula from this source is
   required by the current proof.

3. I. Vialard, On maximal order type of the lexicographic product,
   Logic Journal of the IGPL 33(4), jzaf051 (2025).
   https://doi.org/10.1093/jigpal/jzaf051
   https://academic.oup.com/jigpal/article/33/4/jzaf051/8205767
   Publisher metadata checked: published 17 July 2025, sole author Isa
   Vialard. Cited for the published article's stated scope, not used as a
   mathematical input. Earlier preprint versions have different authorship
   and an author disagreement notice; they must not be silently conflated
   with the published bibliographic record. No disputed formula is needed
   in this package.

## Targeted searches and status

Searches included the exact papers' titles and combinations of
"finitary powersets", "height", "lexicographic", "ordinal", and
"maximal antichains". They located the papers above and classical maximal-
antichain literature, but did not establish a prior occurrence of the exact
retirement-path formula. Search non-discovery is not proof of novelty.

The claim made is a complete proof of a specific nonuniform height formula
that fills the named repository report's expressly excluded ordinal-chain
case, together with its finite algorithm and limit-fibre extension.
It is not presented as a certified solution of the full published extension
programme or a theorem for arbitrary WPO fibres.
