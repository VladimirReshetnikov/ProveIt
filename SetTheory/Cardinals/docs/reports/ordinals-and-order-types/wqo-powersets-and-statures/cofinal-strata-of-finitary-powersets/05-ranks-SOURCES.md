# Sources and provenance

Research and access date: 24 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`.

Primary package:

`SetTheory/Cardinals/docs/reports/ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets/`

Primary package URL:
https://github.com/VladimirReshetnikov/ProveIt/tree/e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets

Read through the GitHub connector: repository tree, Cardinals README, reports
README, package README, and relevant contiguous portions of article.tex.
The article source's blob SHA is
`57498d1bdc438f469df33d296095edc2b8a5a707`.

The package explicitly excludes a nonuniform height formula. Its section
“Boundaries and failed extensions” gives the isolated omega^2 coordinate
beside two successive omega coordinates and identifies persistence as the
obstruction. A repository content search for nonuniform height returned this
package, its audit and example outputs, and its manifest description, rather
than a later mixed-height solution. This is a targeted check, not an audit of
every repository file.

The new article reproduces the essential support/frontier facts with proofs
and does not assume the correctness of the repository's unrefereed theorems.
No repository content was changed, and no third-party article PDFs are
redistributed in this archive.

## Primary literature checked

1. Sergio Abriola, Simon Halfon, Aliaume Lopez, Sylvain Schmitz, Philippe
   Schnoebelen, Isa Vialard. *Measuring well quasi-ordered finitary powersets*.
   arXiv:2312.14587v2, 17 July 2024.
   https://arxiv.org/abs/2312.14587
   https://arxiv.org/html/2312.14587v2

   Section 6 asks about enlarging the elementary family while retaining
   computability of ordinal invariants. The final-page question was inspected
   in the PDF as well as the HTML. The paper distinguishes height, width, and
   maximal order type and discusses nonfunctionality of powerset invariants.
   Its author's current publication list reports acceptance in Mathematical
   Structures in Computer Science; the article cites the precise arXiv version
   actually used, not invented journal volume/page metadata.
   https://isavialard.github.io/home/

2. Jacob Hilton. *The topological pigeonhole principle for ordinals*.
   arXiv:1410.2520v4, 12 July 2016.
   https://arxiv.org/abs/1410.2520
   https://arxiv.org/html/1410.2520v4

   Section 2.5, Theorem 2.20, records the finite Milner–Rado formula. It is used
   as historical attribution for a classical benchmark. The appendix gives a
   separate direct derivation of the product-height formula used in tests.

3. Isa Vialard. *On maximal order type of the lexicographic product*.
   Logic Journal of the IGPL 33(4), jzaf051 (2025).
   DOI: 10.1093/jigpal/jzaf051.
   https://academic.oup.com/jigpal/article/33/4/jzaf051/8205767

   The published article confirms that the neighboring maximal-order-type
   question for lexicographic products is not to be advertised as newly
   solved here. Our target is height after finitary powerset and nonuniform
   finite-poset gluing. No formula from this paper is used in our proof.

## Classical background cited in the article

D. Schmidt (1981), “The relation between the height of a well-founded partial
ordering and the order types of its chains and antichains,” Journal of
Combinatorial Theory, Series B 31(2), 183–189.

M. Džamonja, S. Schmitz, Ph. Schnoebelen (2020), “On ordinal invariants in well
quasi orders and finite antichain orders,” in *Well Quasi-Orders in Computation,
Logic, Language and Reasoning*, Trends in Logic 53, Chapter 2, pp. 29–54.

Bibliographic details were cross-checked against the primary Abriola et al.
article and its references. The present proof does not invoke an unexamined
special theorem from these sources.

## Novelty-search limit

Targeted searches combined “finitary powerset”, “height”, “lexicographic”,
“nonuniform”, “persistent coordinates”, and ordinal-product terminology.
They did not identify the retirement formula proved here. Such searches do
not establish a negative statement about the whole literature, nor prove
priority. Accordingly, the manuscript presents its explicit proof and its
extension of the pinned repository boundary, while leaving priority open to
specialist review.
