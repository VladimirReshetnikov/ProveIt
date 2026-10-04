# Source provenance and scope of inspection

Prepared 3 October 2026. This is a bounded source audit, not an exhaustive
novelty or priority certification.

## Elliot Glazer

Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699v1,
submitted 22 November 2023.

- https://arxiv.org/abs/2311.13699
- https://arxiv.org/pdf/2311.13699

The published research text, rather than an inferred personal profile, fixes
the research intersection. Relevant portions are Corollary 1 on page 3,
Theorem 2 on page 3, and Questions 1 and 2 on page 8. The paper's obstruction
to continuous addition assumes Borel multiplication and arithmetic axioms.
The present article instead imposes local compactness on a signed additive
group and Borel order, while dropping regularity of multiplication and
induction. Neither the full general Polish case nor Glazer's reverse-
mathematical Question 1 is claimed solved here.

## ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:

883e0b3b22263bd9d92fdbbf10376ca4b652b862

Inspected through the GitHub connector: repository tree and root README,
plus the following project guides:

- https://github.com/VladimirReshetnikov/ProveIt/blob/883e0b3b22263bd9d92fdbbf10376ca4b652b862/Logic/PresburgerArithmetic/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/883e0b3b22263bd9d92fdbbf10376ca4b652b862/Algebra/SurrealNumbers/README.md

The Presburger guide describes the existing Cooper-elimination and decision
procedure interfaces. The surreal guide supplies the project context and
separates checked constructions from AI-assisted research reports. We did
not build this repository, execute its Lean/Rocq audits, or independently
certify its global formalization claims. The current article's mathematical
proofs do not rely on the repository's stronger unrefereed assertions.

## Classical mathematical inputs

1. N. H. Asmar and S. J. Montgomery-Smith, *Hahn's Embedding Theorem for
   orders and harmonic analysis on groups with ordered duals*, Colloquium
   Mathematicum 70 (1996), 235-252.
   https://doi.org/10.4064/cm-70-2-235-252
   The publisher record and paper text were inspected, especially Section 3
   on measurable orders. These results are classical inputs, not new claims.

2. E. Hewitt and S. Koshi, *Orderings in locally compact Abelian groups and
   the theorem of F. and M. Riesz*, Mathematical Proceedings of the Cambridge
   Philosophical Society 93 (1983), 441-457.
   Bibliographic attribution was checked through the Asmar--Montgomery-Smith
   paper. This older article was not independently read in full.

3. Remy van Dobben de Bruyn, *Locally compact abelian groups*, notes for the
   Intercity Geometry Seminar on condensed mathematics, 2022.
   https://webspace.science.uu.nl/~dobbe012/doc/LCA.pdf
   The principal structure statement on page 4 was inspected in text and as
   a rendered page. This is the principal imported structure theorem; the
   article does not pretend to reprove the entire LCA structure theory.

4. Raf Cluckers, *Presburger sets and p-minimal fields*, Journal of Symbolic
   Logic 68 (2003), 153-162.
   https://arxiv.org/abs/math/0206197
   https://arxiv.org/pdf/math/0206197
   Section 1.1 gives the Z-group language and quantifier-elimination context.
   The present article supplies its own finite-witness argument and does
   not claim classical Presburger elimination as a new result.

5. Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts
   in Mathematics 156, Springer, 1995.
   https://doi.org/10.1007/978-1-4612-4190-4
   Publisher metadata checked. Cited for standard Polish-space background.
   The automatic-continuity argument needed here is supplied in the article.
   No claim is made to have reread the whole book during this project.

## Earlier user-library companion manuscripts

Retrieved using the Files tool to avoid presenting prior constructions as
new work:

- polish_presburger_glazer.pdf, *Polish Presburger Arithmetic inside the
  Omnific Integers*, 3 October 2026. Its explicit real and Baire-space models,
  low-complexity definable relations, and example-specific multiplication
  obstructions are acknowledged as earlier companion results.
- glazer_proveit_article.pdf, *Borel Presentations and Support Barriers in
  Omnific Arithmetic*, 3 October 2026. Its Hahn-support questions provide
  neighboring context but are not prerequisites for the present proofs.

Both are unrefereed AI-assisted manuscripts. Only relevant retrieved
content was used; no claim is made to have independently audited each
entire companion document. Their bytes are not redistributed in this ZIP.

## Contribution and verification boundary

Proposed contributions for independent review: the general algebraic
amplification package, the ordered-ring local-compactness obstruction with
no multiplication-regularity hypothesis, the pointed Presburger-group
classification and positive-cone threshold, the Borel-scalar subring theorem,
and the stated omnific applications and sharpness examples.

Priority for these exact formulations remains unestablished. Complete proofs
are included, but there has been no external peer review or proof-assistant
verification. Only the finite exact-arithmetic checks and PDF build were
executed. Search-result absence is not evidence that a theorem is new.
