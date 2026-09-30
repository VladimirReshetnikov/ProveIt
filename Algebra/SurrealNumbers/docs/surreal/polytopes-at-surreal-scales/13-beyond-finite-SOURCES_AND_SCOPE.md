# Sources and scope

Consultation date: 30 September 2026.

## Repository consultation

Repository: https://github.com/VladimirReshetnikov/ProveIt

The connected GitHub interface was used. Search-result file URLs were pinned
to commit `6996fee43cc97b6c16351def7507d59a95bf62f0`. The relevant README files
were fetched separately from the default branch; this is not a claim that
all consultation took place in a single simultaneously pinned checkout.

1. `Algebra/SurrealNumbers/README.md`, returned blob
   `cf63fc5ff9ca9d8877e90f8e69ec34e6ded19d23`.
   Used for the project's scope, the distinction between field foundations
   and unrefereed research reports, and the existence of a formalization ledger.
2. `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-fields-across-universes/README.md`,
   returned blob `bfb819fc0cff4c42961a2048d21845af5a9522fd`.
   Used for motivation concerning old fields, omitted cuts, and saturation.
   Its README explicitly does not claim Lean verification of that report.

Other search results and a groups/lattices README were inspected while
selecting the direction, but no statement from them is a proof dependency.
The repository's research claims were not assumed merely because they
appeared in a README. No source file was modified, no repository build was
performed, and no Lean axiom audit was run.

## Primary literature and the role of each source

### Finite ordered-field convexity

Martin Dvorak and Vladimir Kolmogorov, *Duality theory in linear optimization
and its extensions: formally verified*, Annals of Formalized Mathematics 2
(2026), no. 1, DOI 10.46298/afm.14253.
Consulted https://arxiv.org/html/2409.08119v3 (version date 6 March 2026).
The abstract and introductory theorem statements explicitly concern finite
Farkas and duality over linearly ordered fields. Its separately adjoined
infinite values are not identified with surreal numbers.

A. Charnes and W. W. Cooper, *The strong Minkowski–Farkas–Weyl theorem for
vector spaces over ordered fields*, PNAS 44 (1958), no. 9, 914–916,
DOI 10.1073/pnas.44.9.914, is a historical reference. The publisher page was
access-restricted during a final metadata check. No new argument depends
on having obtained the full publisher text; the modern ordered-field
Farkas source and the mathematical finite-elimination argument are explicit.

### Surreal fields and saturation

Philip Ehrlich, *The absolute arithmetic continuum and the unification of
all numbers great and small*, Bulletin of Symbolic Logic 18 (2012), no. 1,
1–45, DOI 10.2178/bsl/1327328438. The official issue record confirms the
2012 date, title, and pagination:
https://www.math.ucla.edu/~asl/bsl/1801-toc.htm
An author-uploaded text was also consulted during research. A legacy
PostScript link from the official issue could not be fetched. The manuscript
supplies its own relative-embedding and small-type-realization proofs.

Lou van den Dries and Philip Ehrlich, *Fields of surreal numbers and
exponentiation*, Fundamenta Mathematicae 167 (2001), 173–188,
DOI 10.4064/fm167-2-3; erratum 168 (2001), 295–297.
The publisher's article record was consulted. The manuscript does not use
the delicate birthday/product-support estimates corrected by the erratum.

### Classical exposure: explicit prior credit

J. E. Martínez-Legaz, *Lexicographical characterization of the faces of
convex sets*, Acta Mathematica Vietnamica 22 (1997), no. 1, 207–211.
Official PDF: https://math.ac.vn/uploads/files/9701207.pdf
All five pages were available as parsed text; the page containing Definition
3 and Proposition 4 was also inspected as a rendered image.

This source ALREADY establishes the following:
- lexicographical exposure of every nonempty proper real finite-dimensional face;
- the degree of non-exposedness;
- the codimension bound;
- the relationship with chains of relative exposed faces.

These are not claimed as discoveries in the present package. The polynomial
infinitesimal degree is identified with that old invariant. The sharp
recursive family is proved directly here, without a priority assertion.

Valentin V. Gorokhovik, *Characterizations of Faces of Convex Sets in
Infinite-dimensional Vector Spaces*, arXiv:2506.08742v1 (2025):
https://arxiv.org/html/2506.08742v1
Used to verify the prior face-characterization context and to distinguish
infinite-dimensional generalizations from the present change of scalar
field and presentation size. No open question in that paper is claimed solved.

## Priority and proof scope

The geometric combination proposed here is finite V/H double compression,
small-family exposure and finite active faces, polar non-generation, and
the complete moment-hull/polar face classifications. These have written
proofs in the article. The compactness mechanism is standard. The searches
were targeted, not exhaustive, and do not establish first publication or
independent novelty of each consequence.

No claim is made about arbitrary proper-class generator/row families,
arbitrary birthday cutoffs, omitted-cut old surreal fields, infinite
convex combinations, or the full semialgebraic extension of a real body.
