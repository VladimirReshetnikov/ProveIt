# Provenance and verification boundaries

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Immutable snapshot inspected:
`6996fee43cc97b6c16351def7507d59a95bf62f0`

Retrieval date: 30 September 2026.

The GitHub connector was used to inspect the repository tree, retrieve source
files at this commit, and navigate with code search. Some code-search results
were indexed at an older commit (`5e0f4e05046bacda3c6ba2643f19b91aa632436b`).
Those results were treated as navigation, not as proof of the current snapshot.

Targeted readings:

- `Algebra/SurrealNumbers/README.md`, opening 130 lines: project scope,
  constructed ordered/real-closed field, research-status caveats, and links
  to the formalization ledger. The ledger and whole Lean library were not
  independently compiled or comprehensively audited for this article.
- `Analysis/Transseries/docs/series-and-transseries/Reversion_Beyond_Archimedean_Valuations/article.tex`:
  opening scope/methodology and finite-certificate discussion, including the
  repository's editorial cautions concerning antecedents and novelty. The
  connector's long-file response was truncated; no full-file proof audit is
  claimed. Its finite positive-grading theme is credited, while the grading
  lemma needed here is proved independently in the new article.
- Targeted searches for surreal polytopes and mixed-volume material were used
  to orient the topic. They do not establish that every possible antecedent in
  the large repository has been found.

No unrefereed advanced analytic claim from the repository is a prerequisite for
the new proofs. The foundational inputs are classical real-closedness and finite
polytope theory; the article gives its own scale, residue, genericity, and
reconstruction arguments.

## External literature

The bibliography records the sources used. In particular:

- Allamigeon–Katz–Strub, *Formalizing the Face Lattice of Polyhedra* (2020),
  open full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC7324146/
- Averkov–von Dichter–Richard–Soprunov, *Mixed volumes of zonoids and the absolute
  value of the Grassmannian*, arXiv:2404.02842v2 (1 November 2024),
  https://arxiv.org/html/2404.02842v2
  This version's proposed tropical direction motivates the article. Its
  historical statements about remaining open problems are not asserted to
  describe every development through September 2026.
- Branden–Huh, *Lorentzian polynomials*, arXiv:1902.03719 and Annals of Mathematics
  192 (2020). The pre-existing volume-polynomial and M-convex context is credited.
- Battistella–Kuehn–Kuhrs–Ulirsch–Vargas, *Buildings, valuated matroids, and tropical
  linear spaces*, arXiv:2304.09146; Journal of the London Mathematical Society
  109 (2024), e12850. Used to place lattice and valuated-matroid language in its
  established context.
- Ehrlich's surreal-field reference, Coste's semialgebraic notes, and Schneider's
  mixed-volume monograph are identified as classical foundational references.
  Their appearance in the bibliography is not a claim that every page of those
  works was read in this session.

The source search is targeted rather than exhaustive. The manuscript provides a
concrete valued-field answer to a proposed direction; it does not assert that
all its formulations are previously unpublished or independently certified.

## New artifacts and checks

The LaTeX article, Python audit program, and supporting documentation were
created for this request. The default program was executed successfully; the
actual results are in `verification.json`. The PDF was built with pdfLaTeX and
latexmk and rendered to page images with Poppler for visual inspection.

Exact program arithmetic is the finite Laurent polynomial ring
Q[eta^+-1, epsilon^+-1] with exponent pairs ordered lexicographically. This is
not an implementation of the entire surreal field. All random data are generated
from the explicit seed recorded in the JSON report.

No source code was pushed to GitHub and no repository was modified.
