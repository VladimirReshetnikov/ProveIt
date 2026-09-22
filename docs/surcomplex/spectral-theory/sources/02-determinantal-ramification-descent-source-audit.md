# Source review and novelty boundary

Review date: September 21, 2026.

## Repository

Repository: VladimirReshetnikov/Surreal
Pinned revision: aa846271b4dcae2c055b216126a87210292ec19b

Read through the GitHub connector:
- Repository README.
- Documentation README/catalogue.
- Full docs/surcomplex/spectral-theory/README.md.
- Opening and selected visible material of the differential-equations article.

The spectral package already states real-closed-field spectral and SVD
results, determinantal singular scales, positive Cauchy--Binet, and spectral
perturbation results. Its stated Hahn workspaces use divisible groups. It
explicitly limits claims of support-controlled parameter-dependent eigenbases.
This article does not present that earlier material as a new discovery.

The review was targeted. It did not inspect every line of every source
manuscript or every Lean module. Missing keyword matches were not treated
as proof of absence.

## Primary literature

- Adkins (1991), Normal matrices over hermitian discrete valuation rings:
  the author's LSU institutional abstract and publication metadata were read.
- Keller and Ochsenius (1995), A spectral theorem for matrices over fields of
  power series: the full publisher-hosted PDF was read. The pages specifying
  the iterated Laurent and infinite direct-sum exponent groups were also
  inspected as rendered images. These are important published predecessors.
- Parusinski and Rond (2020), Multiparameter perturbation theory of matrices
  and linear operators: the original arXiv abstract was read. Relevant
  formal-block results were cross-checked in Parusinski and Rainer's survey.
  The original older preprint's full HTML was not available through the tool;
  the block-lifting proof used in the article is supplied explicitly.
- Dai, Liang, Lu, and Zhi (2026), arXiv:2602.08313v1: the full available HTML,
  its formal ring assumptions, diagonalization criterion, and counterexamples
  were consulted. It is described as a preprint, not as a journal publication.
- Higman (1952) and Neumann (1949): primary publication/bibliographic records
  were checked. The exact word and support lemmas needed here are reproved.
- Gonshor (1986): the established surreal normal-form and field framework is
  imported and attributed; the book's publisher record was checked, not the
  whole book re-read.

## What is offered as potentially new

The primary candidate contribution is the exact arbitrary-rank law relating
minor valuations to the entry field and degree of a principal matrix root,
together with the assertion that the trace is always a primitive generator.
The support-preserving spectral construction provides the nondivisible-field
engine for this law. Its generic mechanism has strong earlier precedents.

No source encountered in this targeted review stated the precise combined
determinantal/primitive-trace formulation. This is not an exhaustive novelty
search, a certification of priority, or an independent referee report.
