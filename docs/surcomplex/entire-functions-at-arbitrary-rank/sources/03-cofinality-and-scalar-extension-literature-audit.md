# Literature and repository audit

Audit date: 21 September 2026.

## Primary mathematical sources consulted

**Bjorn Poonen, Maximally complete fields.** L'Enseignement Mathématique (2)
39 (1993), 87–106. Section 3 supplies the Hahn/Mal'cev–Neumann construction and
support facts; Corollary 4 supplies algebraic closedness for divisible value
group and algebraically closed residue field.

- https://doi.org/10.5169/seals-60414
- https://virtualmath1.stanford.edu/~conrad/Perfseminar/refs/poonencomplete.pdf

The scan's first article page and its printed page 96 were visually checked.
The last bibliography page also verifies the metadata for B. H. Neumann,
“On ordered division rings,” Trans. Amer. Math. Soc. 66 (1949), 202–252.
Neumann's original article was not read in full during this audit.

**William Cherry, Lectures on Non-Archimedean Function Theory.**
arXiv:0909.4509 (2009).

- https://arxiv.org/abs/0909.4509

The examined preparation and product material is a rank-one baseline using a
real-valued non-Archimedean absolute value. Its existence prevents any credible
claim that the present work introduces canonical products in non-Archimedean
analysis.

**William Cherry, Existence of GCD's and Factorization in Rings of
Non-Archimedean Entire Functions.** Contemporary Mathematics 551 (2011),
57–69; arXiv:1007.0984v2.

- https://arxiv.org/abs/1007.0984

The abstract explicitly describes the factorization results as well-known.
The rank-one unit and factorization statements were consulted as prior art.

**Brian Conrad, Lecture 6: More constructions with Huber rings.**
Stanford Number Theory Learning Seminar, 31 October 2014.

- https://virtualmath1.stanford.edu/~conrad/Perfseminar/Notes/L6.pdf
- https://virtualmath1.stanford.edu/~conrad/Perfseminar/

Section 6.2 and Example 6.2.1 explicitly distinguish positive valuation from
topological nilpotence in rank two. That phenomenon is established background,
not a discovery claimed by the article. The proposed unit theorem is the
precise necessary-and-sufficient coefficient criterion for the particular
restricted algebra, including value groups with no order unit.

**Olivier Bournez and Quentin Guilmant, Surreal fields stable under exponential
and logarithmic functions.** arXiv:2201.08199 (2022).

- https://arxiv.org/abs/2201.08199

Used for the surreal/Hahn normal-form setting and the context of set-sized
surreal subfields, not as a source of the present analytic classifications.
Gonshor's 1986 book is cited as a standard foundational reference; it was not
re-read in full during this audit.

## Repository comparison

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned snapshot: `aa846271b4dcae2c055b216126a87210292ec19b`.

The tree, root README, documentation catalogue, relevant report introductions,
and the rank-one report's entire-function and canonical-product material were
reviewed. Especially relevant:

- `docs/README.md`
- `docs/surcomplex/rank-one-berkovich/article.tex`, including its section on
  zero-free entire rigidity and its general canonical-product theorem.

The repository already distinguishes nonpolynomial fixed-workspace entire
series from all-surcomplex polynomial rigidity, and already develops rank-one
canonical products. The new article makes no claim to originate either point.
It targets the exact arbitrary-rank cofinality criterion, the restricted-unit
criterion, and the universal extension domain with zero conservation.

This was a targeted comparison, not an exhaustive line-by-line audit of every
report or every source manuscript. A connector keyword search returning no
matches was not treated as proof that a concept is absent.

## Priority boundaries

No matching statements of the main arbitrary-rank classification and universal
extension-domain package were located in the reviewed primary sources.
That observation is limited evidence, not an exhaustive worldwide literature
search or expert certification of novelty.

The article's proofs should be evaluated independently of the priority question.
They establish the claimed results only if their mathematical arguments and
identified standard inputs withstand review. The finite verification program
is a regression check, not an independent proof or formal certification.

No third-party papers or scans are redistributed in this archive.
