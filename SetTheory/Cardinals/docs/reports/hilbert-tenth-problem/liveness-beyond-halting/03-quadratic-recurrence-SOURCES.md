# Source provenance

Inspected on 30 September 2026. Repository reads used the GitHub connector;
public scholarly records and preprints were checked through web retrieval.
No local repository build or independent source axiom audit was run.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `4e128356d0ef75308be8ed405d89aea2ffdb8a57`

Commit timestamp returned by GitHub: `2026-09-30T18:47:30Z`.

Directly inspected relevant sources:

1. `Computability/HilbertTenthProblem/README.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/4e128356d0ef75308be8ed405d89aea2ffdb8a57/Computability/HilbertTenthProblem/README.md
   The initial README read was at `main`; the pinned tree and subsequent
   source read establish the snapshot used. The README reports MRDP and
   finite-trace infrastructure. These reports are not an independent build
   verification by this manuscript.

2. `Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`
   https://github.com/VladimirReshetnikov/ProveIt/blob/4e128356d0ef75308be8ed405d89aea2ffdb8a57/Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean
   This pinned source was read in full. Relevant declarations:
   `boundedForall_dioph`, `exactIter_dioph`, `existsExactIter_dioph`.
   They concern bounded universals and finite exact iteration/reachability.

The broader root README and subject directories were inspected for context.
Unrelated repository claims are not used as mathematical premises here.

## Classical computation

J. C. Shepherdson and H. E. Sturgis, "Computability of recursive functions,"
Journal of the ACM 10(2), 1963, 217-255.
DOI: https://doi.org/10.1145/321160.321170
JACM bibliographic index: https://projects.csail.mit.edu/jacm/Authors/sturgishe.html

The publication identity and bibliographic data were checked. A direct ACM
full-text request returned HTTP 403; the manuscript does not purport to quote
or audit its full proof. The specific stack/counter simulation used here is
explained within the article.

## Infinite recurrence and fairness

David Harel, "Recurring Dominoes: Making the Highly Undecidable Highly
Understandable," North-Holland Mathematics Studies 102, 1985, 51-71.
DOI: https://doi.org/10.1016/S0304-0208(08)73075-5
Author-institution record:
https://weizmann.elsevierpure.com/en/publications/recurring-dominoes-making-the-highly-undecidable-highly-understan-2/

David Harel, "Effective Transformations on Infinite Trees, with Applications
to High Undecidability, Dominoes, and Fairness," Journal of the ACM 33(1),
1986, 224-248.
DOI: https://doi.org/10.1145/4904.4993
Author-institution record and abstract:
https://weizmann.elsevierpure.com/en/publications/effective-transformations-on-infinite-trees-with-applications-to-/

These records establish that the broad recurrence/tree/fairness connection
predates this article. The manuscript gives its own specific reductions and
does not claim an exhaustive comparison with every theorem in the full papers.

## Analytical hierarchy and related tiling results

Olivier Finkel, "Highly Undecidable Problems about Recognizability by Tiling
Systems," inspected preprint arXiv:0811.3704 (2008).
https://arxiv.org/abs/0811.3704
https://arxiv.org/pdf/0811.3704

The preprint's parsed text, hierarchy section, introduction, and bibliography
were available. Web screenshot requests failed with a cache error, so no
claim in this manuscript relies on inspection of an embedded chart or image.
The source is cited for classical hierarchy background and related infinite
tiling classifications, not as proof of the exact quadratic compiler here.

## Novelty boundary

The priority search was targeted, not exhaustive. The article does not claim
historical novelty for counter universality, analytical recurrence hardness,
König compactness, or the link between recurrence and fairness. Its precise
quantitative normal form, affine obstruction, and combined computable-bound
separations are developed and proved within the manuscript; their
literature-wide priority remains unverified.
