# Source audit and research boundary

Date: 30 September 2026.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `b57c0b5ff112e1a08af8add12b2d687b8ece91d0`

Primary file:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/article.tex`

Git blob: `920246d173bfbc708bcfdd6d67e0a6fc358cb3dc`

Title verified from its preamble/title:
*A Reflexive Root-Polytope Model for Preorder h-Polynomials*.
The snapshot includes seven integrated parts; the relevant stability material is Part VI.

The file was read through the connected GitHub tool at the explicit commit, not inferred
from a same-topic summary. The relevant README and existing `code/08-ade-stability-verify.py`
were also inspected. The source repository is unchanged.

## Source ranges used

Line ranges below refer to the pinned repository file, not the delivered article.

| Lines | Inspected content |
|---|---|
| 1–140 | Title, metadata, scope, and part descriptions |
| 10440–10780 | Part VI provenance, existing claims, notation, status |
| 10800–11100 | ADE, books, multi-theta, matroid and stability bridge |
| 11100–11365 | Cofactors, covariance rigidity, determinant identity, rational Rayleigh certificate |
| 11360–11700 | Classical ADE list, terminal subdivision, legitimate matroid path shortening |
| 12180–12370 | Vertex gluing, tree attachments, weighted diagonals, limits of the existing classification |
| 12410–12680 | Existing checks and proposed further questions |

## Prior results credited, not claimed anew

1. The canonical transversal matroid and inversion bridge.
2. The full-apex tree identity with covariance I - A/2 and its ADE stability criterion.
3. The terminal-subdivision extension and generic path-shortening minor operation.
4. The three-odd-path obstruction and its quartic 1+9t+24t^2+16t^3+t^4.
   The source report credits Shivam Patel for the earlier eight-vertex counterexample.
5. Stability under attaching unmarked trees, available from the source's vertex-sum theorem.
6. The classical ADE spectral classification and general stable-polynomial closure theory.

## Continuation developed in the delivered article

- Arbitrary markings: unmarked branches in the marked hull create an induced odd-theta
  obstruction; the branch-complete cases are exactly those reducible to an ADE terminal skeleton.
- Existence and uniqueness of a supported connected-set covariance, before imposing PSD.
- A direct host-level identity and negative certificate retaining subdivisions and unmarked fringe.
- The at-most-four-leaf endpoint decomposition for every stable marking.
- Exact weighted stable-neighborhood enumeration and O(n^5) arithmetic counting/optimization.
- Exact nearest-neighborhood and weighted apex-edge repair.
- The sharp diameter window for maximum marking cardinality.
- The path-only real-rootedness theorem for the stable-neighborhood counting polynomial;
  explicit failures of log-concavity and unimodality.

This is a relative novelty statement with full proofs, not an exhaustive worldwide priority
claim. General matroid principal-extension theory and small-matroid classifications deserve
specialist comparison before publication.

## Public primary literature consulted

- Choe, Oxley, Sokal, Wagner: *Homogeneous multivariate polynomials with the half-plane property*.
  Advances in Applied Mathematics 32 (2004), 88–187.
  https://arxiv.org/abs/math/0202034
- Brändén: *Polynomials with the half-plane property and matroid theory*.
  Advances in Mathematics 216 (2007), 302–320.
  https://arxiv.org/abs/math/0605678
  https://doi.org/10.1016/j.aim.2007.05.011
- McKee, Smyth: *Integer symmetric matrices of small spectral radius and small Mahler measure*.
  https://arxiv.org/abs/0907.0371
- Kummer, Sert: *Matroids on eight elements with the half-plane property and related concepts*.
  SIAM Journal on Discrete Mathematics 37 (2023), 2208–2227.
  https://arxiv.org/abs/2111.09610
  https://doi.org/10.1137/22M1490648

Public sources were checked online during this task. The article's bibliography gives the
same references. No inaccessible paywalled content is represented as having been read.

## Verification boundary

The 31,886-instance enumeration tests the implementation of the structural classification.
It is not an independent decision procedure for multivariate analytic stability. The 133
small-order coefficient tests do independently compare Boolean support enumeration against
incidence minors and covariance energies. The general proofs, stated imports, computational
checks, and uncompleted formalization are deliberately distinguished.
