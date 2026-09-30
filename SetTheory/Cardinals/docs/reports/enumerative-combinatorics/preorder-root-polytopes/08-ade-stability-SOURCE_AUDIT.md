# Source and claim audit

Review date: 29 September 2026 (America/Los_Angeles).

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned snapshot:
`e1afd75e35a4de734d5aa47aec5cdb917b82ed3e`

Principal comparison file:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/README.md`

Git blob:
`846d9f19fadac9cd933b74370cdb8fafa2211c5d`

The README was fetched from the default branch and again at the pinned commit;
the blob matched. The comparison is targeted, not a complete audit or rebuild of
the repository.

The inspected report already includes:

- height-two matching-support/preorder identities and general gamma-positivity;
- a faithful-matrix classification for bipartite cacti;
- a stable noncactus K_{2,3} example and its tree attachments;
- earlier nonreal-root examples, including Theta(3,3,3), with the corresponding
  first preorder counterexample credited there to Shivam Patel;
- questions about stability/real-rootedness beyond those constructions.

This delivery does not claim those results. The original Patel posting's exact
date and independent verification status were not established in this review;
the article explicitly attributes the historical credit to the inspected repo.

## Primary literature inspected

1. Choe, Oxley, Sokal, Wagner, *Homogeneous multivariate polynomials with the
   half-plane property*, arXiv:math/0202034; Adv. Appl. Math. 32 (2004), 88–187.
   https://arxiv.org/abs/math/0202034

2. Brändén, *Polynomials with the half-plane property and matroid theory*,
   arXiv:math/0605678; Adv. Math. 216 (2007), 302–320.
   Theorem 5.6 is the real multiaffine Rayleigh characterization. The article
   reproves the necessary direction it uses.
   https://arxiv.org/abs/math/0605678

3. McKee and Smyth, *Symmetrizable integer matrices having all their eigenvalues
   in the interval [-2,2]*, arXiv:2002.06082 (2020).
   The introduction and diagrams describe the classical finite/affine ADE
   spectral context. The tree classification is reproved in the delivery and is
   explicitly not a novelty claim.
   https://arxiv.org/abs/2002.06082

4. Ohsugi and Tsuchiya, *Symmetric edge polytopes and matching generating
   polynomials*, arXiv:2008.08621; Combinatorial Theory 1 (2021), Paper 9.
   Relevant prior graph-polynomial context; not a dependency of the tree proof.
   https://arxiv.org/abs/2008.08621

5. Dai, Hou, Liu, Thawinrak, Wang, *Counting Lattice Points in Minkowski Sums of
   Cross Polytopes*, arXiv:2608.16037v2, 27 August 2026.
   Prior root-polytope/support and duality context; not claimed as new.
   https://arxiv.org/abs/2608.16037

## Dependency boundary

The main tree criterion is proved independently of the repository's unrefereed
cactus and general gamma-positivity claims. Its analytic inputs are standard
stability closure facts, elementary Hermitian matrix analysis, the necessary
Rayleigh inequality, and Perron positivity. Its combinatorial inputs are proved
from forest incidence minors. The ADE identification uses a classical spectral
classification for which a self-contained tree proof is supplied.

The terminal-subdivision and odd multi-theta necessity arguments use an explicit
generic-matrix contraction/deletion lemma, not an unsupported assertion that
arbitrary graph contraction preserves stability. The even multi-theta argument
uses independent columns and squarefree differential operators; it does not
claim that arbitrary averages of stable polynomials remain stable.

Only the preorder-corollary subsection imports the repository's transform
h_P(t) = (1+t)^n p_G(t/(1+t)^2).

## Results developed in this delivery

- Exact determinant–adjugate identity with forced tree covariance I - A/2.
- Stability iff the tree covariance is positive semidefinite.
- Explicit rational negative Rayleigh certificates for every excluded tree.
- Extension to subdivisions between fixed terminal apex neighbors.
- Sharp book threshold, exact univariate formula, discriminant proof of
  all-size real-rootedness, and uniform-basis covariance formula.
- Independent-column proof for arbitrary even-path multi-theta graphs.
- Complete simple bipartite multi-theta stability classification.

These are mathematical claims accompanied by written proofs and finite checks,
not externally certified priority claims.

## Limitations of the literature search

Focused searches combined matching-support polynomials, half-plane property,
transversal matroids, tree incidence, spectral radius, and ADE. No retrieved
source was identified as stating the exact tree incidence–apex equivalence.
This does not establish worldwide priority. Equivalent results could occur in
matroid terminology not retrieved by those searches. An independent specialist
review is required before making a publication-priority claim.

## Verification status

All finite checks listed in `data/verification_results.json` passed exactly.
The article was compiled and visually checked as a PDF. No theorem in this
package has been checked by Lean, Rocq, or another proof assistant. Numerical
experiments are not substituted for the written universal proofs.
