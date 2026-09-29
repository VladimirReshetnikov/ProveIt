# Proof and verification status

Date: 29 September 2026.

## Mathematical statements proved in the article

1. The general gamma and multivariate support identities for every finite
   preorder (Theorem 2.2), using the established bipartite counting identity.
2. The transitivity/cancellation/palindromicity/gamma-positivity equivalence
   and exact endpoint-defect formulas (Theorem 2.3), with a separate elementary
   matching-theoretic proof independent of the counting identity.
3. The quotient-block formulas; monotonicity, products, duality and sharp
   extremal bounds; gamma degree and exact -1 multiplicity; and the
   centered-binomial mixture, variance and concentration formulas.

The elementary or classical consequences are not all claimed as new in the
historical sense. In particular, preorder duality, classical chain formulas,
and the height-two matching-support formula were known to the inspected
sources and are explicitly credited.

## Imported mathematical boundary

Lemma 3.1 reduces demand/support equinumeracy to:

- the normalized-volume/hypertree-vector identity for a connected bipartite
  root polytope (Kálmán–Postnikov);
- the matching-support interpretation for its two-universal-vertex
  augmentation (Ohsugi–Tsuchiya; Davis–Kohl Theorem 3.10).

The argument includes the explicit demand-to-hypertree-vector correspondence.
It does not reprove the entire cited root-polytope theory. These are standard
external mathematical inputs, not computational assumptions inferred from
small tests. The main theorem is not conditional on an unrefereed ProveIt
claim. No assertion of Lean availability is made for either external input.

## Independent finite checks

The exact standard-library Python run completed successfully. The full
record is in `data/verification.json` and `data/verification.log`.

The program distinguishes actual matchability (recursive bipartite matching)
from ideal inequalities. It distinguishes actual point enumeration (all
nonnegative vectors of total at most n, tested against ideals) from the
Boolean formula. A separate undirected matching recursion checks gamma
degree. The block formula is checked against the support-pair count.
All negative characterization tests include nontransitive relations.

There is no floating-point step in a mathematical check. The reported time
uses a floating-point timer only; it plays no role in correctness.

## What has not been established

- No proof-assistant formalization or successful Lean compilation.
- No independent referee certification or community acceptance.
- No exhaustive literature/priority certification.
- No canonical pointwise bijection in the inherited demand/support identity,
  and no natural Boolean orbit action on the original lattice points.
- No solution of general flag-polytopal realization.
- No claim of general real-rootedness, gamma log-concavity, or gamma unimodality.
- No classification for arbitrary unbalanced bipartite graphs or balanced
  graphs whose maximum matching is smaller than a shore.
- No claim that h_tau is the Ehrhart numerator of the original Q_tau.
- No reliance on small-instance verification as an all-size proof.

## Suggested independent-review order

Check the support-fibre equivalence (Lemma 4.1), then the imported identity's
normalization (Lemma 3.1), then the finite Boolean summation proving Theorem
2.2. Separately check the near-perfect-support/reachability lemma (Lemma 6.1)
and its transitivity conclusion. For the block theorem, check that ideal
constraints depend only on block differences and that sign assignments are
counted with their multinomial multiplicities.
