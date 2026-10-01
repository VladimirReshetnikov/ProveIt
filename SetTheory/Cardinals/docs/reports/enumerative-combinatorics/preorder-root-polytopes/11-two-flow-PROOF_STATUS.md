# Proof and implementation status

## General mathematical results

The article provides ordinary proofs of the following statements:

1. **Theorem 3.2, two-flow correspondence.** The specific forward/inverse margins select the same positive-support tree and give inverse demand/base maps for every finite bipartite graph.
2. **Lemmas 4.1–4.2.** Cycle-generic optimal supports are forests; optima are unique and integral for integral margins; strict tree potentials transfer optimality to other margins.
3. **Sections 5–7.** Component-balance congruences force connectedness, the inverse subtree estimate forces supplier degree at most two, and explicit positive flows prove both inverse identities.
4. **Theorem 8.1, core-tree factorization.** A forward flow on the selected r suppliers has total value r(r+1). All other suppliers attach independently at their unique reduced-cost minima.
5. **Corollaries 8.2–8.3.** Unselected-supplier deletion/insertion, monotone one-unit contributions, commuting deletions, and receiver restrictions outside the support.
6. **Propositions 9.1–9.2.** Finite perturbation invariance, cycle-sign chambers, and row/column gauge invariance.
7. **Theorem 10.1.** Exact tree certificate soundness. The full and core checkers do not need to trust the optimizer's internal potentials.
8. **Propositions 12.1–12.2.** No fully automorphism-natural deterministic correspondence, and no uniformly bounded coordinate displacement for every basis exchange.
9. **Theorems 13.1–13.2.** Exact preservation of total-variation error under the bijection and polynomial-time full-coordinate sampling, using the published matroid-walk theorem as an explicit dependency.
10. **Proposition 14.1 and Corollary 14.2.** The exact preorder demand realization and its full-coordinate sampling consequence.
11. **Proposition A.1.** The normalized inverse dual price maximizer is unique and identifies the selected suppliers by their two minimizing receivers.

Numbering is taken from the compiled delivered article. The supportwise counting identity is credited as known, not claimed as a new enumerative theorem.

## Implemented and executed

- Exact integer successive-shortest-path optimization with exact reduced-cost arithmetic.
- Iterative augmenting-path matching, including demand allocation checks.
- Full forward map, core forward map, and inverse map.
- Exact full and core certificate checkers.
- Lifted matroid basis oracle and unconditioned down-up walk with integer support activities.
- Integer upper bound for the logarithmic mixing budget; no floating logarithm is used to choose the number of steps.
- Preorder validation and graph construction.
- All recorded finite suites in `data/`.

The full/core maps were compared on every exhaustive support pair. The comparison with all demand vectors uses independent subset inequalities and permutation matching, rather than the same optimization routines as the tested functions.

## Mathematical dependencies and prior work

The abstract base/lattice-point correspondence and leaf formula are prior work of Suho Oh. This article independently proves the specific flow realization it uses; it does not assert priority for the existence of a bijection.

The polynomial-time basis walk is imported from Anari–Liu–Oveis Gharan–Vinzant. A certificate for a decoded vector does not independently certify the mixing theorem or the quality of a random-bit generator.

The preorder specialization uses only the stated ideal inequalities and a direct lower-closure proof. It does not depend on unformalized gamma-positivity or flag-polytopal claims in the repository.

## Not supplied or not established

- No Lean or Rocq source, kernel check, or formal build is supplied.
- No independent peer review or global novelty/priority certification is claimed.
- No exact independent uniform sampler is supplied.
- No magnitude-dependent coordinate weighting theorem is claimed.
- No polynomial-in-log-capacity sampler is obtained by the explicit-cloning dilation argument.
- No arbitrary matroid-minor compatibility of the demand bijection is claimed.
- Rational activities and support-conditioned samplers have mathematical algorithms in the article but not dedicated packaged wrappers.
- The general matroid FPRAS is not reimplemented.
- A Python certificate check can contain a software bug; its mathematical soundness proof is not a proof-assistant check of its source code.

## Suggested formal milestone

Formalize the exact objective-gap identity and uniqueness of a tree-supported zero-margin flow first. That gives a small sound certificate checker, usable with an external optimizer. A universal bijection theorem then also needs a formal existence/termination argument, not merely successful certificates on finitely many instances.
