# Suggested ProveIt integration

Create a new directory:

    Combinatorics/Ramsey/Research/PrimeCyclicBohrObstructions/

Copy this package there without changing the existing numbered Gowers statement catalogue or the formalization counts.

Suggested research-index entry:

> **Prime-Cyclic Bohr Boundary Obstructions — Exponential rank dependence from near-parallel frequencies.** Conventional proofs and exact regression checks. Constructs r-constraint, individually irredundant Bohr sets in all sufficiently large prime cyclic groups with normalized one-step boundary ratio arbitrarily close to (2^r-1)/2. Provides exact circle-component and mass formulas, finite-grid error bounds, radius persistence, and a total-variation approximation/translation tradeoff. Strengthens the inspected member-30 product/CRT lower obstruction from rank base sqrt(3) to 2. No global quantitative Szemeredi improvement or Lean verification is claimed; priority and sharp optimality remain unverified.

Cross-reference the local-quantitative-refinements member-30 fixed-radius package rather than replacing its upper bound or source correction. The new construction is a lower obstruction; the earlier escape-tube upper bound is retained and attributed.

The comparison to `openai/math` is an interface-level motivation concerning sharp versus padded/smoothed polynomial cells. Do not list this package as a dependency proving or disproving that repository's all-length progression claim.

Independent mathematical review and a targeted literature comparison should precede marking the results as independently confirmed. `FORMALIZATION_PLAN.md` gives suggested later work, not already checked Lean modules.
