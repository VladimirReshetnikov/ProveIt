# Independent audit: disjoint core edges and arbitrary balanced cross-core subsets

Approved: for any subset J of P×Q with |P|=|Q|=2, and independent exterior vertices with arbitrary P→I→Q attachments, the signed physical monomer polynomial is real stable for all nonnegative independent role activities. Gamma consequently has only negative real roots and satisfies actual-degree ULC. This note audits the disjoint-two-edge case and the empty/single-edge completion; the full, three-edge and adjacent-two-edge cases have separate approved ordinary proofs.

Final proof: `../DISJOINT_CORE_EDGES_REAL_ROOTEDNESS.md`, SHA256 `1f0d2a69ec0ff8f7c1d0a5267afc30b76761c8a940a06f6cfecb5d3c9652343b`. The revision from the originally reviewed hash was verified to change its status sentence only.

## Kernel and unrestricted algebra

With diagonal core edges, a lost one-core-edge support has residual endpoints forced to one of the two omitted off-diagonal edges. These two sets are disjoint. If either residual endpoint has both choices available, at least one diagonal edge remains, so there are no further losses. The lost terms use opposite private/dummy classes; common-neighbor copies are correctly absent. The two-core-edge support still exists and contributes once. The corrected kernel is therefore B_PB_Q−L_PL_Q+1+r_P1 r_Q2+r_P2 r_Q1.

After swapping the two Q class labels, the corrections are p0q0+p1q1. I independently reconstructed every Rayleigh difference from the bivariate coefficients of H and formal remaining-class first/second moments. The script `check_disjoint_rayleigh_aggregate.py` proves all seven stated identities as exact polynomial identities in independent aggregate symbols, using e2=(A²−U)/2. This proves the formulas for arbitrary class counts and does not rely on the producer's four-class experiment.

The symmetry reduction is complete: three same-side pair types (two distinguished, mixed, two ordinary), and four cross-side types (partnered distinguished, unpartnered distinguished, mixed, two ordinary). Side reversal, simultaneous exchange of partnered distinguished labels, and ordinary-class permutations cover every pair. Empty sums are valid. Each right side is nonnegative at every real class assignment because U,V are sums of squares and their products distribute into squares.

The nonzero multiaffine H therefore meets Brändén's all-real Rayleigh criterion, Theorem5.6 in [the primary paper](https://arxiv.org/pdf/math/0605678), independently inspected during the missing-edge audit. Substitution of nonempty parallel-class sums transfers stability to ground variables without a separate same-class criterion.

## Remaining patterns and weighted transfer

For zero core edges the product B_PB_Q is stable. For one core edge, the kernel is (1−∂a∂b)(B_PB_Q), with a,b the relevant private dummies. Its complete bounded-degree symbol is ((a+x)(b+y)−1) times the usual untouched-variable factors. Both sums are strictly upper, so their product cannot be1. The empty-support leading coefficient remains1. This validates the single-edge proof with the plus-sign convention of Borcea–Brändén Theorem1.1.

All subsets of the four cross-core arcs are now covered up to relabeling/reversal. The negative-reciprocal monomer substitutions, activity scaling, stable physical-copy merge, zero-activity limit, and gamma-root transfer are exactly the previously approved operations. No arbitrary edge-activity theorem is asserted.

## Independent finite test

`../../independent-audit/check_disjoint_monomer.cpp` directly Hall-recounts ordered disjoint supports and separately expands the corrected two-copy formula. It passed all 4,845 exterior-type multisets through four vertices, including isolates, in three role-activity assignments: 14,535 exact multivariate monomer identities and 234,660 feasible supports. The ordinary proof handles unbounded exterior size.
