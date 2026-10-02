# Independent audit: two-edge balanced star core

Approved after complete written-note review: the directed family with two source centers, two sink centers, both core arcs from one fixed source, and independent exterior vertices with arbitrary source/exterior/sink attachments has a real-stable signed monomer polynomial. Its gamma polynomial is negative-real-rooted, including arbitrary nonnegative independent role activities and degree loss. No transitivity assumption is required.

Proof pin: `../STAR_CORE_REAL_ROOTEDNESS.md`, SHA256 `a65f0f38fa97e83f4ffc96d0aaef2cdc3b362b3f46a86fb9d29cb88c899f34c2`. The actual canonical template6 has rows `[0,0,0,3]` and orientation mask12, exactly this family up to the note's relabeling.

## Checks

- The residual source-side polynomial for one core edge is the derivative of B_P in the internally active source's private dummy. The derivative's remaining dummy and exterior variables encode exactly the optional endpoint at the other source. Common-neighbor copies occur once.
- The sink-side residual is L_Q, with each active exterior copy counted once rather than by neighbor count. Completeness of the two outgoing core arcs makes those conditions sufficient. The number of core arcs is fixed by any feasible endpoint support, and no matching can use two such arcs, so the zero/one decomposition is disjoint and complete.
- The rank-two polynomial B_Q+sL_Q is e2 of the parallel-class sums and an additional variable. The already proved rank-two stability argument applies. L_Q has positive imaginary part and B_Q is nonzero. The absence of an upper-half-plane root in s proves Im(B_Q/L_Q)≥0. The negative reciprocal of this nonzero ratio again has nonnegative imaginary part. Consequently the shifted dummy d−L_Q/B_Q remains strictly upper.
- B_P is affine in this one ground-element dummy even when its parallel class contains other elements. Thus B_Q B_P(d−L_Q/B_Q)=B_PB_Q−(∂_d B_P)L_Q exactly, and is nonzero. No unstated closure under sums is needed.
- Negative reciprocal exterior substitution, clearing all denominators, positive activity scaling, the physical-copy merge symbol z+r+s, nonzero zero-activity limits, and the diagonal root transfer are precisely the independently verified operations from the complete balanced proof. The empty-support leading monomial always remains coefficient1.

## Independent finite check

The separate Hall-support checker `../../independent-audit/check_star_monomer.cpp` compares every coefficient of the physical monomer polynomial against a fresh split-copy derivative formula. All 4,845 exterior-type multisets through four physical vertices, including isolated type0 vertices, passed three activity assignments (unit, positive integer, and nonnegative with zeros): 14,535 exact multivariate identities, 222,025 feasible supports. This validates finite algebraic instances; the ordinary upper-half-plane argument proves arbitrary finite exterior size.

The Borcea–Brändén plus-sign theorem used for merging was checked in its [primary paper](https://arxiv.org/pdf/0809.0401), Theorem1.1. Its closure lemma and Hurwitz theorem were verified during the complete balanced audit. No new external theorem is needed for the dummy shift.
