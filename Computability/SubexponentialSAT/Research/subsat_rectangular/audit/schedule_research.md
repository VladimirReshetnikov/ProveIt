# Schedule research result

## New proved refinement relative to imported contraction interface

A conservative use of genuinely rectangular matrix multiplication (dual exponent alpha > 0.3; square exponent omega < 19/8) gives a normalized-wire contraction certificate

- time coefficient C_T = 33.993890859235...;
- space coefficient C_S = 33.993720890631...;
- common scale s / sqrt(log2 s), polynomial description-length factors;
- safe eventual coefficient 34 for both time and space.

This beats the newest incoming cached-tree report's displayed C_T = 35.354588058401..., and also the old square-block method's r=8 limiting root-capacity value 35.063598846170.... It does **not** improve logarithmic order, does not claim optimality among all schedules, and does not establish the conditional n/log n targets. It uses subexponential space. The root tables, not the recursive tail, determine both leading constants.

The complete article-ready proof is `rectangular_theorem.tex`. The executable exact certificate is `rectangular_schedule_certificate.py`; its output is `rectangular_schedule_certificate.json`. Both ordinary Python and `python3 -O` should pass. These verify arithmetic and recurrence bookkeeping, not the imported contraction algorithm or the field multiplication theorem.

## Critical correction made during derivation

A finite rectangular exponent 2+epsilon adds epsilon*y to BOTH branches, including the input/output branch x+y. Omitting it would incorrectly make C_T=C_S. The final proof takes epsilon=1/100000 and uses

max{(1+epsilon/2)(x+y), x+(47/56+epsilon)y+(15/28)z}

for sorted dimension logarithms x>=y>=z. This is a safe upper bound on the interpolated field exponent. The first branch dominates every relevant worst-case cardinality certificate. It gives the factor (1+1/200000) between the time and space coefficients. A fixed epsilon=1/1000 would be too coarse for the chosen `<34` target. The final proof avoids any nonuniform n^{o(1)} diagonalization.

## Simple schedule

Arities: r0=8, r1=10, r2=6, and r3+j=4.

Fractions: f0=49997/3000000, f1=67/5000, f2=17/2000, f3+j=(34003/8000000)(5/8)^j.

Total retained-range capacity: 499/10000. Buffer ceil(6 log2 lambda); leaf threshold s/lambda. All packing gates have strict rational power margins. The root high-degree exponent is 499997/500000 = 0.999994; this is an asymptotic certificate with a potentially enormous threshold, not a practical solver recommendation.

Final block partitions: (3,3,2), (4,3,3), (2,2,2), (2,1,1). Binary subblock merges are balanced. Their largest boundary cardinalities are 30,48,16,8. All corresponding matrix operations are dominated by the near-quadratic input/output term. The complete cache recurrence is paid; tail time candidates 32.812822,31.412630,33.657386 are strictly below the root 33.993891.

## Scheme barrier, including adaptive tree caution

No explicit balanced-cut lower bound was found in the 19 reviewed proposal sources by searching the terms `balanced cut`, `r/3`, `2r/3`, `tree lower bound`, and related phrases. This is a new scoped statement in this review, not a claim of general novelty.

Consider the leading common-tilt entropy relaxation on r(r-1) directed pairs:

H_r(K) = {h >= 0 : ||h||_2 <= K/r}.

A full table on the boundary of a group subset B, |B|=k, has logarithmic cell count L_B(h)=sum_{e crossing B} h_e. The number of crossing directed pairs is 2k(r-k). For a fixed contraction tree, every full binary tree with r leaves has a node with k in [r/3,2r/3]. (Descend while a child has more than 2r/3 leaves; then one child has at least r/3 and at most 2r/3.) Its worst-case table certificate is

sup_{h in H_r(K)} L_B(h) = K sqrt(2k(r-k))/r >= (2/3)K.

This is a fixed-tree certificate barrier. It is **not** a proof that every input costs that much, and it is **not** valid to interchange the supremum over h and minimum over adaptively chosen trees.

For an adaptive tree there is nevertheless an arity-uniform barrier in the SAME abstract entropy model. Choose the single uniform vector

h_e = K / [r sqrt(r(r-1))].

This vector belongs to H_r(K), and every tree has the balanced node above. Its boundary logarithm is at least

(4/[9 sqrt(1-1/r)])K >= (4/9)K.

Thus even budget-dependent adaptive selection among all full-table binary contraction trees cannot prove an o(K) worst-case estimate using only this entropy relaxation. A final triangle contraction can be regarded as a binary tree with a final scalar operation, and its intermediate block boundary tables obey the same argument. Tables may be formed in any order; the argument concerns the required size of one materialized table.

The packing certificate at the root imposes 2a0 log2 r + (9/10)log2 s < log2 s up to lower-order terms, and u0<=a0. Hence u0 <= (1/20+o(1)) log2(s)/log2(r). Since K= (pi sqrt2/ln2) s/sqrt(u0), either fixed- or adaptive-tree envelope is Omega(s sqrt(log r)/sqrt(log s)), in particular Omega(s/sqrt(log s)). This conclusion remains true even if one grants arities growing with s and ignores their extra budget-enumeration cost, provided the same packing/entropy relaxation is the proposed certificate. It cannot yield a new logarithmic power by tree selection, arity retuning, or faster matrix multiplication alone.

The barrier is only for the abstract full-table entropy certificate model. The norm-ball vectors have not been claimed to arise from every real contraction instance; this is not an algorithmic or SAT lower bound. More detailed realizability constraints, nonmaterialized tables, or a new structured summation theorem could evade it. Explicit enumeration has its own already-discussed weighted-partition barrier; this result supplements it for cached table schemes.

## Additional numerical research

A discretized dynamic program over cumulative packet capacities and arities 3..30 found no better fixed normalized certificate than the root-8 table floor. Root 6 and 7 certificates remained about 38.56 and 35.21 respectively in that search. This is heuristic exploration only, not an optimality proof; the search script requires numpy/scipy and need not be included in the deliverable. The final theorem relies only on the simple rational schedule and standard-library exact checker.
