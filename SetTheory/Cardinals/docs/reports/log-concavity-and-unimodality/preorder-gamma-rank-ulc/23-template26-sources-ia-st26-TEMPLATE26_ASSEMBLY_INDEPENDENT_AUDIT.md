# Independent approval: smaller template26 last-gap proof

Approved 2026-10-01. The frozen proof `TEMPLATE26_LAST_GAP_PROOF.md`, SHA256 `08533189ced10ebd683447d792da4176eeb07107958cf31b236da71c528016fb`, supplies a valid certificate-assisted replacement for the large whole-sextic proof of template26's last order-four Newton gap. The original degree-four archive is unchanged.

## Scope and dependencies

The result covers all nonnegative integer clone populations of the eleven legal types 1,2,3,5,7,8,9,10,11,13,15, core rows [0,0,1,7], orientation8, with unit activities. Supports are ordered disjoint tail/head sets, counted once whenever a perfect directed matching exists. The conclusion is 3 gamma3²≥8 gamma2 gamma4. Actual degree below four has gamma4=0, making this inequality automatic. Full rank-ULC at actual degree four additionally uses the separately approved middle-gap and universal first-gap proofs; smaller actual degrees have the previous degree-at-most-three theorem.

The new proof depends on:

1. The independently approved deletion-mixture lemma: ten quartic integer-binomial certificates, the full single-vertex-weighted actual-degree-at-most-three theorem, and the elementary two-point convex-hull argument. All ten identities were independently rebuilt from the Hall kernel and replayed using exact fractions. The lemma supplies only the last order-three gap, which is all this application needs.
2. David G. Wagner, *Rank Three Matroids are Rayleigh*, Theorem1.1, Electronic Journal of Combinatorics12 (2005), N8; primary preprint https://arxiv.org/pdf/math/0403216 . The theorem and positive-variable Rayleigh definition were checked directly. Boundary evaluations follow by continuity of polynomial inequalities.
3. The elementary support bijection, witness injection, and final quadratic calculation reviewed below.

No full degree-four positivity theorem is invoked as an input to the replacement last-gap proof. The earlier audited kernel is used for an exact consistency check only; our new checker independently reconstructs its coefficients.

## Support decomposition

Only p can be matched to an exterior head. Thus a feasible support has either no exterior head, or exactly one exterior head x and the forced edge p→x. In the first case, replacing p by a new pure universal tail gives precisely Q_plus. In the second case, deleting p and x gives precisely a support of Q_minus_x. The converse constructions preserve disjointness, and distinct x have distinct head sets. This proves Gamma=Q_plus+tR without multiplying by the number of matching witnesses. Exterior vertices that become isolates in Q contribute the undeleted polynomial to R and are explicitly covered by the mixture lemma.

The independent standard-library checker `audit_template26_assembly.py` re-enumerates every ordered endpoint support with each selected exterior clone mandatory, testing matching existence rather than counting matchings. It compares the decomposition and the independently pinned source kernel on all 1,365 quota vectors of total at most four: all 6,825 scalar coefficients agree. Larger quotas cannot occur because every used exterior needs a different core partner, of which there are only four. This is an exhaustive coefficient identity for every population, not bounded-population inference.

## Top-ratio argument

Removing the sole internal arc leaves the exterior-only three-head model F. An internal-arc size-two support uses its other edge to head q1, so B=B0+L. A size-three support cannot use the internal arc, so T=T0. This preserves endpoint-support multiplicities exactly.

In the rank-three transversal matroid obtained by adding three private dummies and one prospective new vertex, f=T0 and f_x=tau at zero dummy/new-vertex activities. A derivative at dummy d_i counts exterior pairs matchable to the complementary pair of heads. Summing these three derivatives gives B0, including once each distinct head set, exactly as required by the support convention. Summing mixed x,d_i derivatives gives beta. Hence the sum of three Rayleigh inequalities is tau B0−T0 beta≥0. The dummies ensure rank exactly three even on low-rank exterior faces.

For the internal-arc correction, choose one matching for each feasible old exterior triple. Recording the vertex assigned to q1 and the remaining pair gives an injection into the L K choices, since the recorded data recover the original triple. Thus T0≤LK. When the new vertex can use q1, each old pair counted by K extends to a distinct new triple, so tau≥K. Otherwise ell=0. In both cases tau L−T0 ell≥0. Adding this to the Rayleigh inequality proves the top-ratio comparison without division. Isolated added vertices give equality.

## Zero cases and final square

If R3=0 the required last gap is immediate. Otherwise some deletion has a positive cubic coefficient. It embeds into Q, so Q has a feasible size-three support and, by deleting one matched edge, also a feasible size-two support. Consequently B>0. Applying the top-ratio comparison on restoration of each deleted vertex and then on addition of the universal vertex, multiplying by nonnegative quantities, and cancelling only this B proves T_x B_plus≤B_x T_plus. No cancellation of B_x, T_x, T, or R3 is needed. The comparison therefore survives zero deletion coefficients and all isolate cases. Summing gives R3 B_plus≤R2 T_plus.

Finally R2²≥3R1R3 and R3 B_plus≤R2 T_plus imply

    3(R2+T_plus)²−8(R1+B_plus)R3
    ≥ R2²/3−2R2 T_plus+3T_plus²
    = (R2−3T_plus)²/3 ≥0.

The directions and numerical factors are correct. This proves the claimed last gap for every integer population. It does not prove a new independently weighted degree-four theorem or real-rootedness, and it remains certificate-assisted rather than wholly ordinary.

Receipt: `template26_smaller_proof_approval_receipt.json`.
