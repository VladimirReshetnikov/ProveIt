# Independent audit: every internal 2-by-3 core with complete exteriors

Verdict: **APPROVED**, October 1, 2026. This is a computer-assisted exact-algebra theorem for arbitrary finite exterior populations. The first/last inequalities, moment reduction and graph formulas are ordinary proofs; the two middle inequalities use 26 exact finite identities. No frozen earlier package was modified.

## Scope and support reconstruction

The physical bipartite shores are disjoint `P union X` and `Q union Y`, with `|P|=2`, `|Q|=3`; every P–Y and X–Q edge is present, while H is any of the 64 internal P–Q masks. Every vertex has an arbitrary nonnegative activity. Feasible shore endpoint pairs are counted once, regardless of matching witnesses.

For selected core sets I,J and a size-k support, exactly `|I|+|J|-k` matching edges must be internal. A matching of that size in H[I,J] extends using the two complete exterior blocks. This verifies the Boolean formula for all populations. The independent checker avoids that shortcut when rebuilding coefficients: it makes the entire selected physical graph with the requisite numbers of exterior vertices and tests every Hall subset. The activity monomials and normalized exterior elementary moments are accumulated from these Boolean tests.

At actual degree five, each of the five cover vertices must have positive activity, X has at least three positive vertices and Y at least two. Otherwise no positive size-five support exists. In lower degrees, deleting zero-activity vertices preserves the polynomial and leaves a bipartite graph of matching number equal to the surviving degree. The previously approved arbitrary-vertex-weight bipartite rank-at-most-four theorem then gives the correct normalization. No division by vanishing first moments or padded order-five conclusion is used in that branch.

## Moment domain and polynomial targets

In the degree-five branch, divide the left activities by e1(X) and the right activities by e1(Y); this divides coefficient k by a common positive k-th power. The exterior first moments become one. Let M=e2(X), N=e3(X), S=e2(Y) after scaling. Positivity and the elementary squared-moment identities imply

`0<2M<1`, `0<2S<1`, `0<3N/(2M^2)<1`.

For the last strict inequality, the already verified expansion of `2e2^2-3e1e3` has a strictly positive squared-pair term because at least two exterior activities are positive. For the first two, the sum of individual squares is positive. Thus every actual degree-five instance has unique finite positive cone coordinates

`M=V/[2(1+V)]`, `S=W/[2(1+W)]`, `N=V^2 Z/[6(1+V)^2(1+Z)]`.

No converse realization of every cone point by a finite exterior population is needed: the certificate proves nonnegativity on a larger domain containing all valid instances.

The first middle gap is g2^2−2g1g3. Here g1,g2 are independent of N and the coefficient of N in g3 is exactly q0 q1 q2 for every H. The gap is therefore nonincreasing in N. Replacing N by its upper bound `2M^2/3` gives a lower bound, not an upper bound. Multiplication by `(1+V)^2(1+W)^2` clears every denominator.

For g3^2−2g2g4, use the actual cone coordinates without replacing N. The denominator is `(1+V)^4(1+W)^2(1+Z)^2`. Both multipliers are strictly positive. Inspection of the moment exponents shows these powers suffice for every mask; the independent checker also verifies the bounds term by term and compares direct rational substitution with polynomial expansion at 52 separate rational points. The latter comparisons are diagnostics; the exact denominator-clearing formula is reviewed algebraically.

## Orbit coverage and exact rational certificates

The independent row/column permutation action gives the thirteen representatives `0,1,3,7,9,10,11,14,15,27,29,31,63`. Every one of the 64 masks is covered exactly once. All 384 six-coefficient relabel comparisons pass. Since the five core activities are independent variables, these isomorphisms preserve the full claimed weighted scope rather than only unit weights.

For each of the 26 targets, the independent standard-library checker reconstructs the complete rational polynomial from direct Hall feasibility, then expands every supplied term `lambda*x^m*(rho*x^a−x^b)^2`. It checks that lambda and rho are positive rational numbers and every exponent is a nonnegative integer. It subtracts into the full monomial dictionary, including new monomials not in the original target, so no negative off-support residual can escape inspection. It imports no producer code, invokes no optimizer and does not use stored remainder data as a premise.

All 915 squares pass; the freshly computed remainders contain 33,318 positive coefficients and no negative coefficient. Every remainder is nonempty. The five core variables and V,W,Z are all strictly positive in the degree-five branch, so each nonempty positive remainder evaluates strictly positively. This proves both strict middle inequalities. The first middle result transfers from its boundary value of N back to the original N by the correct monotonicity direction.

The floating-point search that found the rational weights is not a dependency. The independent verification is exact. The certificate checks are exhaustive identities on the 13 core orbits, not finite sampling of the infinite activity/population space.

## First/last gaps, including the empty core

At degree five, the complete P×Y exterior block contains a positive K2,2. Its duplicate size-two matching witnesses make the universal compatibility-graph upper bound strict, giving `gamma1^2>(5/2)gamma2` for every mask.

If H is nonempty, gamma4 and gamma5 are identical to their complete-core values, while gamma3 only decreases when core edges are removed. The previously approved strict complete-core last-gap bound applies directly.

For H empty, I independently substituted its coefficients into the displayed ratio formula and verified the exact identity

`(4 gamma4^2−10 gamma3 gamma5)/(B^2 E^2 M^2 R^2)=4(x+y)^2−10[xy+ch y^2+bs x^2]`.

The elementary bounds b≤1/4, c≤1/3, h≤2/3, s≤1/2 make this at least `(x−y)^2+7x^2/4+7y^2/9`, strictly positive because x,y>0. Thus the empty core does not need the separate star-stability theorem as an extra premise.

Positive submatchings ensure no internal zeros. These ordinary first/last arguments plus the exact middle identities and the lower-rank dependency prove actual-degree ULC for every internal mask, with all four gaps strict at degree five.

## Replay and exclusions

`check.py` accepts `--data-dir` and `--output-dir`, requires only Python's standard library, and rejects `-O`. The receipt records 5,248 selected-subgraph Hall tests, 384 coefficient relabel checks, 52 rational substitution comparisons, all 26 certificates, and hashes of every certificate and the proof note. The all-size proof depends on the reviewed reduction, not on the finite diagnostic evaluations alone.

The complete exterior blocks are essential to the scope. Arbitrary missing exterior edges, arbitrary orientations, independent edge activities and general weighted matching rank five are not established. Real-rootedness is a separate stronger result for empty/star masks; the complete-core nonreal example rules out a uniform real-rootedness claim here. No proof-assistant formalization or priority claim is made.
