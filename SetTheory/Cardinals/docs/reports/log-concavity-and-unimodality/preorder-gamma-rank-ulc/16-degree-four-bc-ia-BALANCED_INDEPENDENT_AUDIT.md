# Balanced two-plus-two core: independent ordinary-proof audit

## Verdict

APPROVED. `BALANCED_LAST_GAP_PROOF.md` proves 3Γ_3²≥8Γ_2Γ_4 for every nonnegative integer population of all fifteen exterior types in the full balanced 2+2 core family. This is precisely canonical template 34, whose rows are [0,0,3,3] and exterior direction mask is 12. Combining this theorem with the separately approved global gap-two certificate and the universal first-gap argument proves actual-degree ULC for that complete template.

The argument proves the exterior-only polynomial F real-rooted. It does not claim that the full Γ polynomial is real-rooted, and it does not assert the full four-attachment theorem.

## 1. Exact support decomposition

All core sources lie on the tail side and all core sinks on the head side in any feasible support. If the selected core subsets are A⊆P and B⊆Q and the selected exterior heads/tails have cardinalities h,j, every realizing matching has exactly s=|A|−h=|B|−j core edges. Thus supports with different s cannot overlap even when they have several realizing matchings.

For s=0, the support is counted by F. For s=1, core subset sizes (1,1),(2,1),(1,2),(2,2) respectively contribute 4,2m,2n,mn−r supports at degrees 1,2,2,3. A physical vertex eligible on both sides cannot occupy both roles, explaining the subtraction r. For s=2, the single support consisting of all four core vertices contributes exactly one t² term. Complete P-to-Q adjacency makes every stated feasible exterior assignment sufficient. Multiple core-edge matchings do not create extra supports.

Consequently Γ=F+4t+(2(m+n)+1)t²+(mn−r)t³ exactly.

## 2. Stability and multiaffine truncation

On a two-center side, e₂(1+Σ_A z_x,1+Σ_B z_x,(z_x)_{x∈Z}) has coefficient one at the empty physical support, coefficient |P(x)| at a singleton, and coefficient one at each matchable two-element physical set. In particular a pair of common neighbors has coefficient one, not two. The singleton multiplicity correctly counts the different selected core vertices.

The e₂ polynomial is stable: differentiate ∏(s+y_i) the required number of times in s and specialize s=0. Its nonnegative affine substitutions are valid by upper-half-plane preservation and boundary specialization. Multiplying the two side polynomials is valid even though physical variables are shared.

For completeness, the stated degree-at-most-one truncation argument is correct. With the other variables in the upper half-plane, roots ρ of h(z) have Im ρ≤0. If h(0)≠0, the sole possible root of h(0)+z h′(0) is 1/(Σ1/ρ), which has imaginary part at most zero; when the denominator vanishes the truncation is a nonzero constant. Hurwitz boundary specialization handles identically zero coefficient cases. In this particular construction those cases are unnecessary: the multivariate constant coefficient remains one after every truncation, so specialization at z=0 is a nonzero stable polynomial.

Truncation deletes exactly uses of a physical vertex in both roles and leaves every valid support coefficient intact. Diagonal specialization then gives the real-rooted F; its nonnegative coefficients and constant one place all roots strictly below zero. For F_4=d>0, degree-four Newton gives 3c²≥8bd with the displayed constants.

The necessary closure statements were checked directly in Wagner's author-hosted survey, Lemma 2.4 and the preceding Hurwitz statement: https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf . The specific truncation proof above was audited directly and does not depend solely on an operator citation.

## 3. Counting bounds and all exceptional cases

Every degree-four F support has two exterior heads and two disjoint exterior tails, with all four core vertices selected. It yields four different ordered pairs of eligible head/tail pairs: two orders of the heads and two assignments/orders of the tails. Each ordered decomposition identifies its support uniquely. Therefore v²≥4d has no matching-multiplicity defect.

The identity 6N p₁−20p₂=(A+B−Z)²+Z²+5(A−B)²+10Z was expanded and verified coefficientwise. Fixing a feasible tail pair leaves a two-center head problem with at most m eligible vertices. Its singleton count carries exactly the multiplicity of the selected source core vertex. Summing p₂≤(3/10)N p₁ over feasible tail pairs yields d≤(3/10)m c_(1,2), with no extra matching count; the symmetric argument gives the asserted lower bound for c.

When max(m,n)≥5, the proof's estimate E≥4d is valid. For the six unordered pairs 2≤m≤n≤4, the r constraint follows from the four distinct exterior vertices required when d>0. All displayed K values and monotonicity in r are correct. Only (2,4,2),(3,4,3),(4,4,4) remain below −12. Their active union has four vertices, so a head pair determines its complementary tail pair and d≤binom(m,2). Multiplication by negative K is in the correct direction. The three lower bounds 94,198,336 are correct.

The d=0 case is immediate because Γ_4=0. In fact the displayed estimates give strict last inequality whenever d>0: the large-count bound is strict and every nonexceptional small row has K>−12, while all three exceptions have strictly positive lower bounds.

## 4. Independent finite verification

Both supplied verification scripts were copied into this audit directory and rerun successfully. Their original files were not edited. The 15,625 scalar identity checks and 256 deterministic labeled examples reproduce their receipts.

A separate C++17 Hall checker imports none of those routines. It checks every multiset of the fifteen types of total size at most four, all 3,876 cases. For each it compares direct full-graph Hall support counts, direct core-deleted Hall counts, and a separate disjoint exterior convolution obtained by enumerating selected core subsets. All decompositions and counting bounds pass, including 1,998 degree-four cases. Undefined-behavior sanitization reports no issue.

The 275 different resulting F polynomials were also checked using exact rational real-root isolation with multiplicities. Every root was certified negative and all algebraic degrees were accounted for. These are corroborating finite checks; the stability and counting proofs establish the arbitrary-population theorem.

Files: `check_balanced.cpp`, `check_balanced.log`, `F_polynomials.txt`, `independent_verification.json`, and the separately reproduced producer-script receipts. The audit receipt pins their hashes and the reviewed proof.
