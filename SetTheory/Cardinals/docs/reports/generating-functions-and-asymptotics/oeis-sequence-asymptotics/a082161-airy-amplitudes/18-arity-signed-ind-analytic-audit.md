# Independent analytic audit: general fixed-arity signed extensions

Date: 2026-10-02. Reviewed producer text: `../general-signed-all-orders.md`.
SHA-256: `e50fc94256b8dfefd6320991b2f00b12b7b60cce540183b366413bc9d9f10f60`.

## Verdict and scope

**Approved for every fixed integer k≥3, and every fixed finite expansion order.** The compacted-tree and finite-language DFA sequences in the specified source conventions have the claimed all-finite-orders Poincaré expansions with one strictly positive amplitude for each model, independent of the truncation order. The normalized ratio constants are positive. Their first logarithmic corrections and eventual strict decrease are established. There is no unresolved signed-delay, endpoint, seed, or all-order transfer gap.

This approval inherits the independently approved leading relaxed estimates and relaxed polynomial formal machinery. It does not claim uniformity in k, convergence of an infinite formal series, explicit amplitude values, or literature novelty. The independent checks are corroboration, not proofs of the infinite asymptotic statements.

The one requested textual change was replacing the unnecessary sharper harmonic-weight bound by the exact inherited bounded-comparability assertion. The reviewed revision contains that change. It introduces no mathematical change to the result.

## 1. Source conventions and transformed physical boundary

The primary source was independently opened: Dastidar–Wallner, arXiv:2404.08415v1, https://arxiv.org/html/2404.08415v1 . Propositions 10 and 11 give the compacted/DFA recurrences; Tables 2 and 3 provide independent initial-count checks. The paper's displayed nonnegative-domain recurrence does not by itself state the negative-index auxiliary. The audit treats b(−1,0)=1 as the explicit exceptional convention required by the displayed first count and verifies that it reproduces every compared table entry. It is not silently attributed as an explicit formula in the paper.

For normalized a=b/2^m, the negative coefficient is m/2; for compacted a=c it is m−1. Under X=(qi+j)/k and m=(i−j)/k, the source locations map as follows:

- Horizontal predecessor (X−1,m): (i−1,j−1)
- Vertical predecessor (X,m−1): (i−1,j+q)
- Subtracted predecessor (X−k,m−1): (i−k−1,j−1)

The factorial gauge produces the ordinary up coefficient q²(m+1)/X and the delayed coefficient δ_m q^(2k)/(X)_k. The coefficient at m=0 must be set to zero rather than using the compacted expression −1 outside its source recurrence. This is correctly done.

For i≥k+1, physical X=i−m≥ceil(qi/k)≥k. Thus no delayed denominator vanishes. Congruence is preserved: j−1≡i−k−1 mod k. For j≥1, the delayed upper bound j−1≤i−k−1 is equivalent to j≤i−k, namely m≥1. At j=0 the input is below the boundary; at m=0 it is outside the upper boundary. Every omitted input in the claimed recurrence is therefore genuinely absent.

The first physical vector with a non-diagonal entry is i=k. The ordinary top values are q^(2i)/i!. At (k,0), the compacted value is q^(2q)/q!, and the normalized DFA value is half that. In the original DFA recurrence the exceptional term at (q,1) is b(−1,0), giving b(q,1)=1. Subsequent first-row values solve b(x,1)=2b(x−1,1)+1, yielding 2^(x−q+1)−1. No factorial at −1 is ever needed.

## 2. Completed-run identity and nonzero lower comparison

A proof can be organized by decomposing a legal path at its vertical steps. If the run at level m has length ℓ≥k, its final k horizontal steps have weight (m+1)^k. Deleting that final block produces exactly a prefix contributing to a(X−k,m). All earlier prefix barriers are unchanged; the remaining portion of the last run is legal because its starting point was already legal at level m. Conversely, each source prefix extends by k horizontal steps and the rise to a legal target whenever the recurrence is evaluated there. This is the bijection behind the signed subtraction.

The coefficient at the rise to m+1 is m for compacted trees and (m+1)/2 for normalized DFAs. Dividing by the removed block weight gives precisely m/(m+1)^k and 1/[2(m+1)^q]. A run has only one final marked block; there is no multiple-subtraction or overlapping-block issue. Expanding the product over completed runs reproduces the recurrence, with the open terminal horizontal run unmodified. This also proves the identity away from the diagonal, not just for endpoint counts.

The first normalized DFA run has factor one half for every admissible length: for ℓ≥k it comes from the ordinary negative term, while the shortest ℓ=q uses the exceptional auxiliary. On the final diagonal, the open terminal run has zero length: its starting point after the final rise must already have x≥qn, equal to the target. Hence the displayed expectation identities are exact and the factor 2^(n−1) is correct.

All individual factors are in (0,1]. The compacted defects are bounded by (m+1)^−q and the DFA defects by half that quantity; their sums converge for q≥2. Standard logarithm bounds after finitely many factors show each infinite product is strictly positive. Thus the lower comparisons are global in n and independent of any limiting path law. No exchange of expectation and infinite products is being used.

## 3. Global signed operator norm

For a concrete large-time bound, take i≥2k. Then X≥qi/k and X−(k−1)≥qi/(2k). Also 0≤δ_m≤C_k i on physical active inputs. Therefore

|β_i(j)| ≤ C_k i · (qi/(2k))^(−k) = C'_k i^(−q)

uniformly in every physical j, including heights outside the Airy window. Bounded positive weight comparability gives

sum_j ω_j |β_i(j)v(j−1)|² ≤ C_k i^(−2q) sum_t ω_t |v(t)|²,

because the shift is injective and omitted inputs only remove terms. The inherited fixed-weight norm therefore gives the claimed global O_k(i^−q) operator bound. The finitely many smaller times are initial data.

Each s_i tends to k, so S_(i−k−1)/S_i tends to k^(−k−1) and remains bounded. Normalized delayed norms have the same exponent. The proof needs no signed spectral theorem.

## 4. Leading finite-memory tracking

The approved relaxed block estimates hold for arbitrary signed inputs. Projecting the additional delayed vector orthogonally costs at most its norm and yields the stated two scalar inequalities.

For Q_i=|a_i|+K i^−1/3||z_i||, choose K sufficiently large that its stable decrement Kc i^−1||z_(i−1)|| absorbs the ordinary central cross term. The stable weight decreases between successive times, which is favorable. The remaining ordinary multiplier is at most 1+Ci^−4/3. For fixed lag ℓ=k+1,

|a_(i−ℓ)|+||z_(i−ℓ)|| ≤ C i^1/3 Q_(i−ℓ).

Thus the delay costs at most Ci^(1/3−q) times the running maximum of earlier Q's. Both error exponents are summable when q≥2. Iterating the running-maximum bound proves bounded a and the preliminary stable growth O(i^1/3).

Substituting this preliminary growth into the delay term gives O(i^(1/3−q)), at most O(i^−5/3). The ordinary central forcing is O(i^−4/3), so stable convolution with damping i^−2/3 gives z_i=O(i^−2/3). The central increments are then absolutely summable, with largest tail O(i^−1/3). This proves the limiting central amplitude exists.

At phase-zero endpoints, norm evaluation is bounded and ψ_i(0) is comparable to i^−1/2. Therefore the relative stable error is O(i^−1/6), which vanishes. The resulting endpoint amplitude is finite. The positive completed-run lower bounds, combined with the positive relaxed amplitude, exclude zero and negative limits. This is precisely where positivity is needed; positivity of a signed propagator is never presumed.

## 5. Formal delay coefficient, scalar factors, and recursion

Substituting i=ε^−3, j=x/ε−1 gives

X−r=[q+xε²−(1+kr)ε³]/(kε³),
m=[1−xε²+ε³]/(kε³).

For compacted trees m−1 instead has numerator 1−xε²−qε³. These formulas directly prove both rational β expressions in the text. Their leading coefficients are q^k k^(k−1) for compacted and half this for DFA, at order ε^(3q).

Dividing by H_(i−1) gives H_(i−k−1)/H_(i−1), a product of exactly k inverse scalar steps at times i−1 through i−k. Dividing by H_i instead would give k+1 factors. The proof uses the correct factor in both places. The delayed profile's time parameter is τ_(k+1); its height parameter is (x−ε)τ_(k+1), since j−1+1=j.

At stage ε^(m+2), the new unknown profile φ_m and scalar σ_(m+2) appear in the inherited relaxed Airy operator. Since 3q≥6, the new delayed contribution can involve only profiles through index m+2−3q≤m−4 and scalar stages strictly earlier than the new scalar. Thus it cannot alter the triangular principal operator or its invertibility. Rational Taylor coefficients and fixed Airy differentiation preserve polynomial-Airy forcing. The inherited K_q has diagonal 2d+1, so it is invertible on every finite polynomial space. Its action on constants enforces B_m(0)=0 uniquely through the scalar; A_m(0)=0 fixes the remaining amplitude gauge. These statements prove all finite formal stages, rather than only finitely many checked stages.

The lower boundary remains exact: at j=0 the virtual delayed profile has argument zero, where every profile vanishes. At the top, the physical m=0 coefficient is zero and all formal profiles and their shifted cutoffs vanish for sufficiently large i. The formal extension of the rational expression at m=0 creates no residual there.

## 6. Arbitrary analytic defect and common normalization

At any fixed truncation order, all rational denominators on the logarithmic cutoff remain bounded away from zero, τ_l is analytic for every fixed l≤k+1, and the scalar inverse product is bounded. Fixed derivatives of each profile are controlled by polynomial-Airy envelopes. Shifted arguments differ by O_k(ε+ε³x), preserving an integrable envelope after weakening its exponential decay constant.

The phase mesh has spacing kε. Summing squared errors costs O_k(ε^−1), exactly canceled by N_i² comparable to ε^−1. This uses integrable envelopes, so no unwanted logarithmic loss remains. Cutoff differences lie where x grows like log i, hence their Airy tails are smaller than every fixed inverse power of i. Together with exact lower zeros and a top boundary far beyond the cutoff, finite Taylor matching produces the asserted norm defect for arbitrary prescribed p>1. The fixed exceptional seeds do not enter the asymptotic residual.

All scalar ansätze have leading multiplicative constant one. Writing S_i=P_i N_i/N_(L−1), P_i/G_i→κ, the normalization Z_i=(κ/N_(L−1))H_iΦ_i/S_i makes its central limit one at every truncation. The signed corrections start beyond the already fixed leading scalar exponents. H_i N_i/S_i stays bounded, giving a normalized defect O(i^−p). Subtracting the exact limiting amplitude times Z_i consequently produces an error with central limit zero and bounded norm. This prevents an order-dependent amplitude from entering the proof.

## 7. Delayed zero-limit bootstrap

Assume |α_i|≤C i^−ν for fixed ν≥0. The stable forcing from the central part is bounded by

i^−ν−4/3 + i^−ν−q + i^−p ≤ C(i^−ν−4/3+i^−p).

Let F_i=i^−ν−2/3+i^(2/3−p). Both are decaying powers because p>1. For every fixed power and fixed lag, the ratio of consecutive or delayed values is 1+O(i^−1). Consequently, for all sufficiently large i,

F_i−(1−ci^−2/3)F_(i−1)−Ci^−q F_(i−k−1) ≥ c' i^−2/3 F_i,

since i^−1 and i^−q are negligible relative to i^−2/3. A sufficiently large multiple dominates the finite initial lag values and forcing. Induction proves the stable bound. This is a comparison for a positive scalar norm inequality, not for the original signed vector evolution.

After substitution, the ordinary central terms have tails O(i^−ν−1/3) and O(i^(2/3−p)); the defect has tail O(i^(1−p)). The delayed central tail is O(i^(1−ν−q)), bounded by O(i^−ν−1/3). The delayed stable tails are smaller still: O(i^(1/3−q−ν)) and O(i^(5/3−q−p)). All sums converge for ν≥0, q≥2, p>1. Backward summation is valid because α_infinity=0 was separately established. Thus

α_i=O(i^−ν−1/3+i^(1−p)).

Iteration from ν=0 reaches p−1 after finitely many stages. The norm error is O(i^(1−p)); the stable component is at most O(i^(2/3−p)). The endpoint loses i^1/2, giving O(i^(3/2−p)) relatively. Since p is arbitrary, every requested finite endpoint remainder follows by increasing the formal truncation order. The same positive amplitude works for all of them.

## 8. First ratio correction and monotonicity

Put η_C=1 and η_B=1/2. The leading signed term in the scalar formal equation is

−η_X q^k k^(k−1) k^(−k) ε^(3q) f = −η_X(q^k/k) ε^(3q) f.

It is pure f, so the entire change is Δσ_(3q)=−η_X q^k/k, with Δφ_(3q−2)=0 in the fixed gauge. Earlier stages are identical. Dividing by the leading scalar k gives Δlog σ=−η_X q^k/k² ε^(3q). Scalar matching has coefficient −(q−1) on h_(3q−3), hence

Δh_(3q−3)=η_X q^k/[k²(q−1)].

The endpoint is ε times a finite power series; the gauge ensures all profiles vanish at zero. A profile of index r contributes no earlier than relative order ε^r, and profiles through 3q−2 are identical. Thus no endpoint correction interferes with the earlier scalar order 3q−3. At i=kn, its coefficient becomes

η_X q^k/[k²(q−1)k^(q−1)] = η_X (q/k)^k/(k−2),

exactly the claimed positive correction. Factorials and Stirling corrections are common and cancel. The extra factor two in B/[2^(n−1)R] changes only its limiting amplitude, not its normalized logarithmic coefficients. In particular A_C=ρ_C A_R and A_B=ρ_B A_R/2 in the count normalization used in the theorem.

Agreement of all count coefficients below index 3(k−2), and the claimed increment at that index, follow by multiplying the common relaxed series by exp(A n^(−(k−2))+higher powers). Since k≥3, the first two corrections agree in both models.

For strict monotonicity, use enough finite orders that the logarithmic normalized ratio remainder is o(n^−(k−1)). Its two-value difference is then still o(n^−(k−1)); no derivative bound is assumed. The first positive term contributes −(k−2)A n^−(k−1), while every later retained fractional power has smaller difference. The difference is strictly negative for all sufficiently large n. The leading positive term also shows approach from above. The proof makes no global-in-n monotonicity assertion.

## 9. Independent reproducibility and exact dependency hashes

The independent script imports no producer code. It constructs source recurrences and a separate completed-run dynamic program with an open terminal run, checking all available physical entries for k=3,…,10 and n≤9. It separately derives the factorial transform and verifies the exact scaled β rational substitutions and ratio conversion.

Results:

- 4,968 all-entry source/run comparisons
- 5,976 transformed signed equations
- 16 exact symbolic scaled-β identities
- 16 exact leading ratio-coefficient identities
- 40 compacted/DFA entries from the published tables
- Total: 11,016 independent checks

The producer script also replays successfully with 2,403 checks. Finite ranges cannot certify a theorem for all k or all orders; the preceding algebra and analytic estimates supply those statements.

SHA-256 records:

- Independent script `check_independent.py`: `689e5d3c41b81c077cf1829bb46f6a19832ec2cf6eac69e2d4e36e03d909939a`
- Independent output `independent-output.json`: `881474b4e30f69ec48464951b11bfb52e51d7bf026d212803877074a47138fcd`
- Producer check script `../check_seeds_runs.py`: `d023f1713bb855e330c77c4713d516c671506518535f10fde529a6df12c91777`
- Inherited relaxed leading proof `../../fixed-arity-proof.md`: `9be0c0aaf02b6918a8015c6d059664851d393e9ea8e75ac4a31e082c34434ee2`
- Inherited relaxed all-orders proof `../../all-orders-proof.md`: `7a67a0230c49f4d463fd24c31c94ca04aee32b3a8d1f9382917a6c460804dee0`

The signed-delay template was compared with the independently approved ternary audit, but each k-dependent coefficient, phase boundary, summability exponent, and finite-memory estimate was checked here separately. No extension to k=2 is approved: the product and summability arguments explicitly use q≥2.
