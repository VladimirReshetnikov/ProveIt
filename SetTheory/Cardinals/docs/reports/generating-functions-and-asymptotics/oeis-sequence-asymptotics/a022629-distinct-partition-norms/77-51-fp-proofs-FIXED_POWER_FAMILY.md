# Fixed positive power tilts and polynomial slot multiplicities

Proposed extension for independent review, 1 October 2026. This is one uniform family result, not a set of separate priority claims. Fix α>0 and an integer β≥0, and write

F_(α,β)(q)=∏_{k≥1}(1+k^α q^k)^(k^β)=Σ a_n^(α,β) q^n.

All coefficients are nonnegative real numbers. For integer α they have the usual colored-slot interpretation. Put d=β+1, m_0=((d+1)n)^(1/(d+1)), L_0=log m_0, and C=π²/6.

## Theorem

1. The sequence is strictly increasing for n≥1, with a_0=a_1=1, and

log a_n^(α,β)=αm_0^d(L_0/d−1/d²)+C m_0^d/[α(L_0−1)]+O_(α,β)(m_0^d/L_0³).       (A)

2. Define f, μ, κ_r and V from F_(α,β) as in EXACT_SADDLE_EXPANSION.md, and let t_n be the unique saddle μ(t_n)=n. If m solves t=αlog m/m and W=m^d/log m, then every fixed R≥0 has

a_n^(α,β)=exp(f(t_n)+nt_n)/sqrt(2πV(t_n)) [E_R(t_n)+O_(α,β,R)(W^(−R−1))],

with exactly the same finite Gaussian-moment cumulant polynomial E_R as in that note.

3. Let s=log y, u_*=[d²s/α]/W_0(d²s/(αe)), m_*=u_*^(1/d), L_*=log m_*, where W_0 denotes the positive real Lambert function. For N_(α,β)(y)=min{n:a_n^(α,β)≥y},

N_(α,β)(y)=m_*^(d+1)/(d+1) · [1−(d+1)π²/(6α²L_*(L_*−1))+O_(α,β)(L_*^(−4))].      (B)

The inverse of each exact-saddle approximant A_R exists for large y. Its integer threshold uncertainty is O(W^(−R−1)/t), before rounding, by the same comparison proof as for A022629.

## 1. Positive coefficients and monotonicity

Interpret a slot configuration as selecting a subset of k^β labeled slots at each size k. Its weight is the product of k^α over all selected slots. Its total size is the sum of their sizes. Pick the least-labeled selected slot at the largest occupied size k, move it to size k+1 preserving its label, and retain every other slot. The target label exists since (k+1)^β≥k^β, and no slot at size k+1 was occupied. The map is injective: its unique new largest slot records the moved label. Its weight strictly increases by ((k+1)/k)^α. Summing positive weights proves strict increase for n≥1, even when α is not an integer.

## 2. Bounds that also handle large α

Let g(x)=αlog x−tx and t=αL/m. Fix

0<δ<min(1/2,d/(2α)).

For k≤δm,

k^(β+r) p_k(1−p_k)≤m^(αδ) k^(β+r−α).

Its sum is O(m^e log m), where e=max(αδ,β+r+1−α+αδ)<β+r+1. This is smaller than m^(β+r+1)/L. On δm≤k≤m, concavity and log(k/m)≥−(1−k/m)/δ give

g(k)≥α(L−1/δ)(1−k/m),

so geometric summation gives the required O(m^(β+r+1)/L). The upper tail follows from p_k≤k^αexp(−tk)=(k/m)^α exp(−αL(k−m)/m). Therefore, for every fixed r≥0,

Σ k^(β+r) p_k(1−p_k)=O_(α,β,r)(m^(β+r+1)/L).

An interval of consecutive k of length comparable to m/L about m has p_k bounded away from zero and one, and k^β≍m^β. Consequently

μ~m^(d+1)/(d+1), V≍m²W, |κ_r|≤C_r m^r W (r≥2).

The complex-neighborhood argument from the single-slot note is unchanged, with slot multiplicity k^β included in each sum. For the minor arcs, the same consecutive-window trigonometric estimate is multiplied by m^β. Its noncentral decay is at least exp(−c m^d/L³), while its central Gaussian scale is V^(−1/2). Replacing w by W in the central Taylor argument proves the entire exact-saddle theorem. All constants may depend on the fixed α, β and truncation order; no uniformity as α→0 or β→∞ is claimed.

## 3. Thermal term

The sum–integral error for x^βlog(1+exp g(x)) is O(m^βL), obtained by integrating the absolute derivative (for β=0 use the unimodal estimate). For x^(β+1)/(1+exp(−g(x))), it is O(m^(β+1)), by the same derivative bound and the variance estimates above. Both errors are negligible at every fixed inverse-logarithmic order of their respective main scales.

The hard integrals are

f_hard=αm^d[L/(d(d+1))−1/d²],  μ_hard=m^(d+1)/(d+1).

The portions x≤δm and x≥2m are negligible at every fixed inverse-logarithmic order, by the preceding small-k bound and its integral version; the bounded interval near zero contributes O(1). On the remaining interval put v=tx−αlog x and use its inverse branch through x(0)=m. Then

x'(0)=m/[α(L−1)], x''(0)=−m/[α²(L−1)³],
x'''(0)=m(2L+1)/[α³(L−1)⁵].

The even kernel log(1+exp(−|v|)) multiplying x(v)^β x'(v) has integral C. The second derivative of that amplitude is O(m^d/L³), uniformly in a symmetric interval |v|≤c_(α,δ)L; its complement is exponentially small in L. Odd terms cancel, giving

f(t)=f_hard+C m^d/[α(L−1)]+O(m^d/L³).

For μ, the odd Fermi-step error multiplies x(v)^(β+1)x'(v), whose derivative is O(m^(d+1)/L²). Hence μ=μ_hard+O(m^(d+1)/L²), locating the saddle at m=m_0[1+O(L_0^(−2))]. For Q_0(m)=nt+f_hard, Q_0'(m_0)=0 and Q_0''(m_0)=α(L_0−1)m_0^(d−2). Thus the stationary displacement costs O(m_0^d/L_0³), as does the change in the thermal term. The Gaussian logarithm is O(log m_0), proving (A).

## 4. Inversion

The main entropy H(m)=αm^d(log m/d−1/d²) has derivative αm^(d−1)log m. With u=m^d, the equation H(m)=s is u(log u−1)=d²s/α, which gives exactly u_* above. The thermal perturbation changes m by the relative amount

−C/[α²L_*(L_*−1)]+O(L_*^(−4)).

Raising to the power d+1, dividing by d+1, and using monotonicity yields (B). Exact-saddle inverse localization follows from (log A_R)'~t; differentiation gives the correction bounds O(1/(mW)) for A_0 and O(1/(mW²)) for E_R.

## OEIS specializations and literature boundary

- (α,β)=(1,0): A022629.
- (α,β)=(2,0): A092484, the squared-product sum over distinct partitions.
- (α,β)=(1,1): A266891, product ∏(1+kq^k)^k.

The entry identifications and current literature discussion must be checked directly before publication. Dennis Kinoti Gikunda's March 2026 thesis, The Distribution of the Product of Parts in Integer Partitions, discusses a closely related product. Its Chapter 4, Section 4.2, imposes a shrinking tilt |a|≤r^δ for u=e^a; the present fixed α>0 regime lies outside that stated hypothesis. This is a scope distinction, not a literature-wide priority assertion.
