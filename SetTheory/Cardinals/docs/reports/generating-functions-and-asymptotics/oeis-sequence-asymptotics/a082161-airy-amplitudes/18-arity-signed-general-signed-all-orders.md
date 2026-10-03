# Fixed-arity compacted trees and finite-language DFAs: signed-delay extension

Date: 2026-10-02. Status: producer proof submitted for independent review. This document is separate from the approved relaxed leading proof and the separately reviewed relaxed all-orders extension. Fix k≥3 and q=k−1 throughout. Constants depend on k and finite expansion order.

## Results

Let R_n=r(qn,n), C_n=c(qn,n), and B_n=b(qn,n) be respectively the relaxed, compacted, and DFA arrays with the exact source conventions below. Define

G_(k,n)=(n!)^q(k^k/q^q)^n exp[3(kq/2)^(1/3)a_1 n^(1/3)]n^((2k−1)/3).

There are positive constants A_k^C,A_k^B such that each array has a finite-order expansion for every M, with the same amplitude at every order:

C_n=A_k^C G_(k,n)[1+Σ_(r=1)^M c_r^C n^(−r/3)+O_(k,M)(n^(−(M+1)/3))],
B_n=A_k^B 2^n G_(k,n)[1+Σ_(r=1)^M c_r^B n^(−r/3)+O_(k,M)(n^(−(M+1)/3))].

The relaxed expansion has coefficients c_r^R. Put

ρ_C=lim C_n/R_n>0, ρ_B=lim B_n/[2^(n−1)R_n]>0.

The first logarithmic differences are

log[C_n/(ρ_C R_n)]=(q/k)^k/(k−2)·n^(−(k−2))+O_k(n^(−(k−2)−1/3)),
log[B_n/(ρ_B 2^(n−1)R_n)]=(q/k)^k/[2(k−2)]·n^(−(k−2))+O_k(n^(−(k−2)−1/3)). (A)

Consequently c_r^C=c_r^B=c_r^R for r<3(k−2). At r=3(k−2), the compacted coefficient increases by (q/k)^k/(k−2), and the DFA coefficient increases by half that amount. In particular the relaxed c₁ and c₂ remain valid for both models for every k≥3. Neither the amplitude values nor convergence of the formal infinite series is claimed.

## 1. Exact source arrays and exceptional seed

The source recurrences, for m≥1 and x≥qm, are

r(x,m)=r(x,m−1)+(m+1)r(x−1,m),
c(x,m)=c(x,m−1)+(m+1)c(x−1,m)−(m−1)c(x−k,m−1),
b(x,m)=2b(x,m−1)+(m+1)b(x−1,m)−m b(x−k,m−1).

All three have a(x,0)=1 for x≥0 and vanish below the physical diagonal x<qm, apart from the DFA auxiliary b(−1,0)=1; all other missing source entries are zero. The auxiliary is required to match the one-state source count: b(q,1)=2−1=1. For x≥q+1, the first-row recurrence is b(x,1)=2b(x−1,1)+1, hence

b(x,1)=2^(x−q+1)−1 (x≥q).

The compacted first row agrees with the relaxed first row because its negative coefficient m−1 vanishes there. These conventions are essential; the ordinary rational transform must never be applied to the auxiliary negative factorial.

For compacted trees put a=c; for DFAs put a(x,m)=b(x,m)/2^m. In both cases define

i=x+m, j=x−qm, X=(qi+j)/k, m=(i−j)/k,
d_i(j)=q^(2X)a(X,m)/X!.

The physical phase spaces are J_i={0≤j≤i:j≡i mod k}. Through time i=k the vectors have the diagonal entries

d_i(i)=q^(2i)/i! (0≤i≤k).

There are no other entries before time k. At time k the additional bottom entry is

d_k(0)=q^(2q)/q! for compacted,
d_k(0)=q^(2q)/(2q!) for DFA.

Thus the DFA bottom seed is half the relaxed one, while the compacted seed agrees. This follows from the just-verified first rows, not a transformed auxiliary value.

For i≥k+1 the exact transformed recurrence is

d_i=T_i d_(i−1)−D_i d_(i−k−1),
(D_i v)(j)=β_i(j)v(j−1),
β_i(j)=δ_m q^(2k)/(X)_k,
δ_m=m−1 for compacted, δ_m=m/2 for DFA,                 (1)

where δ_m is defined to be zero at m=0. A missing delayed input is zero. The source factorial quotient gives (1) directly; (X)_k=X(X−1)⋯(X−k+1). For i≥k+1 every physical X≥k, so these denominators are nonzero. At j=0 the delayed input is absent. For j≥1, it is in the delayed physical phase exactly when m≥1. Early exceptional data have already been handled above.

## 2. Positive completed-run representation and lower amplitudes

A path from (0,0) to (qn,n) has n completed horizontal runs, of lengths ℓ_m at levels m=0,…,n−1, each followed by a vertical step. Its prefix constraints are Σ_(r=0)^m ℓ_r≥q(m+1), and its total horizontal length is qn. The relaxed weight of a level-m run is V_m(ℓ)=(m+1)^ℓ.

For compacted trees the exact completed-run weight is

W_m^C(ℓ)=V_m(ℓ)[1−m/(m+1)^k·1_(ℓ≥k)].                 (2)

For normalized DFAs a=b/2^m, the first run has weight V_0(ℓ)/2 for every allowed ℓ≥q. At subsequent levels m≥1 the exact weight is

W_m^B(ℓ)=V_m(ℓ)[1−1/(2(m+1)^q)·1_(ℓ≥k)].              (3)

Here is an algebraic/combinatorial verification rather than an assumption of positivity for the signed recurrence. In a completed run of length at least k immediately before the rise from level m to m+1, remove its final k horizontal steps. The removed relaxed weight is (m+1)^k. The remaining legal prefix ends at source (x−k,m); removing those final steps preserves the earlier barrier constraints. The negative term at destination level m+1 has coefficient m for compacted trees, and (m+1)/2 for normalized DFAs. Restoring this marked final block gives exactly the subtracted fractions in (2),(3). Distinct completed runs are independent choices in this expansion; expanding their product reproduces the recurrence, including the unmodified final open horizontal run. At the endpoint (qn,n), that final open run has length zero by the diagonal constraint.

The DFA level-zero run needs separate treatment. If ℓ≥k, the ordinary negative term gives fraction 1/2. If ℓ=q=k−1, the auxiliary b(−1,0)=1 gives exactly the same half weight. Thus every permitted first run has factor 1/2, including the exceptional shortest one. This verifies (3) and the overall factor 2^(n−1), not merely 2^n.

All factors in (2),(3) are strictly positive. Under the relaxed path probability measure,

C_n/R_n=E_n Π_(m=1)^(n−1)[1−m/(m+1)^k·1_(ℓ_m≥k)],
B_n/[2^(n−1)R_n]=E_n Π_(m=1)^(n−1)[1−1/(2(m+1)^q)·1_(ℓ_m≥k)].

Therefore, uniformly in n,

0<P_C:=Π_(m≥1)[1−m/(m+1)^k]≤C_n/R_n≤1,
0<P_B:=Π_(m≥1)[1−1/(2(m+1)^q)]≤B_n/[2^(n−1)R_n]≤1.   (4)

Both products are positive because their defects are summable for k≥3 and every factor is positive. These bounds will prove that the limiting amplitudes cannot vanish.

## 3. Global delayed operator bounds

Use the approved fixed weight ω from the relaxed proof, with 0<c_k≤ω≤C_k from the approved leading proof. For sufficiently large i, every physical X is comparable to i and every factor X−r, 0≤r<k, is bounded below by a positive k-dependent multiple of i. Also |δ_m|≤C_k i. Thus

||D_i||≤C_k i^(1−k)=C_k i^(−q).                        (5)

This is a global bound over all physical heights; it is not limited to the Airy window. The shift j↦j−1 is injective and the bounded weight ratios convert the scalar coefficient bound into (5).

Normalize with the SAME leading relaxed S_i=Πs_i and corrected ψ_i as in the approved leading proof. Over k+1 steps, S_(i−k−1)/S_i is bounded and tends to k^(−k−1). Hence

y_i=A_i y_(i−1)−E_i y_(i−k−1),
A_i=T_i/s_i, ||E_i||=O_k(i^(−q)).                       (6)

For y_i=a_iψ_i+z_i with z_i perpendicular to ψ_i, the relaxed blocks give

|a_i−a_(i−1)|≤C i^−4/3|a_(i−1)|+C i^−1||z_(i−1)||
 +C i^(−q)(|a_(i−k−1)|+||z_(i−k−1)||),
||z_i||≤(1−c i^−2/3)||z_(i−1)||+C i^−4/3|a_(i−1)|
 +C i^(−q)(|a_(i−k−1)|+||z_(i−k−1)||).                  (7)

Let Q_i=|a_i|+K i^−1/3||z_i|| for sufficiently large K. Stable damping absorbs the ordinary cross coupling, while the delay contributes at most C i^(1/3−q)Q_(i−k−1). A running maximum is bounded by a product of factors 1+C i^−4/3+C i^(1/3−q), which converges because q≥2. Thus a_i is bounded and initially z_i=O(i^(1/3)). Substitute this coarse bound into (7): the delay forcing is O(i^(1/3−q))≤O(i^−5/3). Stable convolution then gives z_i=O(i^−2/3), and backward tail summation of the central increments gives

a_i→a_infinity, a_i−a_infinity=O(i^−1/3).

Endpoint evaluation loses i^(1/2), yielding a finite leading endpoint limit. The lower bounds (4) and the positive relaxed amplitude imply that each model's limit is strictly positive. No positivity of the signed propagator is assumed.

## 4. Exact delayed formal equations

Put ε=i^−1/3, x=ε(j+1), τ_l=(1−lε³)^−1/3. The relaxed U(ε,x) is the one in the separate relaxed all-orders proof. Let

D_k(ε,x)=Π_(r=0)^(k−1)[q+xε²−(1+kr)ε³].

The exact Airy-scaled delay coefficients are

β^B(ε,x)=[q^(2k)k^(k−1)/2] ε^(3q)(1−xε²+ε³)/D_k(ε,x),
β^C(ε,x)=q^(2k)k^(k−1) ε^(3q)(1−xε²−qε³)/D_k(ε,x).   (8)

The compacted formula is used where m≥1; at m=0 both the actual delay and the profile delayed input vanish far outside the cutoff, so the formal equation creates no boundary issue.

For Φ=Σ ε^m φ_m and scalar step ratio σ(ε), write

Q_k(ε)=Π_(l=1)^k σ(ετ_l)^−1.

Dividing the original recurrence by H_(i−1), not H_i, gives

U Φ(ετ_1,(x−ε)τ_1)+Φ(ετ_1,(x+qε)τ_1)
−β^X(ε,x)Q_k(ε)Φ(ετ_(k+1),(x−ε)τ_(k+1))
=σ(ε)Φ(ε,x).                                          (9)

The inverse product has k factors; after normalization by H_i, the delay in (6) instead has k+1 factors. This distinction fixes the leading ratio constant.

Use exactly the gauge φ_m=A_mf+B_mf′ with A_m(0)=B_m(0)=0. The delay begins at ε^(3q), so at order ε^(m+2) the new unknowns remain only φ_m and σ_(m+2); the delay contribution at that stage is already known from lower stages. Every forcing is polynomial-Airy. The same K_q inverse, with diagonal 2d+1, therefore constructs every stage uniquely without logarithms. All profiles vanish exactly at the bottom, including the delayed input.

## 5. Arbitrary-order remainder and delayed bootstrap

For each p>1, perform sufficiently many formal stages in (9), match

H_i=k^i exp(3λi^(1/3))i^β exp[Σ_(r=1)^J h_r i^(−r/3)],

with leading constant one, and use the same logarithmic Airy cutoff. Then

||T_i[H_(i−1)Φ_(i−1)]−D_i[H_(i−k−1)Φ_(i−k−1)]−H_iΦ_i||
≤C_(k,p)H_iN_i i^(−p).                                 (10)

The full remainder proof from the relaxed all-orders document applies with finitely many extra rational factors and fixed shifts: D_k is bounded away from zero on the cutoff; every τ_l is analytic; H_(i−k−1)/H_(i−1) is a bounded product of k inverse scalar factors; all fixed profile derivatives have square-integrable polynomial Airy envelopes. The mesh normalization cancels the ε^−1 square-sum factor. At j=0 the delayed input argument is exactly zero. The physical top is far outside all shifted cutoffs. Early seeds are fixed finite data, not asymptotic errors.

The common normalization Z_i=(κ/N_(L−1))H_iΦ_i/S_i again has central projection tending to one for every truncation. Its defect in the normalized delayed recurrence is O(i^−p). Let a_infinity be the exact model's positive limiting projection, subtract a_infinity Z_i, and decompose the error as α_iψ_i+w_i. Then α_i→0 and w_i is bounded. Its equations are (7) with these errors and added O(i^−p).

If α_i=O(i^(−ν)), stable power supersolutions give

||w_i||=O(i^(−ν−2/3)+i^(2/3−p)).                        (11)

To check the delayed term explicitly, it adds C i^(−q)||w_(i−k−1)||. For each power supersolution, its relative O(i^−1) step variation and the delayed O(i^(−q)) coefficient are absorbed by half the positive decrement c i^−2/3, since q≥2. The central delayed source O(i^(−ν−q)) is no larger than the ordinary O(i^(−ν−4/3)) forcing. A sufficiently large supersolution dominates the finite initial k+1 values and closes induction.

Substitute (11) into the central increment inequality. Delayed central terms have summable tails O(i^(1−ν−q)), bounded by O(i^(−ν−1/3)); delayed stable terms are still smaller. The remaining terms are exactly those of the relaxed bootstrap. Backward summation from α_infinity=0 gives

α_i=O(i^(−ν−1/3)+i^(1−p)).

Iterate ν from zero to p−1 in finitely many steps. The resulting norm error is O(i^(1−p)), and the relative endpoint error is O(i^(3/2−p)). Since p is arbitrary, this proves every finite-order expansion with the same positive amplitude. Nothing in this transfer requires a spectral theorem for a signed companion matrix.

## 6. First differences and eventual monotonicity

The leading term of β^B is [q^k k^(k−1)/2]ε^(3q); multiplying Q_k(0)=k^(−k) gives (q^k/(2k))ε^(3q). The compacted value is twice this. Thus the first altered scalar is

σ_(3q)^B−σ_(3q)^R=−q^k/(2k),
σ_(3q)^C−σ_(3q)^R=−q^k/k.

This pure-f forcing is absorbed entirely into the scalar; the newly solved profile at that order is unchanged. All earlier scalar/profile stages agree. In the scalar logarithm the first difference is therefore −q^k/(2k²) ε^(3q) for DFA and twice that for compacted. Since h_(3q−3) enters that log step with coefficient −(q−1),

h_(3q−3)^B−h_(3q−3)^R=q^k/[2k²(q−1)],
h_(3q−3)^C−h_(3q−3)^R=q^k/[k²(q−1)].

No endpoint profile correction reaches this order: all profiles through index 3q−2 agree, and every profile vanishes at x=0. Evaluating at i=kn yields (A). The Stirling and factorial factors cancel in the ratios.

Both normalized ratios approach their limits from above and are eventually strictly decreasing. For a rigorous discrete conclusion, take the all-orders logarithmic ratio expansion far enough that its remainder is o(n^(−(k−1))). Subtract its values at n+1 and n. The leading term A n^(−(k−2)), A>0, contributes −(k−2)A n^(−(k−1)); every retained higher power contributes smaller order, and the difference of the two remainders is still o(n^(−(k−1))). This establishes strict decrease without differentiating an uncontrolled remainder.

## Reproducible checks and dependencies

`check_seeds_runs.py` passes 2,403 exact rational checks for k=3,…,8 and n≤7. It compares source recurrences with the completed-run sums, checks the exceptional first rows and transformed seeds, and checks the complete signed delayed recurrence. These finite checks supplement the algebraic proofs, not the asymptotic arguments.

Primary recurrence source: Dastidar–Wallner, arXiv:2404.08415v1, Propositions 10–11, https://arxiv.org/html/2404.08415v1 . The DFA auxiliary convention is stated and independently derived from its first row here; it is not obtained by applying the factorial transform at negative x. The fixed weighted singular gap and leading residuals are inherited from the independently approved fixed-k relaxed proof. The general formal polynomial inverse and scalar matching are in the companion relaxed all-orders proof. The delayed norm bootstrap follows the separately independently reviewed ternary signed-delay argument, with the global exponent q≥2 verified explicitly in (5)–(11).
