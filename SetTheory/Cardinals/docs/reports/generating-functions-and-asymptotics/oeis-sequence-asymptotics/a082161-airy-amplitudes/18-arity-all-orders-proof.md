# Relaxed fixed-arity trees: expansion to every finite order

Date: 2026-10-02. Status: full analytic extension submitted for independent review. The leading theorem in `fixed-arity-proof.md` is independently approved in `independent-analytic-audit/`; its reviewed file is unchanged. All constants depend on the fixed integer k≥3 and on the finite expansion order.

## Theorem

For each fixed k≥3 there exist a constant C_k>0 and uniquely determined real coefficients c_(k,r), r≥1, such that for every fixed M≥0,

R_n=C_k (n!)^(k−1)[k^k/(k−1)^(k−1)]^n
 exp{3[k(k−1)/2]^(1/3)a_1 n^(1/3)} n^((2k−1)/3)
 ×[1+Σ_(r=1)^M c_(k,r)n^(−r/3)+O_(k,M)(n^(−(M+1)/3))].

The amplitude C_k is the SAME positive constant at every order. This is a Poincaré expansion to every finite order, not convergence of the infinite formal series. It has no logarithmic powers. Put q=k−1, B=(2/q)^(1/3), and λ=a_1/B. The first coefficient is

c_(k,1)=k^(−1/3) λ²(3q²+27q+23)/(45q).

The second coefficient is

c_(k,2)=k^(−2/3)[h_1²/2+λ(4q³+321q²+429q+126)/(270q)],
h_1=λ²(3q²+27q+23)/(45q).

Every later coefficient is computable from the exact recursion below. The theorem concerns relaxed trees only.

## 1. Approved analytic input

Use the phase spaces, fixed weighted norms, and exact transfer T_i from the approved leading proof. Let ε=i^(−1/3), x=ε(j+1), f(x)=Ai(a_1+Bx), and

p(x)=−(q+3)x²/(6q)−(q−1)λx/(3q),
F_i(j)=χ(x/log i)[f(x)+εp(x)f(x)],
N_i=||F_i||_ω, ψ_i=F_i/N_i,
β=(7k−6)/6,
t_i=k[1+λε²+βε³], s_i=t_iN_i/N_(i−1), A_i=T_i/s_i.

The approved estimates are N_i≍i^(1/6), N_i/N_(i−1)=1+O(i^−1), ψ_i(0)≍i^−1/2 at residue zero, and the block estimates

A_i = [[1+O(i^−4/3), O(i^−1)], [O(i^−4/3), D_i]],
||D_i||≤1−c_k i^−2/3,

relative to span(ψ_(i−1)) and span(ψ_i) and their orthogonal complements. The exact normalized solution has bounded norm and its central projection tends to a positive constant C. The leading proof supplies this positivity for the exact relaxed initialization by the published lower Theta estimate. These are the only nontrivial analytic facts inherited here; no higher-order spectral expansion is assumed.

## 2. Exact evolving formal equation

Write τ=(1−ε³)^(−1/3). The exact up coefficient in these variables is

U(ε,x)=q²[1−xε²+(k+1)ε³]/[q+xε²−ε³].

Let Φ(ε,x)=Σ_(m≥0)ε^m φ_m(x) and σ(ε)=k+Σ_(r≥2)σ_r ε^r. The equation for an evolving scalar-profile ansatz is

U(ε,x)Φ(ετ,(x−ε)τ)+Φ(ετ,(x+qε)τ)
=σ(ε)Φ(ε,x).                                           (1)

Set φ_0=f and σ_2=kλ. The omitted ε term vanishes by zero critical drift. All profiles obey the exact bottom condition φ_m(0)=0.

At order ε^(m+2), m≥1, the only new profile is φ_m and the only new scalar is σ_(m+2); profiles φ_(m+1),φ_(m+2) cancel out because the critical zero and first moments are k and zero. The equation has the form

k L_q φ_m=σ_(m+2)f+P_m f+Q_m f′,
L_q=(q/2)D²−x−λ,                                       (2)

where P_m,Q_m are known polynomials formed from earlier stages. Indeed f″=(2/q)(x+λ)f, so differentiation preserves polynomial combinations of f,f′, and every Taylor coefficient of U and τ is polynomial in x.

## 3. Polynomial inverse and exact boundary gauge

For polynomials A,D (D here denotes a coefficient polynomial, not differentiation),

L_q(Af+D f′)
=[(q/2)A″+2(x+λ)D′+D]f+[qA′+(q/2)D″]f′.

To solve L_q(Af+D f′)=P f+Q f′, eliminate A:

K_q D:=−(q/4)D‴+2(x+λ)D′+D=P−Q′/2,
A′=Q/q−D″/2.                                           (3)

On polynomials of degree≤d, K_q is triangular with diagonal 1,3,…,2d+1, so it is invertible. Also K_q(1)=1. Adding a scalar to P changes only the constant term of D. Consequently the new scalar in (2) uniquely enforces D_m(0)=0. Integrating A′ with A_m(0)=0 fixes the amplitude gauge. Since f(0)=0 and f′(0)≠0, D_m(0)=0 is exactly φ_m(0)=0.

This proves existence and uniqueness of the recursion in this gauge for every finite m. All coefficients are rational functions of q with polynomial dependence on λ. There is no formal resonance and no logarithmic profile term. At m=1 one gets D_1=0, A_1=p and σ_3=kβ, matching the approved leading profile.

## 4. Scalar matching with a common leading constant

Choose one sufficiently large starting time L. Define

G_i=k^i exp(3λ i^(1/3))i^β,
P_i=Π_(m=L)^i t_m,
S_i=Π_(m=L)^i s_m=P_iN_i/N_(L−1).

Then P_i/G_i→κ>0. For each finite formal truncation choose

H_i=G_i exp[Σ_(r=1)^J h_r i^(−r/3)],                    (4)

with leading constant EXACTLY one. Expand log[H_i/H_(i−1)] in ε. Its order-ε² and order-ε³ terms agree with log[σ(ε)/k]. A new h_r first enters at order ε^(r+3) with coefficient −r/3. Hence every further scalar coefficient can be matched uniquely to arbitrary finite order, without a new logarithm. The power i^β already accounts for the only order-i^−1 summation.

This scalar convention is essential: an order-dependent multiplicative constant is never absorbed into C_k.

## 5. Arbitrarily small analytic defect

For any prescribed real p_*>1, choose sufficiently many formal profile and scalar stages, and form

Φ_i(j)=χ(x/log i)Σ_(m=0)^M ε^m φ_m(x).

Then

||T_i[H_(i−1)Φ_(i−1)]−H_iΦ_i||_ω
≤C_(k,p_*) H_iN_i i^(−p_*).                            (5)

Here are explicit analytic reasons formal matching proves this bound. Every fixed derivative of every φ_m is bounded near zero and, for x≥1, by a polynomial in x times exp(−c_k x^(3/2)); the envelope may contain f′ and need not vanish at zero. On x≤2log i, the exact denominators q+xε²−ε³ stay bounded away from zero for large i. Rational Taylor remainders are fixed powers of ε times polynomials in x. The factor τ is analytic near ε=0. Shifted arguments differ from x by O_k(ε+ε³x), so profile Taylor remainders have the same square-integrable envelope after slightly decreasing c_k. Summing squared errors on a mesh of width kε costs O_k(ε^−1), canceled by N_i²≍ε^−1.

Every absent bottom forward input is at j−1=−1, corresponding to argument zero. Each φ_m(0)=0 exactly, so no unproved boundary approximation is introduced. The moving top lies far beyond the cutoff. Cutoff mismatches are supported where x≥log i−O_k(ε+ε³log i), and exp[−c_k(log i)^(3/2)] dominates every fixed polynomial in i. All such errors are smaller than any required power. Taking more complete formal stages therefore proves (5) for arbitrary p_*; no assertion about a convergent infinite formal series is involved.

For a conservative concrete stage choice, match the full recurrence and scalar ratio through ε^K with K>3p_*+4 and retain every profile needed through that stage. Taylor's theorem then leaves strictly more powers than (5) requires.

Set

Z_i=(κ/N_(L−1))H_iΦ_i/S_i.                              (6)

Since H_i/G_i→1 and P_i/G_i→κ, while Φ_i−F_i=o(N_i), one has Z_i−ψ_i→0 in norm. Thus its central projection tends to one for EVERY truncation. Also H_iN_i/S_i stays bounded. Dividing (5) by S_i gives

||Z_i−A_i Z_(i−1)||_ω=O_(k,p_*)(i^(−p_*)).              (7)

## 6. Zero-limit bootstrap transfers arbitrary order

Let y_i be the exact solution normalized by S_i, and let C be its limiting central projection from the approved leading theorem. For one chosen high-order Z_i, set E_i=y_i−CZ_i and write

E_i=α_iψ_i+w_i, w_i perpendicular to ψ_i.

By (6), α_i→0, and E_i is bounded. The approved blocks and (7) give

|α_i−α_(i−1)|≤C_k i^−4/3|α_(i−1)|+C_k i^−1||w_(i−1)||+C i^(−p_*),
||w_i||≤(1−c_k i^−2/3)||w_(i−1)||+C_k i^−4/3|α_(i−1)|+C i^(−p_*). (8)

Suppose α_i=O(i^(−ν)) for a fixed ν≥0. Stable convolution, with kernel bounded by exp[−c_k(i^(1/3)−m^(1/3))], yields

||w_i||=O(i^(−ν−2/3)+i^(2/3−p_*)).                     (9)

The finite initial contribution decays stretched-exponentially. The effective window has length O(i^(2/3)), which multiplies source sizes i^(−ν−4/3) and i^(−p_*), respectively. This also follows by a power supersolution: the damping i^−2/3 dominates a power's one-step relative variation O(i^−1).

Substitution into the first inequality in (8) gives summable increments. Summing backward from α_infinity=0 proves

α_i=O(i^(−ν−1/3)+i^(1−p_*)).                            (10)

Indeed the slowest summation is Σ_(m>i)m^(−ν−4/3)=O(i^(−ν−1/3)); the remaining tails are O(i^(−ν−2/3)), O(i^(2/3−p_*)), and O(i^(1−p_*)). Start with ν=0 and iterate ν↦min(ν+1/3,p_*−1). After finitely many iterations,

||E_i||=O(i^(1−p_*)).                                  (11)

This does not infer a small error merely from a formal solution: it uses both the proven stable gap and the prescribed zero limit of the central error.

At a residue-zero endpoint, bounded ω_0 gives |E_i(0)|≤C_k||E_i||. Since ψ_i(0)≍i^−1/2, the relative endpoint error is O(i^(3/2−p_*)). For a desired expansion through n^(−M/3), choose p_*>3/2+(M+1)/3 and retain sufficiently many formal terms. Equations (4),(6),(11), Taylor expansion of Φ_i(0), and Stirling then prove the theorem. C is unchanged by the truncation because every Z_i was normalized to central limit one.

## 7. Endpoint coefficients and first explicit correction

The gauge gives φ_m(0)=0 for every m. Therefore

Φ_i(0)=ε f′(0)[1+Σ_(r≥1)e_r ε^r]

as a finite Taylor expansion to any requested order. In fact e_1=0: f″(0)=0, φ_1=p f=O(x²), and higher profiles are multiplied by ε² or smaller. Endpoint corrections begin at ε². Stirling for (qn)!/(n!)^q begins at i^−1=ε³, so neither affects the first relative coefficient.

The order-ε⁴ scalar calculation gives

σ_4=−λ² k(6q²−81q+46)/(270q).

The order-ε⁴ coefficient in log[H_i/H_(i−1)] is −h_1/3, while the same coefficient in log[σ(ε)/k] is σ_4/k−λ²/2. Thus

h_1=λ²(3q²+27q+23)/(45q).

At i=kn, this gives c_(k,1)=k^(−1/3)h_1 as stated. For k=3 it is 89a_1²/(90·3^(1/3)); the algebra also reduces at k=2 to 53a_1²/90, although this theorem uses the k≥3 analytic input only.

The next independently reproducible symbolic stage gives

σ_5=−λk(8q³−327q²+657q−92)/(810q),
h_2=λ(4q³+309q²+531q−46)/(270q),
e_2=λ(6q²−51q+86)/(135q).

Here log[G_i/G_(i−1)] has ε⁵ coefficient λ/3, so h_2=(3/2)[λ/3−σ_5/k+λβ]. The endpoint coefficient follows from e_2=f‴(0)/(6f′(0))+p′(0)+φ_2′(0)/f′(0). Therefore c_(k,2)=k^(−2/3)(h_1²/2+h_2+e_2), yielding the displayed formula. At q=2 this is 3^(−2/3)[7921a_1⁴/16200+115a_1/27]. The full exact calculation and its two-component residual assertions are in `coefficients/derive_c2.py`, with output in `coefficients/c2-output.txt`.

The exact symbolic source for the first calculation is `/workspace/shared/root-fixed-arity-recursion/check_general.py`; its polynomial solution checks both f and f′ coefficients at order ε⁴. A local reproducible copy is included alongside this document. Later coefficients use (1)–(4), the ordinary endpoint Taylor product, and Stirling; they are universal for this recurrence and gauge, while the amplitude is fixed by the exact initial data.

## Source/dependency record and scope

The exact recurrence, factorial conversion, and positive Theta lower bound are from Dastidar–Wallner, arXiv:2404.08415v1, equations (3)–(5) and Theorem 1, https://arxiv.org/html/2404.08415v1 . The singular gap and leading estimates used here are proved in the independently approved `fixed-arity-proof.md`. The structure of the error bootstrap is the same as the independently approved ternary `all-orders-reduction.md`, with the general-k operator (3) and all fixed-k constants checked explicitly here.

This document does not prove compacted or DFA all-orders expansions; those require an exact signed-delay transform, seed handling, and a positive lower comparison. None is silently inferred from the relaxed theorem.
