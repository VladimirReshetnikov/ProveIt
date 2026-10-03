# A202061: second-order upper coefficient bound

Research derivation, 2 October 2026. This is a separate working note; it does not modify any frozen or audited release. The argument below uses the exact positive representation, uniform fixed-q transfer, critical root derivatives, and first-hit estimate from the audited sharp-deficit and foundation reports. This note itself needs independent review.

## Statement

Let D_n=n log(mu)−log a_n, L=log n, l=log L,

H=n^(2/3)L^(1/3), F=H²/n=n^(1/3)L^(2/3),
C_*=(3π²α²/(2v))^(1/3).

Then there is a constant K such that, for all sufficiently large integers n,

D_n ≥ C_* F [1+(7/3)l/L] − K F/L.                 (T)

Thus the coefficient-upper/deficit-lower side of the proposed second logarithmic term is rigorous subject to review of the argument below. No coefficient amplitude or third logarithmic constant is claimed.

## 1. Inputs and notation

Write ρ=1/mu, t=t_*, and let w(e,q,d) be the exact critically tilted macro-step weight in the audited sharp upper bound. Here e≥1 is macro-length, q≥1 is the downward parameter, d is height increment, and legality at height h is precisely q≤h. The unrestricted critical row has mass

m_*=sum_(e,q,d) w(e,q,d)<1.

For small real (s,θ), define

W_q(s,θ)=sum_(e,d)w(e,q,d)exp(se+θd).

The audited transfer estimate gives, uniformly in a fixed real neighborhood of zero,

W_q(s,θ) ≤ C q^(−3/2)exp[q Ψ(s,θ)],
Ψ(s,θ)=(s+vθ²/2)/α+O(s²+|sθ|+|θ|³).          (1)

For every fixed q, W_q is analytic near zero and W_q(s,θ)→W_q(0,0) uniformly as (s,θ)→0. The constants in these assertions do not depend on q.

The exact terminal factor after a prefix of macro-length e and final height h, at total word-length n, is

ρ^(n−1−e)t^(1−h),

apart from the original factor ρ for the first letter. Finally, for fixed D_0>0 supplied by the foundation's first-hit estimate and fixed R,

a_n^[>RH] ρ^n ≤ C exp[−R²F/(4D_0)].            (2)

## 2. A quantitative truncated-row estimate

For r→∞ let

κ(r)= (1/2)log r + loglog r − C_0/2,

where C_0 is any fixed constant. Then, for fixed Q and sufficiently large r,

sum_(Q<q≤r) q^(−3/2)exp[κ(r)q/r]
 ≤ C Q^(−1/2) + o(1) + C exp(−C_0/2),         (3)

where o(1) is uniform for r above any threshold tending to infinity. The constants C can be chosen independently of C_0 once r is sufficiently large (depending on that fixed C_0).

Proof: κ(r) is positive and asymptotic to (log r)/2. Split the sum at r/κ and r/2. In the first range exp(κq/r)≤e, giving O(Q^(−1/2)). In the second range its sum is at most

C(κ/r)^(1/2) exp(κ/2)=O(r^(−1/4)log r)=o(1).

For q≥r/2, use q^(−3/2)≤C r^(−3/2) and sum the geometric progression. The result is

C r^(−1/2)exp(κ)/κ ≤ C exp(−C_0/2),

because exp(κ)=r^(1/2)(log r)exp(−C_0/2) and log r/κ remains bounded. Empty ranges and integer rounding only improve or change these bounds by fixed factors.

Consequently, whenever vanishing tilts s,θ satisfy uniformly for q≤h

q Ψ(s,θ) ≤ κ(r)q/r+o(1),
q≤h≤r, r→∞ uniformly,

one can make the row limsup strictly less than 1 by choosing C_0 sufficiently large. Indeed, first choose Q so that the first error in (3) is smaller than a fixed fraction of 1−m_*, then C_0 so the last error is likewise small; the finitely many q≤Q have limiting sum at most m_*.

## 3. Finite-n potential and exact affine calibration

Fix a sufficiently large R, chosen below. Set

δ=ε=L^(−12),
V_n(y)= α/[2L(y+ε)] {log[H(y+ε)]
                         +2loglog[H(y+ε)]−C_0},  0≤y≤R,
B_n=α/(2L){log H+2loglog H−C_0}.               (4)

All logarithms are well defined for sufficiently large n, since εH→∞. B_n lies in a fixed compact subinterval of (0,∞). For A>0 put

J_n(A)=min_(0≤y≤R){Ay+V_n(y)}.                 (5)

Let p_*(s) be the momentum of the leading Kepler arch with parameter B_n:

y_*(s)=M sin²u, s=(u−sin u cos u)/π,
M³=2vB_n/π², p_*(s)=−y_*'(s)/v,
p_*'(s)=B_n/y_*(s)².

Define

p_n(s)=p_*(δ+(1−2δ)s), 0≤s≤1,
g_n(1)=0,
g_n'(s)=v p_n(s)²/2−J_n(p_n'(s)),
f_n(s,y)=g_n(s)+p_n(s)y.                       (6)

This is an exact finite-n calibration:

−∂_s f_n+(v/2)(∂_y f_n)²
 =J_n(p_n')−p_n'y ≤ V_n(y).                    (7)

Near each Kepler endpoint p_* is O(s^(−1/3)), p_*' is O(s^(−4/3)), and p_*'' is O(s^(−7/3)), with uniform constants for B_n in its compact range. Therefore

||p_n||∞=O(L^4), ||p_n'||∞=O(L^16),
||p_n''||∞=O(L^28).                            (8)

For sufficiently large n, V_n is strictly convex on [0,R]: direct differentiation gives a positive second derivative, since log[H(y+ε)] tends uniformly to infinity. Hence the minimizer in (5) is unique, J_n is C¹ and 0≤J_n'(A)≤R, including possible boundary minimizers. The identity g_n''=vp_np_n'−J_n'(p_n')p_n'' then shows

||f_n||_(C²([0,1]×[0,R]))=O(L^28),
||∂_s f_n||∞=O(L^16), ||∂_y f_n||∞=O(L^4).     (9)

The C² norm bound includes the bounded value of f_n. For J_n itself one may use 0<J_n(A)≤AR+V_n(R) and (8).

## 4. Value of the calibration, including endpoints

Uniformly for A in the range of p_n',

J_n(A) ≥ 2sqrt(B_n A)
 −(C/L)sqrt(A)(1+|log A|)−εA.                  (10)

Here is an elementary proof. Put a=α/(2L), B=B_n and u=y+ε. On ε≤u≤R+ε,

V_n(y) ≥ [B+a log u−a]/u,
B+a log u−a ≥ B/2                              (11)

for large n, since log u≥−12log L and
2log(log(Hu)/log H)≥−1. Set λ=sqrt(B/A), r=u/λ. After adding Aε, the expression Ay+V_n(y), divided by sqrt(AB), is bounded below by

r + [1+(a/B)(log λ−1)+(a/B)log r]/r.

If r is outside [1/8,8], (11) bounds this below by r+1/(2r)≥4, so the claimed lower bound holds. Inside that interval, r+1/r≥2, and the remaining term is at worst

−C(a/B)(1+|log λ|).

Because B is bounded above and below, this proves (10).

The Kepler endpoint estimates imply the uniform integrability bound

integral_0^1 sqrt(p_n')(1+|log p_n'|) ds ≤ C.    (12)

Indeed the comparison near zero is s^(−2/3)(1+|log s|), with the truncated/reparametrized version bounded in integral uniformly in δ. Also integral p_n' ds=O(δ^(−1/3)). Substituting (10) into (6),

f_n(0,0) ≥ integral_0^1[2sqrt(B_n p_n')−vp_n²/2]ds
          −O(1/L)−O(εδ^(−1/3)).               (13)

For the full Kepler momentum, the integral equals

C(B_n)=3(π²B_n²/(2v))^(1/3).

Cutting off both ends and linearly reparametrizing changes it by O(δ^(1/3)): both discarded integrands have absolute size O(s^(−2/3)), and the reparametrization factors differ from 1 by O(δ). Since δ=ε=L^(−12), equations (13) give

f_n(0,0) ≥ C(B_n)−O(1/L).                      (14)

Thus endpoints cost O(F/L), with substantial margin; no unquantified order of limits is being used.

## 5. Uniform transformed rows

Let elapsed macro-length be k, current height h, and retain only legal transitions with k+e≤n−1 and 1≤h+d≤RH. Let s=k/n, y=h/H, and transform the row by

w(e,q,d) exp{F[f_n(s,y)−f_n(s+e/n,y+d/H)]}.     (15)

Set a_n=F/n, b_n=F/H, so b_n²=a_n and a_nH=L. On

e≤H L^40, |d|≤sqrt(H)L^40,                     (16)

Taylor expansion using (9) gives, uniformly,

F[f_n(s,y)−f_n(s+e/n,y+d/H)]
 =−a_n(∂_s f_n)e−b_n p_n(s)d+o(1).            (17)

There is no d² term because f_n is affine in y. An explicit bound for the error is

C F L^28 [(H L^40/n)²
              +(H L^40/n)(L^40/sqrt H)]
 =n^(−1/3)L^O(1)=o(1).

Put λ=−a_n∂_s f_n and θ=−b_np_n. These tilts tend uniformly to zero. The remainder in (1), multiplied by q≤RH, is o(1), since all calibration derivatives grow only as fixed powers of log n. By (7),

q Ψ(λ,θ) ≤ (q/α)a_n V_n(y)+o(1)
 = (q/[2r]){log r+2loglog r−C_0}+o(1)
 = κ(r)q/r+o(1), r=h+εH.                      (18)

Here r≥εH→∞ uniformly. Section 2 therefore bounds the total contribution from (16) by some fixed m_bar<1, once C_0 is fixed sufficiently large and n is sufficiently large.

### Complement of (16)

The full transformed exponent is bounded by

C a_n L^16 e+C b_n L^16 |d|.                   (19)

To control e>H L^40, add a fixed sufficiently small positive length tilt λ_0 to this majorant, split the two signs of d, and use the fixed-q transfer bound in its fixed real neighborhood. The resulting row is at most

C exp[−λ_0 H L^40+O(H)]=o(1).

For |d|>sqrt(H)L^40, add a signed height tilt

θ_0=c L^40/sqrt(H),

with c>0 sufficiently small and fixed. Formula (1) bounds the majorant generating row by

C exp{C_R H[a_n L^16+(b_n L^16+θ_0)²]}.

The Chernoff factor is exp(−θ_0 sqrt(H)L^40)=exp(−cL^80). The displayed positive exponent is C_R c²L^80+O(L^(57)), since Ha_n=L and sqrt(H)b_n=sqrt(L). Choosing c<1/(2C_R) shows this tail is exp[−cL^80/2+O(L^57)]=o(1). The cubic/root-Taylor remainders are o(1), as H times any cubic power of these vanishing polylogarithmic tilts is n^(−1/3)L^O(1).

These estimates sum unrestricted destinations and lengths, so they cover every omitted transition. Choosing the margin in Section 2 before these o(1) errors proves one uniform row bound m_bar<1 for all elapsed lengths and heights.

## 6. Telescoping, terminal control and the final expansion

The positive Neumann/geometric expansion of the transformed prefix kernel has total weight at most 1/(1−m_bar). The telescope in (15) gives

a_n^[≤RH]ρ^n ≤ C exp[−F f_n(0,1/H)],           (20)

provided the terminal factor is uniformly bounded. This follows quantitatively from (9):

f_n(s,y)≤p_n(1)y+C L^16(1−s).

Writing r_0=n−1−k≥0, the terminal product is bounded by

ρ^r_0 t^(1−h)
 exp[b_np_n(1)h+C a_nL^16(r_0+1)].

Both b_np_n(1) and a_nL^16 tend to zero, so the fixed negative exponents logρ and −log t dominate, uniformly in r_0,h. There is no forced small endpoint height and no dropped terminal weight. Moreover,

F[f_n(0,1/H)−f_n(0,0)]=b_np_n(0)=o(1).

Choose R fixed with R²/(4D_0)>C_*+1. Equations (2), (14) and (20) show

D_n≥F C(B_n)−O(F/L).

Finally,

B_n=α/3+(7α/6)(l/L)+O(1/L),
C(B_n)=C_*[1+(7/3)l/L]+O(1/L),

because log H=(2/3)L+(1/3)l and
2loglog H=2l+2log(2/3)+O(l/L).

This is (T).

## Scope and dependency boundary

The argument proves a one-sided O(F/L) remainder after the 7/3 loglog correction. A matching coefficient-lower construction is a separate argument. It uses no stronger full local coefficient equivalent than the uniform fixed-q transfer already audited for the leading theorem. The tail amplitude and C_0 are deliberately not optimized, so this does not determine the coefficient of F/L, a polynomial prefactor of a_n, or an all-orders transseries.
