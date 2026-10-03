# A022629: exact-saddle expansion to arbitrary algebraic order

Research proof submitted for independent review, 1 October 2026. This note gives an exact-saddle expansion; it does not claim an exponentially complete transseries or a literature-wide first result.

Let F(q)=∏_{k≥1}(1+kq^k)=Σa_nq^n and, for t>0, define

f(t)=log F(e^(−t)), p_k(t)=k e^(−kt)/(1+k e^(−kt)),
μ(t)=Σ k p_k(t)=−f'(t), κ_r(t)=(−1)^r f^(r)(t), V(t)=κ_2(t).

For every real x>0 there is a unique t=t_x with μ(t)=x: μ is continuous and strictly decreasing from infinity to zero, since μ'=−V<0. Let m=m(t)>e be the large solution t=log m/m, valid for sufficiently small t; put L=log m and w=m/L.

## Theorem

For every fixed nonnegative integer R, as n→∞,

a_n = exp(f(t_n)+n t_n)/sqrt(2π V(t_n)) · [E_R(t_n)+O_R(w^(−R−1))].

All cumulants and w are evaluated at t_n. The finite polynomial E_R is

E_R= Σ (-1)^(s/2)(s−1)!! ∏_{r=3}^{2R+2} {1/j_r! · [κ_r/(r! V^(r/2))]^(j_r)},

where j_r≥0, Σ(r−2)j_r≤2R, s=Σrj_r is even, and the empty term equals one. Thus

E_0=1,
E_1=1+κ_4/(8V²)−5κ_3²/(24V³).

This is a relative expansion of arbitrary order in w^(−1), using exactly defined saddle data rather than fitted coefficients. In particular a_n~exp(f(t_n)+nt_n)/sqrt(2πV(t_n)).

## 1. Size and analyticity estimates

Uniformly as t↓0,

μ(t)~m²/2, V(t)≍m³/L=m²w,
|κ_r(t)|≤C_r m^(r+1)/L=C_r m^r w  (each fixed r≥2).

To check these, use p_k(1−p_k)≤min(k e^(−tk), e^(tk)/k). On k≤m/2, the latter is at most sqrt(m)/k; on m/2≤k≤m, it is at most exp(−(L−2)(1−k/m)); on k≥m, the former is (k/m)exp(−L(k−m)/m). Multiplication by k^r and summation gives O_r(m^r w). The small-k bound contributes O_r(m^(r+1/2)) for r≥1 and O(sqrt(m)log m) for r=0, which are smaller. Every Bernoulli cumulant of order r≥2 is p(1−p) times a fixed polynomial in p, so the same estimates apply. A consecutive interval I of length comparable to w, centered at m, has p_k bounded away from both zero and one; this gives V≳m²w. The same boundary bounds, with p_k−1_{k≤m}, show μ=m²/2+O(m²/L), hence the stated equivalence.

For some fixed c>0 the centered logarithmic characteristic function is analytic for complex θ with |θ|<c/m, and its derivatives of every fixed order r≥2 are O_r(m^r w), uniformly on a smaller disk. Indeed for k≤2m, |exp(ikθ)−1|<1/2 if c is sufficiently small, so the Bernoulli logarithm has no zero there and its derivatives are bounded by a constant times k^r p_k(1−p_k). For k>2m, k exp(−(t−c/m)k)=O(1/m) and the absolutely convergent logarithm series gives the same bound after summation. This avoids any assertion that log F is analytic on the full unit disk.

## 2. A minor-arc estimate including the near-resonances

The modulus of the characteristic function of S_t=ΣkX_k, for independent Bernoulli variables X_k with parameters p_k, satisfies

|E exp(iθS_t)|≤exp(−c Σ_{k∈I}sin²(kθ/2)).

For every consecutive interval I of W integers and |θ|≤π,

Σ_{k∈I}sin²(kθ/2) ≥ c W min(1,W²θ²).

Here c is absolute for W sufficiently large. A short proof: the left side is at least [W−|Σ_{j=1}^W exp(ijθ)|]/2. For |θ|≤1/W, write W²−|Σexp(ijθ)|²=Σ_{i,j}(1−cos((i−j)θ)) and use 1−cos u≥c u². For 1/W≤|θ|≤C/W, the normalized geometric sum is bounded below one by a fixed amount, uniformly in that compact scaled range; this follows equally from the same pairwise identity by retaining pairs with |i−j| between fixed fractions of W/C. For C/W≤|θ|≤π, the geometric bound |Σexp(ijθ)|≤1/|sin(θ/2)|≤π/|θ|≤W/2 holds on choosing C≥2π.

Additionally, for |θ|≤c_0/m, all k∈I satisfy |kθ|≤1, and hence Σ sin²(kθ/2)≥c m²w θ². It follows that:

- for w^(1/12)/sqrt(V)≤|θ|≤c_0/m, the modulus is at most exp(−c w^(1/6));
- for c_0/m≤|θ|≤π, it is at most exp(−c m/L³).

Both bounds decay faster than any inverse power of m. In particular the possible resonances θ≈2πj/m do not create competing saddle contributions at any algebraic order.

## 3. Fourier inversion and arbitrary-order expansion

At t=t_n the random variable S_t has mean n and

a_n=exp(f(t)+nt) P(S_t=n).

Fourier inversion expresses the probability as (2π)^(−1)∫_{−π}^π E exp(iθ(S_t−n))dθ. Section 2 discards the region outside |θ|≤w^(1/12)/sqrt V with an error smaller than every power of m, even after multiplication by sqrt V.

Inside this interval set u=θsqrt V. The analytic estimate of Section 1 gives

log E exp(iu(S_t−n)/sqrt V)
=−u²/2+Σ_{r=3}^{2R+3} κ_r(iu)^r/(r!V^(r/2))
 +O_R(w^(−R−1)|u|^(2R+4)).

The coefficient of the rth term is O_r(w^(−(r−2)/2)). Expand its exponential and retain all monomials of weighted degree Σ(r−2)j_r≤2R+1. The integral of the discarded remainder is O_R(w^(−R−1)): Taylor's integral remainder is bounded by that power times a fixed polynomial in |u| times exp(−u²/4). This domination follows from |u|≤w^(1/12), since the nonlinear exponent is O(w^(−1/2)|u|³)=o(1), and the analyticity estimates control the fixed higher terms. Enlarging the Gaussian integrals to the real line incurs only an exponentially small error.

Odd weighted degree has odd s and integrates to zero. For even s, the Gaussian integral of (iu)^s is (−1)^(s/2)(s−1)!!sqrt(2π), which gives exactly E_R and the theorem. The omitted cumulant of order 2R+3, if it appears alone at weighted degree 2R+1, is odd and therefore need not be written in E_R.

## 4. Positive-real and integer inverse localization

Define, for sufficiently large real x,

A_R(x)=exp(f(t_x)+xt_x)/sqrt(2πV(t_x)) · E_R(t_x).

This is a positive smooth function, eventually strictly increasing. Indeed E_R=1+O(1/w), its derivative with respect to x is O(1/(mw²)), and

d/dx log A_0(x)=t_x−κ_3/(2V²)=t_x+O(1/(mw)).

The stated derivative bound for E_R follows by differentiating each finite cumulant monomial, using dκ_r/dx=κ_(r+1)/V, the estimates of Section 1, and dt_x/dx=−1/V. Thus (log A_R)'~t_x~1/w.

Consequently A_R has a unique large positive-real inverse x_R(y). For the integer inverse N(y)=min{n:a_n≥y}, the coefficient theorem and strict monotonicity of a_n imply

N(y)=ceil(x_R(y)+ε_R(y)), with ε_R(y)=O_R(w^(−R)),

where w is evaluated at x_R(y). More explicitly, the crossing lies between the integer roundings of x_R(y)±C_R w^(−R). This follows because log a_n−log A_R(n)=O(w^(−R−1)), while (log A_R)'~1/w. The ceiling statement only expresses these shrinking threshold brackets; it does not claim that an integer can be selected unambiguously when x_R(y) is exceptionally close to an integer. Already R=0 gives N(y)=x_0(y)+O(1).

Strict monotonicity of a_n for n≥1 is proved by increasing the largest part and retaining its color; the new single part of size n+1 with color n+1 lies outside the image.

## Verification status and limitations

The proof is self-contained apart from elementary Fourier inversion and Gaussian integration. Exact and numerical checks are corroboration, not dependencies. Independent review is requested, particularly of the uniform remainder and inverse localization. No complete exponentially small transseries, convergence of the formal series, or full literature priority claim is asserted.
