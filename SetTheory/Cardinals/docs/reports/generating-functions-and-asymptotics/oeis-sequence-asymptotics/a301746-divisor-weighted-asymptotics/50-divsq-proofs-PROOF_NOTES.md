# A301746: exact-saddle expansions and explicit logarithmic inversion

Research proof notes, 1 October 2026. These results are deductions below, not claims of literature priority. See SOURCE_STATUS.md for independently checked prior art. Sections 2–3 were independently reviewed on 1 October 2026; no correction was required. A full article review remains advisable.

Let d(k) be the number of positive divisors of k, b_k=d(k)^2, and

F(q)=∏_{k≥1}(1+q^k)^{b_k}=Σ_{n≥0}a_nq^n,
f(t)=log F(e^{-t}), κ_r(t)=(-1)^r f^{(r)}(t), V=κ_2,
L=log(1/t), M=t^{-1}L^3.

We use M only for t sufficiently small that L>1. For real x>0 let t_x be the unique positive solution κ_1(t_x)=x. Set

A_0(x)=exp(f(t_x)+xt_x)/sqrt(2πV(t_x)).

## 1. Explicit Mellin polynomial, with derivative-controlled errors

The Euler factor identity

Σ_{j≥0}(j+1)^2z^j=(1+z)/(1-z)^3=(1-z^2)/(1-z)^4

proves Σ b_k k^{-s}=ζ(s)^4/ζ(2s), Re(s)>1. Mellin inversion of log(1+e^{-x}) gives

f(t)=(2πi)^{-1}∫_{c-i∞}^{c+i∞} Γ(s)(1-2^{-s})ζ(s+1)ζ(s)^4/ζ(2s) t^{-s} ds, c>1.

Define the analytic function near s=1

h(s)=Γ(s)(1-2^{-s})ζ(s+1)[(s-1)ζ(s)]^4/ζ(2s).

It has h(1)=1/2. Write B_j=(d^j/ds^j)log h(s)|_{s=1}, j=1,2,3, and abbreviate b=B_1, c=B_2, d=B_3. (The constant d in this paragraph is distinct from the divisor function d(k).) Then

P(L)=((L+b)^3+3c(L+b)+d)/12.

For every fixed 1/2<σ<1 and fixed integer r≥0,

κ_r(t)=t^{-r-1}P_r(L)+O_{σ,r}(t^{-σ-r}),
P_0=P,  P_r=∏_{j=1}^r(D+j)P,  D=d/dL.                         (1)

For r=0, κ_0 denotes f. In particular,

κ_r(t)~(r!/12)t^{-r-1}L^3.                                    (2)

Proof of the remainder: move the Mellin line to Re(s)=σ. In Re(s)>1/2 the reciprocal 1/ζ(2s) has an absolutely convergent Dirichlet series and is bounded on every such fixed vertical line. The remaining zeta factors have polynomial vertical growth, while Γ(s) decays exponentially. Only the fourth-order pole at s=1 is crossed. For derivatives use the integrand Γ(s+r) in place of Γ(s), before moving the line. This proves the derivative errors rather than differentiating an uncontrolled O-term. The same argument works in closed subsectors |arg t|≤π/2−δ.

With γ_j defined by ζ(1+u)=u^{-1}+Σ_{j≥0}(-1)^jγ_j u^j/j!, and Z_j=(d^j/ds^j)logζ(s)|_{s=2}, the constants are

b=3γ+log2−Z_1,
c=ζ(2)−2(log2)^2−3Z_2−8γ_1−4γ^2,
d=−2ζ(3)+6(log2)^3−7Z_3+12γ_2+24γγ_1+8γ^3.                 (3)

## 2. Arbitrary-order coefficient theorem in exact saddle data

For every fixed nonnegative integer R,

a_n=A_0(n){E_R(t_n)+O_R(M(t_n)^{-R-1})},                       (4)

where

E_R(t)=Σ (-1)^{s/2}(s−1)!! ∏_{r=3}^{2R+2} [1/j_r! · (κ_r/(r!V^{r/2}))^{j_r}].

The sum is over j_r≥0 such that Σ(r−2)j_r≤2R and s=Σrj_r is even. The empty term is 1. Thus

E_0=1,
E_1=1+κ_4/(8V^2)−5κ_3^2/(24V^3)
   =1−(9/4)t/L^3 · (1+O(1/L)).                              (5)

All data in (4) are exact convergent sums at the positive real saddle. The error is relative to A_0. This is an all-orders exact-saddle expansion; it is not an explicit exponentially complete transseries.

### 2.1 Analytic derivative estimates

The elementary bound b_k≤d_4(k) follows prime-power by prime-power from (j+1)^2≤binom(j+3,3). Consequently Σ_{k≤X}b_k≤X(1+log X)^3. Partial summation gives the requisite weighted exponential sum bounds.

For complex z with |z−t|≤t/2 and each fixed r≥1, the absolutely convergent logarithmic series gives

|f^{(r)}(z)|≤Σ_k b_k k^r Σ_{j≥1}j^{r−1}e^{-jkt/2}
           =O_r(t^{-r-1}L^3).                               (6)

For k≤1/t, bound the inner sum by O_r((kt)^{-r}); for k>1/t use O_r(e^{-kt/2}), then the summatory bound. The logarithm is analytic on Re(z)>0: each factor has its zeros on Re(z)=0, and the log series is locally normally convergent. In particular (6) is available for Taylor remainders in a fixed disk of radius proportional to t. Equations (1) and (6) imply

κ_r/V^{r/2}=O_r(M^{-(r−2)/2}), r≥3,  V≍t^{-2}M.             (7)

### 2.2 Minor arcs: a full consecutive block is enough

Let X_{k,j}, 1≤j≤b_k, be independent Bernoulli variables with p_k=1/(1+e^{kt}), and S_t=Σ_{k,j}kX_{k,j}. Then E S_t=κ_1, Var(S_t)=V and

|E e^{iθ S_t}|≤exp(−2Σ_k b_k p_k(1−p_k)sin^2(kθ/2)).

On the consecutive interval I_t={k:1/t≤k≤2/t}, the probabilities stay uniformly away from 0 and 1, and b_k≥1. For an interval I of W consecutive integers and |θ|≤π,

Σ_{k∈I}sin^2(kθ/2)≥cW min(1,W^2θ^2).                       (8)

To prove (8), first bound the left side below by (W−|Σ_{j=1}^W e^{ijθ}|)/2. For |θ|≤1/W, apply 1−cos u≥c u^2 to the pairwise identity W^2−|Σe^{ijθ}|^2=Σ_{i,j}(1−cos((i−j)θ)). For 1/W≤|θ|≤C/W retain pairs whose differences are in a fixed subinterval of [1,W/C]; their squared phase is bounded below after summation. For C/W≤|θ|≤π, use the geometric-sum bound |Σe^{ijθ}|≤π/|θ|≤W/2 after increasing C. This proof is independent of where I starts.

It follows that

|E e^{iθS_t}|≤exp(−c t^{-1}min(1,t^{-2}θ^2)).               (9)

Set U=M^{1/12} and θ_0=U/sqrt V. Since θ_0/t≈M^{-5/12}→0, (9) bounds all θ_0≤|θ|≤π by

exp(−c M^{1/6}/L^3).

This is smaller than every power of t (and M^{-1}), even after multiplication by sqrt V. No arithmetic exponential-sum estimate or unproved equidistribution of the b_k is needed. Although this bound uses only one slot at each active size and loses L^3 near zero, it remains more than sufficient.

### 2.3 Local expansion and explicit coefficients

At t=t_n, Fourier inversion gives

a_n=e^{f(t)+nt}(2π)^{-1}∫_{−π}^π E e^{iθ(S_t−n)}dθ.

Discard |θ|≥θ_0 using (9). With u=θsqrt V, (6) and (7) give

log E e^{iu(S_t−n)/sqrt V}
=−u^2/2+Σ_{r=3}^{2R+3}κ_r(iu)^r/(r!V^{r/2})
 +O_R(M^{-R-1}|u|^{2R+4}).

Expand the exponential by weighted degree, assigning weight r−2 to the rth normalized cumulant, through degree 2R+1. Taylor's integral remainder is bounded, after multiplication by the Gaussian, by O_R(M^{-R-1}) times a fixed polynomial in |u| times e^{-u^2/4}; here |u|≤M^{1/12}, and the nonlinear exponent is O(M^{-1/2}|u|^3)=o(1). Integrating gives the stated O_R(M^{-R-1}) remainder. Odd total degree has odd s and vanishes by symmetry. Gaussian integration of (iu)^s produces exactly the coefficient (-1)^{s/2}(s−1)!!. This proves (4).

### 2.4 Global monotonicity

The original slot multiplicities need not be monotone. Nevertheless the coefficients have a simple global monotonicity proof. Rewrite

F(q)=∏_{k≥1}(1−q^k)^{-w_k},  w_k=b_k−1_{2|k}b_{k/2}.

For k=2^a m with m odd, w_k=(2a+1)d(m)^2≥1. In particular w_1=1, so F(q)=(1−q)^{-1}G(q), where G has nonnegative coefficients and its coefficient of q^k is positive for every k≥2 (use one part of size k). Hence a_1=a_0=1 and a_{n+1}>a_n for every n≥1.

## 3. Positive-real inverse and integer thresholds

For each fixed R define the specified positive-real continuation

A_R(x)=A_0(x)E_R(t_x).

This is positive and eventually strictly increasing. Indeed dt_x/dx=−1/V and dκ_r(t_x)/dx=κ_{r+1}/V, whence

(d/dx)log A_0(x)=t_x−κ_3/(2V^2)=t_x(1+O(M^{-1})),
(d/dx)E_R(t_x)=O_R(t_x M^{-2}).                             (10)

Thus (log A_R)'~t_x. Let x_R(y) be its unique large inverse and N(y)=min{n≥0:a_n≥y}.


Equation (4), (10), and the mean value theorem show that, with t=t_{x_R(y)}, L=log(1/t),

ceil(x_R(y)−δ_R(y)) ≤ N(y) ≤ ceil(x_R(y)+δ_R(y)),
δ_R(y)=C_R M^{-R-1}/t = C_R t^R/L^{3R+3}.                   (11)

The constants can be chosen for all sufficiently large y. At an exceptionally near-integer x_R, these brackets deliberately do not select one integer. Already R=0 has a shrinking O(L^{-3}) localization before rounding; every further correction sharply refines it.

## 4. Explicit expansion to every fixed inverse-logarithmic order

Put Q=P+P' and T=2P+P'. (T is the entropy polynomial, not a time variable.) Let ℓ=ℓ_n be the unique sufficiently large real solution

n=e^{2ℓ}Q(ℓ).                                               (12)

Set \hat t=e^{-ℓ}. Using (1) for r=1,2 gives t_n−\hat t=O(\hat t^{2−σ}/ℓ^3). Taylor expansion at the model saddle then gives

log a_n=e^ℓ T(ℓ)+O_σ(e^{σℓ}+ℓ),  1/2<σ<1.                  (13)

For detail, f(t)−t^{-1}P(log(1/t))=O(t^{-σ}); the model entropy is stationary at \hat t, so its change is O(\hat t^{-3}ℓ^3(t_n−\hat t)^2)=O(\hat t^{1−2σ}/ℓ^3)=o(\hat t^{-σ}). The Gaussian logarithm is O(ℓ), and (4) supplies a still smaller correction. Thus the model error in (13) is below every fixed inverse power of ℓ relative to its main term.

Writing H=log n and r_H=−3log H+2b+log96, explicit reversion gives

log a_n = sqrt(n) H^{3/2}/(2sqrt6) ·
 [1 + 3r_H/(2H)
    + (3r_H^2/8−9r_H/2+6c−9/2)/H^2
    + O((log H)^3/H^3)].                                   (14)

In particular this proves the logarithmic conjecture visible in the OEIS entry.

Every fixed further order is generated as follows. Let z=ℓ+b. Define

q(z)=z^3+3z^2+3cz+3c+d,
r(z)=z^3+(3/2)z^2+3cz+(3/2)c+d.

Equation (12) is

2z+3log z+log(1+3/z+3c/z^2+(3c+d)/z^3)=H+2b+log12.

Insert z=H/2+(−3log H+2b+log96)/2+Σ_{j=1}^K u_j(log H)H^{-j}. Determine u_j successively by vanishing coefficients; each stage has nonzero leading derivative 2. Taylor's theorem and the implicit-function estimate then supply an error O((log H)^{K+1}/H^{K+1}) in z. Substituting into e^ℓT(ℓ)=sqrt(n)T(ℓ)/sqrt(Q(ℓ)) proves the corresponding rigorous fixed-depth expansion. The u_j and output coefficients are polynomials in log H with constants determined by b,c,d.

A Lambert-W core for this reversion is

z_*=(3/2)W((2/3)(12e^{2b}n)^{1/3}),

which exactly solves e^{2(z_*−b)}z_*^3/12=n. The full model saddle differs by z−z_*=−3/(2z_*)+O(z_*^{-2}); it can be expanded recursively to every fixed order in z_*^{-1}.

## 5. Explicit inverse logarithmic hierarchy

Let Y=log y and Z=log Y. The inverse model is best parameterized by

Y=e^ℓT(ℓ),  n=e^{2ℓ}Q(ℓ)=Y^2Q(ℓ)/T(ℓ)^2.                 (15)

Its expansion coincides to every fixed inverse-logarithmic order with every x_R(y) and with N(y). To justify this statement, use (13) and (10): the logarithmic height error O(e^{σℓ}+ℓ) creates index error O(e^{(1+σ)ℓ}+e^ℓℓ), while n≍e^{2ℓ}ℓ^3, so the relative error is below every fixed power of 1/ℓ. Rounding is smaller still.

With r_Z=−3log Z+b+log6,

N(y)=3Y^2/Z^3 ·
 [1−3r_Z/Z+(6r_Z^2+9r_Z+9/4−3c)/Z^2
  +O((log Z)^3/Z^3)].                                     (16)

This is a statement for the integer threshold at a coarse logarithmic scale. The separate continuous inverse and the sharp rounding brackets are (10)–(11).

To compute all further terms set z=ℓ+b and solve

z+3log z+log(1+3/(2z)+3c/z^2+((3/2)c+d)/z^3)=Z+b+log6.

Then n=3Y^2 q(z)/r(z)^2. One has

q(z)z^3/r(z)^2=1−(3c+9/4)/z^2+(27/4−d)/z^3+O(z^{-4}).

The same successive coefficient extraction, now with leading derivative 1, proves every fixed inverse-logarithmic order.

A convenient Lambert-W core is z_*=3W((6e^bY)^{1/3}/3), with z=z_*−3/(2z_*)+O(z_*^{-2}). An even cleaner centered form uses v=ℓ+b+1/2 and

T(ℓ)=[v^3+(3c−3/4)v+d+1/4]/6.

The core v_*=3W((6e^{b+1/2}Y)^{1/3}/3) then has v−v_*=O(v_*^{-2}).

## 6. One further explicit correction and symbolic checks

The coefficient of H^{-3} inside the square brackets in (14) is

F_3(r_H)=−r_H^3/16−3cr_H−18c+4d+63r_H/4+27.

Including it improves the bracket remainder to O((log H)^4/H^4). The coefficient of Z^{-3} inside the square brackets in (16) is

I_3(r_Z)=−10r_Z^3−(81/2)r_Z^2−(153/4)r_Z−81/8+15cr_Z+9c−d.

Including it improves that bracket remainder to O((log Z)^4/Z^4). These coefficients, the two preceding coefficients, and the corresponding saddle reversion coefficients are independently extracted by `verify_log_series.py`; its machine-readable output is `log_series_verification.json`.

## 7. What is and is not established

Established by the proof above: the OEIS leading logarithmic conjecture; explicit three-correction forward and inverse formulas; a constructive arbitrary fixed-depth logarithmic hierarchy; an arbitrary-order relative coefficient expansion using exact saddle cumulants; global coefficient monotonicity; and shrinking integer-threshold localization for each specified real saddle continuation.

Not established: a convergent all-orders series, an explicit complete exponentially improved transseries, or a literature-wide first theorem. Further Mellin continuation encounters possible poles at s=ρ/2 from zeros ρ of ζ, subject to cancellations and multiplicities. The exact-saddle theorem retains this arithmetic information implicitly; the cubic-pole model does not. Exponentiating a finite inverse-logarithmic expansion of log a_n does not give a multiplicative equivalent for a_n.
