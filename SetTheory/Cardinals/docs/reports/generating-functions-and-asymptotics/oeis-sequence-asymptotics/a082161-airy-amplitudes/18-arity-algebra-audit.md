# Independent fixed-arity algebra audit

Date: 2026-10-02. Scope: fixed integer k≥3, q=k−1. This checks the exact harmonic weight, singular variance and telescoping, the confined column loss, the evolving first Airy correction, and the adjoint/norm algebra in `fixed-arity-proof.md`. All estimates have constants depending on fixed k. This is an algebra audit, not a replacement for the separate compactness and tracking review.

## Verdict

The audited algebra is correct. In particular, the stated correction

p(x)=−(q+3)x²/(6q)−(q−1)(a/B)x/(3q),  B=(2/q)^(1/3),

together with

t_i=k[1+(a/B)ε²+(7k−6)ε³/6],

is the correct correction for the evolving equation T_i F_(i−1)=t_i F_i+error. The dilation between ε_(i−1) and ε_i is essential for both coefficients.

Sections 3 and 6 have no algebraic error: the bottom column-loss formula is exact even at the extra negative-v sites, the adjoint moments have the stated orders, and the first three norm coefficients are independent of phase. The following stronger exact bound is available:

1≤ω_j≤q for all j≥0.

One qualification must be retained: the forward error is an absolute polynomial Airy-envelope error, not an error uniformly relative to f at the bottom. The envelope must allow |f′| and can be nonzero at x=0. The current norm-based argument has the correct form.

## 1. Harmonicity, roots, renewal positivity and derivative controls

Let h_j=j+1 for j≥0 and h_(−1)=0. Let T u(j)=q u(j−1)+u(j+q), with negative inputs zero. Directly,

Th=kh.

Define l_j by

L(z)=Σ_(j≥0)l_j z^j=(qk/2)/(q−kz+z^k),

and put l_j=0 at negative indices. Coefficient extraction gives

q l_(j+1)+l_(j−q)=k l_j,  l_0=k/2.

Thus T*l=kl, including every bottom equation.

### Exterior roots

The exact factorization is

q−kz+z^k=(1−z)[q−Σ_(m=1)^q z^m]=(1−z)²S(z),
S(z)=q+(q−1)z+⋯+z^(q−1).

If S(ζ)=0 and |ζ|≤1, then q=Σ_(m=1)^q ζ^m. The triangle inequality forces |ζ|=1, and equality with the positive real number q forces every ζ^m=1. In particular ζ=1, contradicting S(1)=qk/2>0. Thus every zero of S is strictly outside the unit disk.

All these exterior roots are simple, so no polynomial factors in j are actually necessary in the remainder. Indeed, a common root of D(z)=q−kz+z^k and D′(z)=k(z^q−1) must satisfy ζ^q=1 and D(ζ)=q(1−ζ)=0, hence ζ=1. The root at 1 is exactly double, since D″(1)=kq≠0.

### Exact renewal representation and sharp-enough uniform bounds

Let X_1,X_2,… be independent uniform random variables on {1,…,q}, put S_0=0 and S_n=X_1+⋯+X_n, and set

τ_j=min{n≥1:S_n>j}.

Then τ_j≤j+1 deterministically. The renewal expansion of L gives

l_j=(k/2)Σ_(n≥0)P(S_n≤j)=(k/2)E[τ_j].

For completeness, the bounded stopping identity here follows from a finite sum:

E[S_(τ_j)]=Σ_(n=1)^(j+1)E[X_n 1_{τ_j≥n}]
=(k/2)Σ_(n=1)^(j+1)P(τ_j≥n)=(k/2)E[τ_j].

The factorization in the middle is valid because {τ_j≥n} is determined by X_1,…,X_(n−1). Hence

l_j=E[S_(τ_j)].

The overshoot lies between j+1 and j+q, so

j+1≤l_j≤j+q,
1≤ω_j:=l_j/(j+1)≤(j+q)/(j+1)≤q.

The renewal coefficients of l_j−l_(j−1) are strictly positive. Therefore l_j is increasing, and the harmonic recurrence also yields

1<l_(j+1)/l_j≤k/q.

The upper equality holds for 0≤j≤q−1. These bounds justify all bounded-ratio uses in the confined-form estimates without a separate compactness argument over finitely many sites.

### Asymptotic coefficient and remainder

Since S(1)=qk/2 and S′(1)=qk(q−1)/6,

L(z)=(1−z)^−2+(q−1)[3(1−z)]^−1+analytic remainder,
l_j=j+(q+2)/3+E_j.

Writing the exterior roots as ζ, an explicit remainder is

E_j=−(q/2) Σ_(S(ζ)=0) ζ^(−j−1)/(ζ^q−1).

Consequently, for some 0<ρ_k<1 and every fixed m≥0,

|Δ^m E_j|≤C_(k,m)ρ_k^j,
ω_j=1+(q−1)/[3(j+1)]+E_j/(j+1),
|Δ^m(ω_j−1)|≤C_(k,m)(j+1)^(−m−1).

Any choice of a fixed-step finite difference has the same conclusion. No sign claim about E_j is needed.

## 2. Exact singular variance and phase telescoping

Set π_j=l_jh_j. The critical Doob kernel is

P(j,j−1)=qj/[k(j+1)],
P(j,j+q)=(j+k)/[k(j+1)].

It has row sum one, and π supplies the exact invariant mass identity from one phase to the next. If u has finite support on an input phase and g_j=u_j/h_j, conditional variance gives

k²||u||²_ω−||Tu||²_ω
=Σ_(j≥1, output phase)q ω_j h_(j−1)h_(j+q)|g_(j−1)−g_(j+q)|².

There is no contribution at j=0 because there is only one present input there. After putting t=j−1, the two inputs differ by k and the coefficient is qω_(t+1)h_t h_(t+k). This identity is valid for complex inputs using squared moduli.

For a phase r∈{0,…,k−1}, put H_m=r+km+1 and u_m=u(r+km). Direct expansion yields

Σ_(m≥0)H_mH_(m+1)|u_(m+1)/H_(m+1)−u_m/H_m|²
=Σ_(m≥0)|u_(m+1)−u_m|²+[k/(r+1)]|u_0|².

Every interior diagonal coefficient is two, because H_(m−1)+H_(m+1)=2H_m. The first diagonal coefficient exceeds the ordinary half-line gradient's coefficient by k/H_0. Finite support includes the final edge to zero.

Combining this identity with 1≤ω≤q gives the explicit two-sided bounds

q A_r(u)≤k²||u||²_ω−||Tu||²_ω≤q² A_r(u),
A_r(u)=Σ_(m≥0)|u_(m+1)−u_m|²+[k/(r+1)]|u_0|².

For the critical bulk increment distribution, the mean is zero and variance is q; equivalently the unnormalized second derivative coefficient is qk/2. For the actual Doob increment Y at height h=j+1,

E[Y]=q/h,
E[Y²]=q+q(q−1)/h,
Var(Y)=q+q(q−1)/h−q²/h².

The singular-variance identity above is the exact identity needed in the proof; there is no assertion that it controls all adjacent-site differences across different residue classes.

## 3. Confined column loss: exact formulas and all bottom sites

For i≥1, on physical output/input phases, set

U_i(j)=q²(i−j+k)/(qi+j)=q−v_i(j),
v_i(j)=qk(j−q)/(qi+j),
α_i=1+(q²−1)/(qi+1).

The coefficient U_i(j) decreases in j. Every present up edge has j≥1 and

U_i(j)≤U_i(1)=qα_i.

Also 1≤α_i≤q. Thus Q_i(j,t)=T_i(j,t)h_t/(kα_i h_j) is dominated entrywise by the critical Doob kernel, so its row sums r_i and invariant-mass column sums c_i are both at most one.

Every physical input t≤i−1 has the up output t+1, while the down output t−q is present exactly when nonnegative. Therefore

c_i(t)=[U_i(t+1)l_(t+1)+1_(t≥q)l_(t−q)]/[kα_i l_t],
1−c_i(t)=[α_i−1+v_i(t+1)l_(t+1)/(k l_t)]/α_i.

This includes the physical top exactly; no omitted up output occurs there.

For every 0≤t≤q−1, harmonicity gives l_(t+1)/l_t=k/q, and direct reduction gives

1−c_i(t)=k t(qi+q)/[α_i(qi+1)(qi+t+1)].

It is zero at t=0 and strictly positive at every other such physical site. The equality remains valid at t=q−1, where v_i(t+1)=0. Thus the extra negative-v sites for q>2 do not create a sign problem.

One can make the global lower bound explicit:

1−c_i(t)≥t/(2ki),  1≤t≤i−1.

A proof with harmless overlaps between ranges is as follows.

- For 1≤t≤q−1, use the exact bottom formula, α_i≤q and qi+t+1≤ki to get 1−c_i(t)≥t/(qi).
- For q−1≤t≤2(q−1), the nonnegative v term may be discarded. Since (α_i−1)/α_i=(q²−1)/(qi+q²)≥(q−1)/(qi), this is at least t/(2qi).
- For t≥2(q−1), v_i(t+1)≥qt/(2i), because t+1−q≥t/2 and qi+t+1≤ki. Use l_(t+1)/l_t≥1 and α_i≤q to obtain t/(2ki).

For a physical output row j, the exact row loss includes the top truncation:

1−r_i(j)=[α_i−1+v_i(j)j/(k(j+1))]/α_i
          +1_(j+q>i−1) (j+k)/[kα_i(j+1)].

The added term is the missing down-input mass. Away from that top truncation it vanishes. The absent j=0 up input is already handled by the factor j=0. This optional identity is not used in the main draft.

Finally, with p=Q_i(j,j−1), b=Q_i(j,j+q), r=p+b, the elementary identity

p|a|²+b|b_0|²−|pa+bb_0|²
=pb|a−b_0|²+(1−r)[p|a|²+b|b_0|²]

proves equation (6) in the draft after summation and addition of the column loss. All three resulting terms are nonnegative. This establishes the claimed algebra of the confined form.

## 4. Evolving Airy correction

Put ε=i^(−1/3), x=ε(j+1), λ=a/B, B=(2/q)^(1/3), and f(x)=Ai(a+Bx). Then

(q/2)f″−xf=λf,
f‴=(2/q)[f+(x+λ)f′].

The coefficient expansion is

U_i(j)=q−kxε²+k²ε³+(k/q)x²ε⁴+O_k(ε⁵ polynomial(x)).

Also ε_(i−1)=ε(1+ε³/3+O(ε⁶)). Writing F_i=f+εg for the uncut profile, the expansion through order ε³ is

T_iF_(i−1)
=kf+kεg+kε²[(q/2)f″−xf]
+kε³[(q/2)g″−xg+q(q−1)f‴/6+(4x/3)f′+kf]
+O_k(ε⁴W(x)).

The additional x f′/3 term comes from the preceding-time dilation. Set g=pf and t_i=k[1+λε²+με³]. Then the ε³ residual divided by k is

[(q/2)p″+(q−1)/3+k−μ]f
+[qp′+(q+3)x/3+(q−1)λ/3]f′.

Both coefficients vanish when

p′=−(q+3)x/(3q)−(q−1)λ/(3q),
p=−(q+3)x²/(6q)−(q−1)λx/(3q)+C,
μ=(7q+1)/6=(7k−6)/6.

The constant C is free at this order; the draft chooses C=0. Since a is an Airy zero, f(0)=g(0)=0, so the absent bottom forward input is respected exactly.

### Boundary error qualification

For C=0 and before the cutoff, the next residual has the form

T_iF_(i−1)−t_iF_i=kε⁴[A(x)f(x)+B_4(x)f′(x)]+O_k(ε⁵W_5(x)),

on bounded x intervals, where

A(x)=(q²−q+1)(x+λ)²/(6q)
     +[((3q+1)x)/3+(q−1)λ]p′(x)
     +(q+5)p(x)/6−λx/q,
B_4(x)=−(9q+2)/6−q p(x)p′(x).

In particular B_4(0)=−(9q+2)/6. At the actual bottom x=ε, the residual can be order ε⁴ while f(ε) is order ε. Therefore a uniform bound O(ε⁴f) would be false. An integrable polynomial envelope built from |f|+|f′| is valid, and its weighted mesh norm is O(ε^(−1/2)), just as N_i is. This gives the normalized O(ε⁴) residual claimed in the draft.

## 5. Weighted adjoint moments

For t≥q, put h=t+1, A=ω_(t+1)/ω_t and C=ω_(t−q)/ω_t. The weighted adjoint and difference are

T†F(t)=qA F(t+1)+C F(t−q),
D=T†−T.

Its zeroth, first and second Taylor moments are exactly

M_0=qA+C−k,
M_1=qA−qC,
M_2=qA+q²C−q−q².

They obey

M_0=O_k(h^(−3)), M_1=O_k(h^(−2)), M_2=O_k(h^(−2)),

and every fixed higher moment is bounded. These orders include the exponential remainder in ω.

For an explicit check, set d=(q−1)/3 and temporarily replace ω by 1+d/h. Then

A−1=−d/[(h+1)(h+d)],
C−1=dq/[(h−q)(h+d)],
M_0=dqk/[(h+d)(h+1)(h−q)],
M_1=−h M_0,
M_2=dqk[(q−1)h+q]/[(h+d)(h+1)(h−q)].

The actual expressions differ by exponentially decaying quantities. More importantly, for the actual full weight the cancellation

Dh=0, equivalently hM_0+M_1=0,

is exact, not asymptotic. It also holds at every exceptional bottom site when the absent adjoint inputs are omitted.

Let c=f′(0). Because f(0)=f″(0)=0 and g(x)=O(x²), the remainder R(h)=f(εh)+εg(εh)−cεh satisfies, for h≤ε^(−1)+O_k(1),

|R^(m)(h)|≤C_kε³[h^(3−m)+h^(2−m)] for m=0,1,2,
|R‴(h)|≤C_kε³.

Taylor expansion with the moments gives |DR|≤C_kε³. At the finitely many bottom sites the same bound follows directly from Dh=0 and the finite number of evaluations. For h≥ε^(−1), the moment estimates and Airy derivatives yield O_k(ε³W(εh)). Thus

||DF_i||_ω=O_k(ε³N_i).

The variable-coefficient adjoint term has the expansion

−v_i(t+1)[ω_(t+1)/ω_t]F_i(t+1)
=−kxε²F_i(t)+O_k(ε³W(x))

in weighted mesh norm, including the bottom by a direct finite-site estimate. The same norm scale covers the preceding-time dilation. Together with the norm ratio below, these justify the draft’s normalized adjoint residual O_k(ε³).

## 6. Adjacent-phase norm coefficients

Let r∈{0,…,k−1} be the phase, x_m=ε(r+km+1), and let d=(q−1)/3. With cutoff errors omitted because they decay faster than every power, write

N_(r,ε)²=Σ_(m≥0)[1+d/(r+km+1)+E_(r+km)/(r+km+1)] [f(x_m)+εg(x_m)]².

Then

N_(r,ε)²=C_(−1)ε^(−1)+C_0+C_1ε+O_k(ε²),

with the following explicit phase-independent coefficients:

C_(−1)=(1/k)∫_0^∞ f(x)² dx,
C_0=(2/k)∫_0^∞ f(x)g(x) dx+(d/k)∫_0^∞ f(x)²/x dx,
C_1=(1/k)∫_0^∞ g(x)² dx+(2d/k)∫_0^∞ f(x)g(x)/x dx.

All integrals converge at zero and infinity. To check phase dependence, set H=(f+εg)². Both H(0) and H′(0) vanish, so the first phase-dependent ordinary Euler–Maclaurin term is O(ε²). For the algebraic weight term, H/x vanishes at zero; its first phase-dependent mesh term is O(ε), and the prefactor dε makes its contribution O(ε²). Finally,

Σ_(j in phase) |E_j| |F_i(j)|²/(j+1)
≤C_kε² Σ_(j≥0)|E_j|(j+1)=O_k(ε²),

using an Airy envelope and exponential decay. Thus any phase dependence from E_j also starts at the allowed order.

Since ε_(i−1)−ε_i=O(ε_i⁴), adjacent squared norms differ by O(ε_i²), while their leading size is C_(−1)ε_i^(−1). Consequently

N_i/N_(i−1)=1+O_k(ε_i³),
N_i≍_kε_i^(−1/2).

At the residue-zero bottom,

F_i(0)=f′(0)ε_i[1+O_k(ε_i²)],
ψ_i(0)≍_kε_i^(3/2)=i^(−1/2).

These are precisely the accuracies required in section 6; no phase-independent ε³ coefficient for the norm ratio is being assumed.

## Final audit status

No repair is required in the audited algebra. The renewal overshoot argument strengthens the weight bound, and the explicit norm constants make the phase estimate transparent. Keep the absolute-envelope interpretation of the forward residual. Analytic compactness, min–max convergence, and the later tracking argument are outside this audit’s verdict.
