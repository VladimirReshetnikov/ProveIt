# Proportional-depth iterated Bell numbers

Research extension, 2 October 2026. No external publication. This file does not modify the audited theorem or certificate. It uses their fixed radius 1/2, Fatou-coordinate normalization, verified outer entry, and certified positive value at β=1. The extension below has a complete mathematical argument but has not itself undergone the original independent audit.

## Main finding

The proportional-depth equivalent holds for every positive slope, uniformly when the slope varies in a compact subset of (0,∞). There is a clean positivity argument that avoids interval certification at each slope: nonnegativity follows from the integer coefficients, analyticity makes possible zeros isolated, and the positive quadratic term in Bell composition excludes every such zero.

Let f(z)=exp(z)−1 and H(n,m)=n![z^n]f^∘m(z). Use exactly the audited Ψ and fixed-contour functional ℐ. For real β>0 set

I(β)=ℐ[exp(βΨ)].

Then I is real analytic and strictly positive on (0,∞). For m=λn+δ with integer m, λ in a fixed compact subset of (0,∞), and |δ| bounded,

H(n,m) ~ (n−1)! 2^(−n) (λn)^n (λn)^(−1/(3λ)) exp(δ/λ) I(1/λ).

Equivalently, with β=1/λ and α=1/2+β/3,

H(n,m) ~ D(λ) exp(βδ) (λ/(2e))^n n^(2n−α),
D(λ)=sqrt(2π) λ^(−β/3) I(β).

All equivalences are uniform for those compact slope and bounded shift ranges. In particular the proposed normalization and power are correct. At λ=1, D(1)=sqrt(2π)I(1)=2C, reproducing the audited convention C n^(2n−5/6)/(2^(n−1)e^n).

There are expansions to every fixed order in n^(−1), with degree-at-most-2j polynomials in log n at order j, uniformly in these parameter ranges. Constants can be constructed effectively by the audited finite-order Abel-defect method; this does not supply numerically instantiated final error bounds or a threshold certificate for a particular numerical target.

## 1. Uniform absolute transfer before positivity

The safest first statement does not divide by I. Put β=n/m and let β range in a compact interval [b,B] contained in (0,∞). Then

H(n,m) = (n−1)! 2^(−n) m^n m^(−β/3) [I(β)+O(m^(−1)(1+log m)^D)],

uniformly for positive integers n,m tending to infinity in this range. This is an absolute amplitude expansion, valid even if I were zero.

The residue identity is unchanged:

H(n,m)=(n−1)!2^(−n) Res[t_m(u)^n du].

For the compact entrance set K from the audit, let τ denote its possibly unbounded entrance delay on the cut. For j=m−τ≥m/2 the real comparison orbit gives

|t_m| ≤ m−τ−(log(j+1))/3+C.

Multiplying log(|t_m|/m) by n=βm and using log(1+v)≤v yields

m^(β/3)|t_m/m|^n ≤ exp(βC−βτ)(m/(j+1))^(β/3) ≤ C' exp(−bτ),

where constants are uniform for β∈[b,B]. If 0≤j<m/2, |t_m|≤m/2+17 gives an exponentially small bound uniform in the same range. If crossing has occurred but entrance has not, |t_m|<16; before crossing, the imaginary part is exactly zero. Thus the normalized imaginary cut integrand is bounded by C exp(−c min(τ,m)), with positive c uniform on [b,B].

Furthermore Re Ψ≤C_K−τ and Im Ψ is uniformly bounded. Every coefficient function exp(βΨ) times a fixed polynomial in Ψ is therefore bounded by C exp(−bτ)(1+τ)^d, uniformly in β. The audited endpoint bound Re Ψ≤3−1/s also gives direct integrability near s=0 for every b>0.

For any requested finite order, split at τ≤A log m. On this part, compact-orbit reversion and ordinary finite Taylor expansions are uniform, since |Ψ|=O(log m). On the complement, choose A sufficiently large that both the true integrand and the finitely many coefficient tails are below the desired order. Outer arcs have already certified uniform finite entry. The contour has finite length. This proves uniform integration of every finite expansion, with finite effective logarithmic remainder degree, exactly as in the audited diagonal argument. No new global continuation or arbitrary-radius assertion is used.

## 2. Real analyticity, nonnegativity, and strict positivity

### Analyticity

On the outer contour Ψ is bounded. On the cut its imaginary part is bounded and Re Ψ≤C−τ. Around any β0>0, all derivatives in real β are dominated by exp(−β0 τ/2)(1+τ)^d times a constant, and the Taylor series is dominated on a sufficiently small neighborhood. Hence I is real analytic on (0,∞).

One can also obtain a holomorphic extension to Re β>0, but must use the complex-linear full-circle and upper/lower-lip contour functional. The displayed real-part/imaginary-part form of ℐ is only the equivalent real-β expression and must not be used as though it were complex linear for complex β. Explicitly, with r=1/2, use

J[F]=(1/(2π))∫_(−π)^π r e^(iθ)F(r e^(iθ))dθ +(1/(2πi))∫_0^r [F(−s+i0)−F(−s−i0)]ds.

For real β this equals I(β) when F=exp(βΨ). At finite m one must combine the two lips before estimating: their pre-crossing cancellation is essential. The limiting exp(βΨ) lips themselves are separately integrable.

### Nonnegativity everywhere

For any β>0 choose m→∞ and n=floor(βm), eventually n≥1. The positive normalization and uniform absolute transfer give I(n/m)≥−o(1), since H(n,m)≥0. By continuity I(β)≥0.

The audited certificate proves I(1)>1.64. Thus I is not identically zero. By real analyticity its zeros in (0,∞) are isolated. At this stage, nonnegativity and isolated zeros do NOT by themselves prove strict positivity.

### Quadratic Bell composition eliminates the zeros

Because the iterates commute,

f^∘(m+1)(z)=exp(f^∘m(z))−1.

All coefficients are nonnegative. The quadratic term alone gives the exact inequality

H(n,m+1) ≥ (1/2) Σ_(k=1)^(n−1) binom(n,k) H(k,m) H(n−k,m).

Fix β>0 and integers n,m→∞ with n/m→β. Write

C(n,m)=(n−1)!2^(−n)m^n m^(−n/(3m)).

For any fixed 0<a<c<1 restrict the positive sum to a≤k/n≤c. The absolute transfer is uniform for k/m and (n−k)/m in compact positive ranges. The exact normalization identity is

binom(n,k) C(k,m) C(n−k,m) / C(n,m)= n/[k(n−k)].

Consequently the restricted sum divided by C(n,m) converges by an ordinary Riemann sum to

(1/2) ∫_a^c I(βθ) I(β(1−θ))/[θ(1−θ)] dθ.

Uniform o(1) errors remain o(1), since the sum of n/[k(n−k)] on this restricted range stays bounded. On the left,

C(n,m+1)/C(n,m) → exp(β),

because (1+1/m)^n→exp β and
−[n/(3(m+1))]log(m+1)+[n/(3m)]log m→0.

Therefore

exp(β) I(β) ≥ (1/2) ∫_a^c I(βθ) I(β(1−θ))/[θ(1−θ)] dθ.

The compact θ-interval meets only finitely many zeros of each factor, since their arguments stay strictly inside (0,∞). Everywhere else both factors are strictly positive. The integral is strictly positive. Therefore I(β)>0.

This works for EVERY β>0. It neither assumes positivity propagates from samples nor uses numerical evidence outside β=1. It also proves a nontrivial integral inequality for the amplitude. Sending a↓0 and c↑1 by monotone convergence is possible after the fact, giving the full integral inequality and finiteness, but is unnecessary for the proof.

By continuity and compactness, I has a strictly positive minimum on each compact positive β-range. This upgrades all absolute expansions to uniform relative expansions.

## 3. Coefficient generator and first correction

Use the audited orbit polynomials v_j(y), defined by

W(q,y)=q+y+Σ_(j≥1) v_j(y)q^(−j),
W(q+1,y−log(1+1/q)/3)=g(W(q,y)),
v_1(y)=−y/3−1/18.

They have degree at most j and are determined by the invertible polynomial operator −j−(1/3)d/dy. For the base q=λn, set β=1/λ and

y=Ψ+δ−(log n+log λ)/3.

The bounded shift δ enters exactly through Ψ→Ψ+δ. This follows from the Abel coordinate identity and finite reexpansion of W(m,Ψ−log m/3), with m=q+δ; it does not require defining fractional iterates of the original generating function.

Define polynomials R_j(y;β) by the finite formal generator, with z=1/n,

Σ_(j≥0) R_j(y;β) z^j
= exp( z^(−1) log[1+β y z+Σ_(j≥1) v_j(y)β^(j+1)z^(j+1)] −βy
       +Σ_(ℓ≥1) B_(2ℓ) z^(2ℓ−1)/[2ℓ(2ℓ−1)] ).

At every desired order the sums are truncated. The Bernoulli sum is the logarithmic Stirling expansion for (n−1)!. The degree bound is deg_y R_j≤2j. In particular

R_0=1,
R_1(y;β)=1/12+β²(−y²/2−y/3−1/18).

Thus

H(n,λn+δ)=D(λ)e^(βδ)(λ/(2e))^n n^(2n−α)
 × [1+Σ_(j=1)^M P_j(log n;λ,δ)/n^j+O(n^(−M−1)(1+log n)^D_M)],

where

P_j(L;λ,δ)=I(β)^(−1) ℐ[e^(βΨ) R_j(Ψ+δ−(L+log λ)/3;β)].

Coefficient dependence is analytic in λ>0 and polynomial in δ, and the expansion is uniform on compact λ and bounded δ ranges. The remainder exponent can be chosen uniformly on each such compact parameter range.

Write μ_j(β)=I^(j)(β)/I(β), with μ_0=1. These are signed contour moments, not moments of an asserted positive measure. Let A=δ−(L+log λ)/3. Then the fully explicit first correction is

P_1 = 1/12 − β²[(μ_2+2Aμ_1+A²)/2 +(μ_1+A)/3 +1/18].

At β=1, λ=1 this reduces exactly to the audited first correction, including 1/36 as its unshifted constant before moments.

For a fixed integer depth increment r, H(n,m+r)/H(n,m)→exp(r/λ), uniformly on the same ranges. The leading relative shift dependence is exp(βδ), not exp δ except at λ=1.

## 4. Floors and other bounded shifts

For m=floor(λn), δ_n=−{λn}. Therefore

H(n,floor(λn)) ~ D(λ) exp(−{λn}/λ) (λ/(2e))^n n^(2n−α).

The oscillating multiplier is indispensable. For integer λ it is identically 1. For noninteger rational λ it is periodic; for irrational λ it has the usual fractional-part oscillation. In particular, the unmodulated normalization generally has no single limiting amplitude. The full expansion remains valid by substituting δ_n in each coefficient polynomial; bounded-shift uniformity justifies this substitution without any smoothness of δ_n.

The equivalent statement for ceilings has δ_n=ceil(λn)−λn, including δ_n=0 at integral λn. More general bounded shifts work pointwise and uniformly, but an arbitrary shift sequence need not make H(n,m_n) monotone.

## 5. All-finite-order inverses and the discrete distinction

Fix λ>0 and a constant real δ, and select a smooth finite asymptotic model. This choice describes a model; it is not an assertion that H admits canonical noninteger depth interpolation. Let

c=log(λ/(2e)), α=1/2+1/(3λ), d=log D(λ)+δ/λ,
G_N(t)=2t log t+c t−α log t+d+Σ_(j=1)^N A_j(log t;λ,δ)t^(−j),

where A_j are obtained by formal logarithm of the forward series. G_N is eventually strictly increasing uniformly on compact λ and bounded δ ranges.

For target Y let y=log Y and

x=y/[2 W_0(y sqrt(λ)/(2 sqrt(2e)))],
L=log x, S=2L+1+log(λ/2).

Then 2x log x+c x=y. Seek

t=x+Σ_(j=0)^M x^(−j)U_j(L,S^(−1);λ,δ).

Cancel residual powers successively. The new U_j occurs only as S U_j at its first order. Therefore

U_0=(αL−d)/S,
U_1=[αU_0−U_0²−A_1(L;λ,δ)]/S.

The same recursion supplies all finite orders. Taylor remainders and G_N'≥S/2 give inverse error O(x^(−M−1)(1+log x)^E/S), taking N≥M. For the first correction alone one may use O(log²x/(xS)). All constants may be chosen uniformly on the compact parameter ranges under discussion.

For rational λ=p/q, each residue class of n modulo q has a fixed δ_n, so the fixed-δ smooth inverses apply separately on those arithmetic progressions, followed by lattice bracketing. For irrational λ there are no finitely many such branches.

For floor depth, do NOT silently hold δ_n constant during inversion. The sequence has a bounded sawtooth term −{λn}/λ in its logarithm. A smooth δ=0 model misses this O(1) term, corresponding to O(1/log n) index uncertainty, larger than higher smooth corrections. One can instead bracket with the δ=0 and δ=−1 models and their explicit forward errors, or check candidate neighboring exact counts. Any claimed unique rounding rule requires separation from integer boundaries or exact bracketing.

The floor-depth sequence is eventually strictly increasing. Depth monotonicity follows from the positive recurrence and S(n,n)=1. For fixed m≥2, H(n+1,m)>H(n,m) for n≥2: in the recurrence over j, S(n+1,j)≥S(n,j), and strict inequality at j=2 contributes positively since H(2,m−1)>0. Since floor(λ(n+1))≥floor(λn) and floor(λn)≥2 eventually, the desired strict increase follows. This provides a well-defined eventual discrete threshold, but does not resolve the fractional-part phase automatically.

## 6. Scope and remaining work

- The result covers each fixed λ>0 and uniformity on compact positive λ-ranges. It does not claim uniformity as λ→0 or λ→∞ with n.
- The strict-positivity proof is analytic and combinatorial, with only the audited I(1)>0 certificate as numerical input.
- Final numeric constants, numerical amplitude evaluations away from 1, and effective target-specific threshold enclosures have not been certified here.
- Formal coefficient generation is accompanied by the audited analytic finite-remainder mechanism; a finite symbolic check alone is not its proof.
- The literature check is separate in literature.md. A lack of located proportional-depth equivalents is bounded overlap evidence, not an unrestricted novelty claim.
