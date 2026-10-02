# Independent audit: proportional-depth iterated Bell extension

Date: 2026-10-02. Mathematical review, not proof-assistant verification. No external publication or transmission was performed.

## Verdict

**PASS, conditional on the already audited diagonal foundation and its positive amplitude certificate.** The frozen research draft `reviewed-proportional-depth.md` establishes the proportional-depth expansion to every fixed order, uniformly on compact positive slope ranges and bounded shifts. No missing uniform estimate or circular positivity step was found. The new all-positive-parameter amplitude proof is valid. The result does not assert endpoint uniformity as the slope tends to zero or infinity, certified numerical amplitudes away from the seed, or a unique integer rounding rule.

The foundation used is `/workspace/shared/oeis-iterated-bell-report/iterated-bell.tex` together with its delivered audit. I independently checked the new argument rather than rerunning the foundation's interval certificate. Its seed I(1)>0 is sufficient; no new interval calculation is required.

## 1. Exact normalization and uniform absolute transfer

Write A(n,m)=(n−1)! 2^(−n) m^n m^(−n/(3m)). The inverse-iterate residue identity gives exactly H(n,m)/A(n,m)=m^(β/3) Res[(t_m/m)^n du], β=n/m. There is no missing n, 2, or factorial.

On the cut after compact entrance, j=m−τ≥m/2 gives

m^(β/3)|t_m/m|^n ≤ exp(βC−βτ) (m/(j+1))^(β/3) ≤ C_K exp(−bτ)

for b≤β≤B. When j<m/2, the upper bound |t_m|≤m/2+17 gives exponential suppression in m uniformly for β≥b. After cut crossing but before entrance, |t_m|<16 gives the same conclusion. Before crossing the cut jump is exactly zero. Thus the claimed normalized jump estimate holds with uniform positive constants.

A useful precision: individual true upper/lower lip integrals need not be absolutely integrable near s=0 at finite m. One must combine them into their jump before bounding; pre-crossing cancellation is essential. The draft does so by using the imaginary part. The limiting coefficient functions on each lip are separately integrable.

On τ≤A log m, the previously proved compact entrance expansion has Ψ=O(log m), so finite Taylor remainders are uniform in β on compact positive intervals. On the complementary region the true jump is bounded by C exp(−c min(τ,m)), and each limiting coefficient by C exp(−bτ)(1+τ)^d. Choosing A to depend on the requested order and the compact interval suffices. The constants do not need to be uniform as b→0. Finite contour length then proves every finite absolute amplitude expansion before division by I.

## 2. Analyticity and positivity

For completeness, the complex-linear functional is

J[F]=(1/(2π)) ∫ from −π to π r exp(iθ) F(r exp(iθ)) dθ
     +(1/(2πi)) ∫ from 0 to r [F(−s+i0)−F(−s−i0)] ds,

where r=1/2 and upper/lower values of Ψ are the audited continuations. The orientation and plus sign of the cut term agree with the residue identity. For real β, conjugation reduces J[exp(βΨ)] exactly to the draft's real-part/imaginary-part functional. For complex β it is J, not the real-part formula, that must be used.

On every compact subset of Re β>0, let b=min Re β>0 and T=max |Im β|. Since |Im Ψ| is bounded and Re Ψ≤C−τ on both lips,

|exp(βΨ) Ψ^k| ≤ C_(K,k) exp(−bτ)(1+τ)^k.

The circle values are bounded. This proves local domination and holomorphy, hence real analyticity on (0,∞). Equivalently, the draft's real-variable Taylor proof works because |Ψ|≤τ+C and the exponential Taylor series has an integrable majorant on |β−β0|<β0/2.

Absolute transfer along n=floor(βm) proves I(β)≥0 by continuity. The seed I(1)>0 proves I is not identically zero. Real analyticity on the connected interval makes zeros isolated, with only finitely many in each compact interior interval.

The exact quadratic composition inequality and exact factorial cancellation are

H(n,m+1)≥(1/2) Σ binom(n,k) H(k,m)H(n−k,m),
binom(n,k) A(k,m) A(n−k,m)/A(n,m)=n/[k(n−k)].

For a≤k/n≤c with 0<a<c<1, both k/m and (n−k)/m remain in compact positive intervals. If each amplitude error is uniformly bounded by ε_m→0 and |I|≤M on these intervals, the product error is bounded by 2M ε_m+ε_m². The sum of the weights n/[k(n−k)] remains bounded. Therefore accumulated error tends to zero; one does not need an error as small as o(1/n).

The lattice sum becomes ∫_a^c I(βθ)I(β(1−θ))/[θ(1−θ)] dθ. On the left,

log(A(n,m+1)/A(n,m))
= n log(1+1/m)+(n/3)[log m/m−log(m+1)/(m+1)] → β.

The second summand is O(log m/m) when n/m stays bounded. Also n/(m+1)→β, so the amplitude on the left tends to I(β). Thus

e^β I(β)≥(1/2)∫_a^c I(βθ)I(β(1−θ))/[θ(1−θ)]dθ.

The integrand is nonnegative everywhere and positive except for finitely many θ on the chosen compact interval. The integral is strictly positive, proving I(β)>0 for every β>0. Compactness now licenses uniform division by I. This ordering avoids assuming the conclusion in the transfer or convolution.

## 3. Bounded shifts, coefficients, and Stirling factors

For m=λn+δ, β=1/λ, the Abel-time shift is represented asymptotically by Ψ→Ψ+δ in the inverse expansion based at q=λn. This is a formal inverse-coordinate identity with uniform finite analytic remainders; no fractional iterate of f is needed.

Stirling for (n−1)! is sqrt(2π) n^(n−1/2)e^(−n) times the usual positive logarithmic correction 1/(12n)+…. Combining factors gives

D(λ)=sqrt(2π) λ^(−β/3) I(β),
H(n,m)~D(λ)e^(βδ)(λ/(2e))^n n^(2n−1/2−β/3).

At λ=1 this is 2C times n^(2n−5/6)/(2e)^n, exactly the delivered diagonal convention.

The draft's coefficient generator uses n, not m, in its Stirling series, correctly yielding

R1(y;β)=1/12+β²(−y²/2−y/3−1/18).

Its contour moment formula therefore gives the stated first correction. The independent executable `check_coefficients.py` checks R1, degree bounds through order two, both coefficients' β=1 reductions, and bounded-shift Abel translation through order two using exact SymPy arithmetic. Those finite checks supplement, rather than replace, the analytic all-order argument. The general degree bound follows because the order-j term in the logarithm has degree at most j+1≤2j, and exponentiation preserves the total degree bound 2j.

## 4. Floors and inverses

For m=floor(λn), δ_n=−{λn}; e^(−{λn}/λ) is indispensable. Bounded-shift uniformity justifies substituting this nonsmooth sequence into every finite forward coefficient. It does not justify differentiating the phase.

The fixed-δ smooth model has leading function 2t log t+c t, c=log(λ/(2e)). Its inverse core

x=y/[2 W0(y sqrt(λ)/(2 sqrt(2e)))], y=log Y,

and derivative S=2 log x+1+log(λ/2) are correct. Residual cancellation yields exactly the displayed U0 and U1. Eventual derivative lower bounds hold uniformly on compact λ and bounded δ ranges, so the claimed all-finite-order smooth inverse errors follow.

The draft explicitly withholds a canonical fractional-depth interpolation and an unjustified integer ceiling rule. Floor-depth phase uncertainty is O(1/log n) in index and dominates high smooth corrections unless handled. Bracketing with bounded-shift models plus instantiated errors or checking exact neighboring counts is appropriate. Eventual strict increase of floor-depth H is correctly justified by monotonicity in both integer arguments. Effective numerical threshold certification still requires explicit final constants and validity ranges.

## Recommended editorial precision

Include the explicit complex-linear functional or retain the fully adequate real-analytic proof with its exponential Taylor majorant. Mention that finite-m lip cancellation precedes any integration bound. Neither point is a substantive gap in the reviewed draft as written.
