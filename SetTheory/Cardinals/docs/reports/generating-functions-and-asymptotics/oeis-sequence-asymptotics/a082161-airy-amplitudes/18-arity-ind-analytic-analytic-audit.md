# Independent analytic audit of the fixed-arity Airy amplitude proof

Date: 2026-10-02. Scope: every fixed integer k≥3, with constants permitted to depend on k. This review concerns the relaxed recurrence initialized by d_(0,0)=1, and no other combinatorial sequence.

## Verdict

**Approved for the stated leading positive amplitude and relative O_k(n^−1/6) error.** I found no fatal gap in compactness, the moving-boundary treatment, forward or weighted-adjoint residuals, phase normalization, singular compression, tracking, or the positivity deduction. The detailed estimates below fill out the compressed analytic passages in the reviewed proof. They do not require a new hypothesis or an unproved quantitative eigenvector-convergence rate.

The certified conclusion is

R_n = C_k (n!)^(k−1) [k^k/(k−1)^(k−1)]^n
      × exp{3[k(k−1)/2]^(1/3) a_1 n^(1/3)}
      × n^((2k−1)/3) [1+O_k(n^−1/6)],

where 0<C_k<∞. This is conditional only on the stated published recurrence/conversion and lower Theta estimate, whose match to the proof I independently checked in the primary paper. The positive constant is not evaluated by this argument.

No uniform-in-k result, all-orders expansion, compacted-tree amplitude, or DFA amplitude/ratio is certified. The rational test script is a useful algebra guard, not evidence for the analytic limiting assertions.

## Exact reviewed files

The hashes below were computed from the files actually read, before producing this audit.

- fixed-arity-proof.md: SHA-256 9be0c0aaf02b6918a8015c6d059664851d393e9ea8e75ac4a31e082c34434ee2
- algebra-audit.md: SHA-256 393f8477787f31c732a778b7ddfef1636656369640bd31889e03ddccdcd595ca
- check_exact.py: SHA-256 0ca2bdacc939ab1e43c628b7c839e54343c2aaa4d688870692141d7c825d19c1

Comparative ternary material actually read:

- amplitude-proof-candidate.md: SHA-256 18cdbc4ef9215673871f6196a18c5886ada435c0a995f6a808b44c82a28d783b
- independent-gap-audit/leading-amplitude-verdict.md: SHA-256 6aed66c2816f1576e3e410db54d224d835d78865b8d40447fe3b0990af42075e
- independent-gap-audit/singular-airy-audit.md: SHA-256 a474e355cafe9edbc1f7e5ebf767444f6f736d4525a1851c0d08f97036abcca9

The ternary verdict itself names an earlier candidate hash. I have not silently treated its approval as approval of a byte-identical current candidate. The fixed-arity proof was checked on its own, using the ternary audit only as comparative material.

I reran `python check_exact.py`: PASS, 2,095 exact rational phase-form and confined-column checks for q=2,…,10. Its finite range does not substitute for the symbolic general-q identities.

## 1. Fixed weights and exact positive form

Put q=k−1. The generating function factorization and the exclusion of exterior-root intrusions are correct. The renewal representation has nonnegative coefficients and a positive constant term, giving l_j>0; its double pole at 1 gives l_j=j+(q+2)/3+E_j. Exterior poles give exponentially decaying E_j and every fixed finite difference. Thus ω_j=l_j/(j+1) is bounded above and below by positive fixed-k constants. The stronger 1≤ω_j≤q estimate in the algebra audit is useful but not necessary.

The harmonic identities Th=kh and T*l=kl include every lower equation. The vector h is not square-summable, but no assertion that it is a Hilbert-space eigenvector is needed: these are pointwise row and column identities. The variance derivation applies to finitely supported vectors, so infinite invariant mass causes no interchange problem.

On phase r, write H_m=r+km+1 and g_m=u_m/H_m. Direct expansion verifies

Σ H_mH_(m+1)|g_(m+1)−g_m|²
= Σ|u_(m+1)−u_m|² + k|u_0|²/(r+1).

The terminal zero edge is essential. The algebra is valid over the complex numbers by taking real parts of cross terms.

For the physical confined map, α_i dominates every present up coefficient. The exact column loss remains valid at the top because every input t≤i−1 has its up output t+1≤i. Its bottom formula handles all q−1 negative-v locations rather than dropping them. The column loss is zero at t=0 and bounded below by c_k t/i for every physical t≥1. The positive decomposition (6) therefore holds without a negative boundary defect.

Define the positive shifted form

E_i^+(u) = [k²α_i²||u||²−||T_i u||²]/(2k²ε²).

Then E_i^+−E_i=(α_i²−1)||u||²/(2ε²)=O_k(ε)||u||². In particular the unshifted forms have a uniform lower bound tending to zero. A norm-bounded sequence with E_i bounded above also has E_i^+ bounded. This is the form used for every compactness and liminf estimate below.

## 2. Moving top, localization, and the actual Dirichlet boundary

A genuine danger would be applying the infinite critical identity to the physical variance sum without localization. The top output can have only one input, so the physical variance does not contain the terminal critical edge. The reviewed proof does not make that mistake.

The column term in E_i^+ gives

Σ εt ω_t|u_t|² ≤ C_k E_i^+(u),

and hence Σ_(εt≥R)ω_t|u_t|²≤C_k/R for bounded energy. This remains valid near the moving top, and it prevents mass escaping there.

Choose χ_R(x)=χ(x/R), equal to 1 up to R and 0 past 2R, with derivative O(1/R). For all sufficiently large i depending on fixed R, every edge meeting its support lies strictly below the physical top and U_i is bounded above and below by fixed positive constants. The positive variance then controls the critical radial energy of χ_Ru, since

H_mH_(m+1)|Δ(χ_R g)_m|²
≤2H_mH_(m+1)|χ_(m+1)Δg_m|²
 +2H_mH_(m+1)|g_m Δχ_m|².

The second sum is at most C_k ε²R^−2||u||²: Δχ=O(kε/R), and H_(m+1)/H_m≤k+1. This proves

Σ|Δ(χ_Ru)|² + k|χ_R(x_0)u_0|²/(r+1)
≤ C_k ε² [E_i^+(u)+R^−2||u||²].

The constants can be chosen independently of R≥1 once i is large enough for that R. Thus the later passage R→∞ does not lose global derivative control.

Let I_i u be the linear interpolation with nodal values u_m/√(kε), first node x_0=ε(r+1), and value zero at x=0. For a localized vector the exact identity gives

∫|(I_i u)'|²
= [1/(k²ε²)] [Σ|Δu|²+k|u_0|²/(r+1)].

Indeed the first segment contributes |u_0|²/[kε²(r+1)]. This is why the correct continuum trace is Dirichlet on every residue class; no residue-dependent Robin boundary survives.

The local H¹ bound and zero anchoring imply |I_i u(x)|²≤Cx and ∫_0^δ|I_i u|²≤Cδ². Summing the nodal bound gives the corresponding near-zero discrete mass O_k(δ²+εδ+ε²). Thus concentration on the first few sites is impossible, even though the column loss vanishes at t=0.

Rellich compactness on bounded intervals, this lower-tail bound, and the column-loss upper-tail bound yield strong global L² compactness after a subsequence. The weighted nodal and interpolation norms agree in the limit: off zero ω_j→1 uniformly; differences between nodal and linear interpolation norms vanish under the mesh H¹ estimate; lower and upper tails are uniformly negligible. The same is true of inner products. Using the localized derivative estimate above and then R→∞ shows that the limit is in H¹_0(0,∞), with a globally square-integrable derivative.

## 3. Liminf, recovery, eigenvalues, and ground profiles

On δ≤x≤R the coefficients converge uniformly. The positive column-loss term contributes (1/2)∫x|F|². The positive row-loss term contributes the other half. This second assertion uses local strong L² convergence and control of O(ε) translates by the local H¹ estimate; a formal pointwise coefficient expansion alone would not suffice. Those estimates have been established above.

For a profile F=xG, the variance coefficient is qω_(t+1)h_t h_(t+k)/(2k²ε²) in the limit. With u_t=√(kε)F(εh_t), the mesh kε Riemann sum gives exactly

(q/2)∫x²|G'|².

For arbitrary bounded-energy sequences the same local expression follows by weak lower semicontinuity on [δ,R]. Discarding the other nonnegative pieces and sending δ↓0 and R↑∞ gives the radial liminf plus potential.

The radial-to-ordinary energy identity is justified on the resulting domain, not merely on test functions. Hardy's inequality gives F/x∈L² for F∈H¹_0. Integration by parts, or approximation by compactly supported functions, yields

∫x²|(F/x)'|² = ∫|F'|².

The boundary term |F(x)|²/x vanishes at zero because it is bounded by ∫_0^x|F'|², and at infinity for H¹∩L² functions. Consequently the limiting closed form is

(q/2)∫|F'|²+∫x|F|²,

with domain H¹_0(0,∞)∩L²(x dx). Its potential makes its form embedding compact.

For recovery, sample F∈C_c^∞((0,∞)). Such samples have no lower or upper boundary error, and all coefficients converge uniformly on their support. This class is a form core: truncate at large x and near zero, then smooth. Polarization supplies simultaneous convergence on each fixed finite-dimensional recovery space.

The min–max argument is therefore complete. Recovery spaces bound each fixed discrete low eigenvalue from above. Take the corresponding finitely many discrete orthonormal eigenvectors; compactness preserves orthonormality in the limit, and liminf applies to every fixed linear combination, giving the matching lower bound. Thus

[k²−σ_(i,m)²]/(2k²ε²) → −a_m/B,
B=(2/q)^(1/3),

which is exactly (8). One is diagonalizing T_i†T_i, not T_i, and no nonnormal spectral theorem is used.

The leading right singular vector can be chosen nonnegative. T_i†T_i has positive adjacent off-diagonal entries along its input phase because the connecting up coefficient is strictly positive. Hence its top eigenvector is simple and positive. Compactness and the simple continuum ground eigenspace identify every subsequential limit, establishing convergence of the whole ground-profile sequence. All phase choices are covered; there are only k of them.

## 4. Forward residual, cutoff, and lower boundary

I independently checked the orders of the expansion. The critical first moment is zero; the second and third Taylor coefficients are qk/2 and qk(q−1)/6. The previous-time dilation contributes kxf'/3 at order ε³. Combining it with the variable up coefficient yields the coefficient 4kxf'/3 in (9). Dropping that dilation would change both p and β, so its inclusion matters.

The supplied p and β satisfy

(q/2)(pf)''−(x+λ)pf
=−(q+3)f/6−[(q+3)x+(q−1)λ]f'/3,

and cancel the uncorrected ε³ coefficient down to βf. The bottom forward row can be expanded using the value at x=0 because that input is exactly h_(−1)=0 and f(0)=g(0)=0. There is no extrapolated negative forward input.

Taylor remainders on the effective support have a polynomial Airy envelope W, with ∫W²<∞, allowing |f'| as well as |f|. A bound uniformly relative to f would fail at the first nodes; the reviewed statement uses the correct absolute-envelope bound. A fixed polynomial times a slightly shifted Airy envelope can be used to absorb all fixed-size shifts without introducing logarithmic losses.

All cutoff mismatch terms occur at x comparable to log i. Their norms are smaller than any inverse power of i because exp[−c(log i)^(3/2)] dominates every such power, even after mesh factors. The support O(i^(1/3)log i) is far below the moving physical top. For sufficiently large fixed starting I, 1+εp>0 throughout this support, and t_i>0.

The weighted squared mesh sum of W is O_k(ε^−1). Thus the unnormalized forward remainder is O_k(ε⁴ε^−1/2)=O_k(ε⁴N_i). Since s_i=t_iN_i/N_(i−1), normalization gives exactly (10). Small i cutoff conventions are irrelevant when tracking begins at fixed sufficiently large I.

## 5. Adjoint residual: finite bottom set and phase identification

The difference D=T†−T acts here on a common smooth sequence evaluated at all nonnegative sites. It need not be regarded as a difference of two maps between the same individual phase spaces: its role is a stencil comparison on that common sequence. The final adjoint estimate is between the correct physical input/output phases.

For t≥q, the stated moment estimates follow from the weight differences, including the exponentially decaying remainder. The cancellation Dh=0 is exact. Subtracting cεh, c=f'(0), before estimating the lower region is therefore valid and necessary. Taylor's theorem and f(0)=f''(0)=0, g(x)=O(x²) give

|R|≤Cε³(h³+h²), |R'|≤Cε³(h²+h),
|R''|≤Cε³(h+1), |R'''|≤Cε³.

Multiplying these by M_0=O(h^−3), M_1=O(h^−2), M_2=O(h^−2), and the bounded third-moment remainder gives |DR|≤C_kε³. At the finitely many exceptional t<q, Dh=0 and a direct finite sum give the same estimate with no negative adjoint input. There are O(ε^−1) low-region sites, so their norm contribution is O(ε³ε^−1/2). In the remaining region the ordinary Airy envelope gives that same scale. The far-top stencil terms vanish because the profile is already zero.

The variable adjoint term has leading part −kxε²F with O_k(ε³N_i) remainder, and the critical second derivative gives kλ ε²F. Time dilation and the omitted ε³ scalar correction are within O_k(ε³N_i). Together with the phase norm estimate below, this establishes (11).

A normalization subtlety is harmless but worth spelling out: the desired unnormalized adjoint comparison contains t_i(N_i²/N_(i−1)²)F_(i−1), not simply t_iF_(i−1). The squared norm ratio is 1+O(ε³), precisely within the admitted adjoint remainder.

## 6. Adjacent-phase norm precision

A mere norm asymptotic N_i²=C/ε+O(1) would be insufficient. The proof's three common coefficients are the correct remedy.

Let d=(q−1)/3 and H=(f+εg)². On a phase r, the ordinary mesh sum has endpoint terms governed by H(0), H'(0), etc. Since the first two vanish, phase dependence begins at absolute order ε². The algebraic part of ω contributes dε times the mesh sum of H/x. This quotient is smooth, vanishes at zero, and has first phase-dependent correction O(ε); multiplying by dε again gives O(ε²). Finally the exponential part is bounded by

Cε² Σ|E_j|(j+1)=O(ε²),

uniformly in phase. This follows from a global bound |f(εh)+εg(εh)|≤Cεh, available from the boundedness of f/x and g/x and the cutoff.

The phase-independent coefficients are

C_(−1)=(1/k)∫f²,
C_0=(2/k)∫fg+(d/k)∫f²/x,
C_1=(1/k)∫g²+(2d/k)∫fg/x.

All integrals converge. Since ε_(i−1)−ε_i=O(ε⁴), the common leading term changes by O(ε²), as do the uncontrolled phase remainders. Relative to a squared norm of order ε^−1 this is O(ε³), proving the required norm ratio. No coefficient at relative order ε³ needs to be independent of phase.

At residue zero, F_i(0)=cε+O(ε³), with c=B Ai'(a_1)>0. Therefore ψ_i(0) is positive and comparable to ε^(3/2)=i^−1/2.

## 7. Compressed singular gap

Let v_(i,1) be the normalized first right singular vector. After identifying the input mesh, ψ_(i−1) and v_(i,1) both converge to the same positive normalized Airy profile. The change from ε_(i−1) to ε_i is negligible, so

η_i=1−|〈ψ_(i−1),v_(i,1)〉|²=o(1).

For any x perpendicular to ψ_(i−1), |〈x,v_(i,1)〉|²≤η_i||x||². Consequently

||T_i x||² ≤ [σ_(i,2)²+(σ_(i,1)²−σ_(i,2)²)η_i]||x||².

This upper bound remains valid even though the other singular values are far below σ_2; replacing them by σ_2 only increases the expression. Since s_i=k[1+λε²+O(ε³)] and the singular gap has a strictly positive leading ε² coefficient, division by s_i gives 1−c_kε² on the complement. Orthogonal projection at the output can only decrease the norm.

Thus qualitative ground-state convergence suffices. No quantitative convergence rate, Temple bound, frozen eigenvector equation for ψ, or singular/eigenvalue identification is being assumed.

## 8. Tracking and endpoint rate

Write Z_i=||z_i|| and A_i=|a_i|. The forward residual gives the scalar diagonal error O(i^−4/3) and forcing O(i^−4/3). The adjoint residual gives the scalar off-diagonal coupling O(i^−1). With the compressed gap, choose K large enough that the negative contribution −Kc_k i^−1Z_(i−1) absorbs that coupling. Since i^−1/3 decreases,

A_i+K i^−1/3Z_i
≤(1+C_k i^−4/3)[A_(i−1)+K(i−1)^−1/3Z_(i−1)].

The multiplicative errors are summable, yielding bounded A_i and the indicated Lyapunov quantity. This does not immediately bound Z_i uniformly; instead substitute bounded A_i into its damped recurrence.

The product of dampings is bounded by exp[−c_k(i^(1/3)−m^(1/3))]. For m≥i/2, summing forcing m^−4/3 over its effective window of length O(i^(2/3)) gives O(i^−2/3). For m<i/2 the stretched-exponential suppression dominates every required power, and the fixed initial term obeys the same conclusion. Thus Z_i=O_k(i^−2/3).

Now |a_i−a_(i−1)|≤C_k(i^−4/3+i^−5/3), so a_i has a finite limit with tail O_k(i^−1/3). At residue zero, coordinate evaluation is bounded in the fixed weighted norm, hence

|z_i(0)|/ψ_i(0)≤C_k i^−2/3/i^−1/2=O_k(i^−1/6).

This is the actual rate bottleneck. The endpoint limit follows even before knowing that its value is nonzero.

## 9. Scalar product, exact conversion, and positivity

Expanding log t_i/k gives λi^−2/3+βi^−1+O_k(i^−4/3). The last sequence is summable with tail O(i^−1/3), and summation of the leading two terms gives

∏_(m=I+1)^i t_m = C_I k^i exp(3λi^(1/3))i^β[1+O_k(i^−1/3)].

The norm ratios telescope exactly. Their product times ψ_i(0) is F_i(0)/N_I, so the endpoint power is β−1/3=(7k−8)/6, not a power obtained by separately approximating every norm ratio. Setting i=kn gives stretched-exponential coefficient 3[kq/2]^(1/3)a_1. The exact factorial conversion shifts the polynomial exponent by 1−k/2, yielding (2k−1)/3. Stirling's relative O(1/n) error is smaller than the claimed rate.

I independently opened [Dastidar–Wallner, arXiv:2404.08415v1](https://arxiv.org/html/2404.08415v1). Equations (3)–(5) give the same initialized recurrence, up coefficient, and conversion R_n=(qn)!q^(−2qn)d_(kn,0). Theorem 1 gives a positive lower Theta bound with the same factorial, exponential, stretched-exponential, and polynomial normalization. Consequently the finite normalized limit proved here is strictly positive. Dividing the absolute normalized O_k(n^−1/6) error by that positive constant gives the relative error. The paper supplies the lower bound, not the stronger amplitude assertion being audited.

## Gaps and publication clarifications

No unresolved mathematical gap was found in the reviewed fixed-arity proof. The following clarifications are advisable when expanding it into a standalone paper:

1. State d_(0,0)=1 explicitly in the theorem setup, and begin quasimode tracking at sufficiently large fixed I.
2. Keep the localized-gradient proof before using the terminal-edge identity; never apply that identity to the unlocalized physical variance.
3. Include the row-loss strong-L² argument and the global H¹/Hardy explanation for the radial form identity.
4. Keep the absolute Airy-envelope interpretation of the forward residual, including a nonvanishing |f'| contribution at zero.
5. State the singular-vector overlap compression inequality, rather than asking the reader to infer an eigenvector estimate for the evolving quasimode.
6. Preserve the distinction between an absolute endpoint limit/rate and the subsequent use of the published lower bound to establish positivity and a relative rate.

These are exposition improvements supported by the estimates above, not additional unproved lemmas or restrictions on the theorem.
