# Independent audit: fixed-weight singular Airy limit

Status: the singular Airy lemma in `amplitude-proof-candidate.md`, sections 1–3 and its use for the compressed singular gap in section 5, is mathematically consistent. The required interpolation argument can be supplied below. This audit does not certify section 4's evolving-quasimode remainder estimates or the full amplitude theorem.

## Exact normalization and boundary checks

Let input phase r=(i−1) mod 3, and input sites k∈J_(i−1). Let Q_i be the h-conjugate of T_i/(3α_i), with π=h l and α_i=1+3/(2i+1). For every nonzero up edge its output j≥1, and U_i(j)≤U_i(1)=2α_i. Its down coefficient after division by α_i is ≤1. Thus Q_i is entrywise dominated by the infinite critical Doob kernel restricted to the physical spaces. Both row and π-column masses are ≤1.

The input column k has exactly its critical candidate output rows k+1 and k−2, except for the already-zero negative l values. The upper output k+1≤i is present. Consequently the candidate's column-defect formula (2) is exact even at the upper boundary, with no missing upper correction:

1−c_i(k)=(α_i−1)/α_i + [2(k−1)/(α_i(2i+k+1))] l(k+1)/l(k).

For k=0 this is zero. For k=1 it is (α_i−1)/α_i. For k≥2 it is bounded below by a positive absolute constant times k/i. The k=1 case has the same bound. This establishes scaled tail tightness away from zero; it does not itself exclude concentration at k=0.

The variance coefficient on the pair of input sites k,k+3, whose output is k+1, is exactly

π(k+1)pq = [U_i(k+1) ω(k+1)/(9α_i²)] h(k)h(k+3).

In the positive normalized form E_i^+=[9α_i²||u||²−||T_i u||²]/(18ε²), the coefficient is therefore U_i(k+1)ω(k+1)/(18ε²). On a fixed scaled compact interval it converges to 1/(9ε²), as required. The difference E_i^+−E_i=(α_i²−1)||u||²/(2ε²)=O(ε)||u||² is negligible, including in all bounded-energy compactness arguments.

A real boundary caveat: the physical top output row has no second input. The moving positive variance sum therefore does NOT include the critical edge from the top input to its zero extension. One must not apply the full critical radial identity directly to the unlocalized moving variance sum. Localizing at fixed scaled height before taking i→∞ removes this issue.

## Exact radial identity and a simpler interpolation

For a finitely supported sequence u on one infinite phase r,r+3,..., put g_k=u_k/h_k, with h_k=k+1. Then, including its terminal edge to zero,

Σ_(k≡r) h_k h_(k+3)|g_(k+3)−g_k|²
= Σ_(k≡r)|u_(k+3)−u_k|² + 3|u_r|²/(r+1).

This follows by expanding each summand and telescoping the difference. The factor 3 and denominator r+1 are essential.

Let x_k=ε(k+1) and interpolate F_i linearly with node value u_k/√(3ε), adding F_i(0)=0 and zero continuation after the last zero node. Then the exact identity above says

∫_0^∞ |F_i′|² dx
= [1/(9ε²)] Σ h_k h_(k+3)|g_(k+3)−g_k|².

The contribution of the first interval is |u_r|²/[3ε²(r+1)], exactly the trace term. This gives a direct endpoint convention that enforces Dirichlet trace without an implicit radial-domain argument. This F interpolation differs from the draft's x times the linear G interpolation, but their difference tends to zero in L² on each compact subset away from zero under the same energy estimates; either convention yields the same limiting form.

## Localization and compactness

Choose χ_R(x), equal to 1 on [0,R] and zero past 2R, with derivative O(1/R), and apply the exact identity to v_k=χ_R(x_k)u_k. For all sufficiently large i (depending on fixed R), every edge meeting supp χ_R lies well below the moving top. There U_i is bounded below by a fixed positive constant. Product differences and h_(k+3)/h_k≤4 give

Q(χ_R g) ≤ C Q(g; x≤2R+3ε) + C ε² R^−2 Σ |u_k|².

The positive variance part controls the first term divided by ε². Hence the zero-anchored linear interpolants have a uniform H¹ bound on [0,R]. This includes the lower endpoint and implies

∫_0^δ |F_i|² ≤ (δ²/2) ∫_0^δ |F_i′|²,

as well as a discrete near-zero nodal mass bound O(δ²+ε²). For example, zero anchoring gives |u_k|²=3ε|F_i(x_k)|²≤3ε x_k C, and summation over x_k≤δ yields the claimed estimate. Thus a mass concentrated on finitely many boundary coordinates is impossible at bounded scaled energy.

Ordinary compactness on [0,R], the column-deficit tail estimate C/R, and the near-zero bound yield global strong L² compactness. Weighted nodal norm, unweighted nodal norm and interpolation norm converge together: off zero ω→1 and interpolation errors tend to zero; the lower and upper tails are uniformly negligible. The same applies to inner products, so discrete orthonormality survives in the limit.

A diagonal argument in R makes the limit locally H¹ with zero trace. The localized bound is uniform in R up to O(R^−2)||u||², so its global derivative is square integrable. There is no nonzero Robin trace left by the phase-dependent first mesh point.

## Liminf, recovery, and min–max

On [δ,R] with 0<δ<R<∞ all coefficient expansions are uniform. The variance term has limit ∫x²|(F/x)′|²; each of the two nonnegative loss terms contributes one half of ∫x|F|². The latter assertion requires local strong L² (available above), not merely a formal pointwise expansion. Shifted input/output sampling has the same limit because the local interpolation H¹ bound controls its O(ε) translations.

Discarding nonnegative terms outside [δ,R] gives the liminf. Letting δ↓0,R↑∞ gives the radial form plus potential. Since F has zero trace and finite global H¹ energy, the standard Hardy inequality and integration by parts give

∫x²|(F/x)′|² = ∫|F′|².

The boundary term F²/x vanishes at zero by |F(x)|²/x≤∫_0^x|F′|²; at infinity it vanishes for H¹∩L² functions. Thus the limiting operator is precisely −d²/dx²+x on H¹_0 with finite potential energy.

Recovery sequences may use F∈C_c^∞((0,∞)), sampled as u_k=√(3ε)F(ε(k+1)). These stay strictly below the moving top, vanish near the bottom, and have the exact norm/form limits. Such functions form a core for the Dirichlet Airy form; no special boundary Airy recovery estimate is needed. Polarization gives finite-dimensional recovery spaces for min–max upper bounds.

For lower bounds choose the first m normalized discrete eigenvectors of (9I−T_i†T_i)/(18ε²). Recovery bounds ensure their energies are uniformly bounded. Take a common compact subsequence; the strong norm and inner-product limits preserve dimension m and orthonormality. Apply the liminf to each linear combination. This proves convergence of each fixed eigenvalue to −a_m, hence

σ_(i,m)=3[1+a_m i^−2/3+o(i^−2/3)].

Ground-vector convergence follows from simplicity and sign selection. Positivity can be selected because T_i†T_i has positive adjacent off-diagonal entries throughout its input phase; this is an irreducible nonnegative Jacobi matrix. If one works only with compactness, convergence is initially up to sign.

## Nonnormal and amplitude limitations

Only T_i†T_i is being diagonalized. The argument provides singular values and right singular vectors; it gives no frozen eigenvalue theorem for T_i or its three-step product, and no left/right spectral projection asymptotic.

The section-5 compression bound is nevertheless valid without a Temple estimate. If ψ has overlap |〈ψ,v_1〉|²=1−η_i with the top right singular vector, then on ψ⊥,

||T_i x||²≤[σ_2²+(σ_1²−σ_2²)η_i]||x||².

Here η_i=o(1) suffices, since the singular gap itself is of order ε². With s_i=3[1+a_1 ε²+O(ε³)], this yields ||D_i||≤1−cε². No quantitative convergence rate of v_1 is needed. This avoids substituting an evolving forward quasimode into a frozen-eigenvector or Temple argument.

The independent work still required before certifying the full amplitude proof is the two-sided evolving-quasimode remainder lemma, including phase-dependent normalization ratios and the exact lower-bound input used for positivity. Finite matrix computations cannot supply any of those missing analytic statements.
