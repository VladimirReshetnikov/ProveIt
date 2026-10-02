# Ternary Airy amplitude: fixed-weight proof candidate

Date: 2 October 2026. Status: a complete proposed leading-amplitude argument, pending independent scrutiny of the two analytic lemmas below. Exact algebraic identities are independently checked. This is not an all-orders theorem, and it must not be advertised as one. It does not yet prove the DFA/relaxed ratio limit.

## 1. Exact transfer and fixed norm

Let J_i={j:0≤j≤i, j≡i (mod 3)}. The transformed relaxed array obeys

 d_i(j)=U_i(j)d_(i−1)(j−1)+d_(i−1)(j+2),
 U_i(j)=4(i−j+3)/(2i+j)=2−v_i(j),
 v_i(j)=6(j−2)/(2i+j).

Missing input coordinates are zero. Write this rectangular map as T_i:H_(i−1)→H_i. The critical infinite-phase map T has up weight 2 and down weight 1. Define

 h(j)=j+1,
 l(j)=j+4/3+(1/6)(−1/2)^j,
 ω(j)=l(j)/h(j),  π(j)=l(j)h(j).

Then 1≤ω(j)≤3/2. Direct substitution, including j=0,1, gives

 Th=3h,   T* l=3l,

where l(−1)=l(−2)=0. Thus T has norm ≤3 between the phase spaces with norm ||u||²_ω=Σω(j)|u(j)|². Its weighted adjoint also has the SAME edge-harmonic vector h. The exponentially alternating term in l is necessary; replacing l by j+4/3 breaks the two bottom equations.

For a finitely supported input on any phase, set g(j)=u(j)/h(j). Exact conditional variance gives

 9||u||²_ω−||Tu||²_ω
 =Σ_(j≥1, output phase) 2ω(j)j(j+3)|g(j−1)−g(j+2)|².       (1)

This identity includes the final edge to zero beyond the input support. In particular, it does not have the residue-dependent extrapolation lengths of the unweighted singular problem.

## 2. Positive decomposition for the confined form

Set α_i=1+3/(2i+1). On the finite physical phase spaces, introduce

 Q_i(j,k)=T_i(j,k)h(k)/(3α_i h(j)),
 r_i(j)=Σ_k Q_i(j,k),
 c_i(k)=π(k)^−1 Σ_j π(j)Q_i(j,k).

Both r_i≤1 and c_i≤1. Indeed U_i≤2α_i, so Q_i is entrywise dominated by the critical h-Doob kernel. Its π-column sums are also dominated by the critical ones. More explicitly, for an input coordinate k,

 1−c_i(k)=(α_i−1)/α_i+v_i(k+1)l(k+1)/(3α_i l(k)).         (2)

At k=0 the two terms cancel exactly, since l(1)/l(0)=3/2. For k≥1, both terms are nonnegative and

 1−c_i(k)≥c k/i                                                     (3)

with an absolute positive c, uniformly for physical k≤i−1 and all sufficiently large i. At a row with both inputs present, write p=Q_i(j,j−1), q=Q_i(j,j+2). Rows with a missing input use its probability as zero. The exact form decomposition is

 9α_i²||u||²_ω−||T_i u||²_ω
 =9α_i²{Σ_k π(k)(1−c_i(k))|g(k)|²
       +Σ_j π(j)pq|g(j−1)−g(j+2)|²
       +Σ_j π(j)(1−r_i(j))[p|g(j−1)|²+q|g(j+2)|²]}.       (4)

Every term is nonnegative. This follows by first summing Q_i|g|² with its column masses, then using the elementary two-point identity

 p|a|²+q|b|²−|pa+qb|²=pq|a−b|²+(1−p−q)(p|a|²+q|b|²).

Thus the only difference between (4) and the unshifted form 9||u||²−||T_i u||² is the scalar O(i^−1)||u||². It vanishes after Airy scaling.

## 3. Analytic lemma S: compact singular Airy limit

Claim S. For each fixed m, the m-th largest singular value of T_i in the fixed weighted phase norms satisfies

 σ_(i,m)=3[1+a_m i^−2/3+o(i^−2/3)],                        (5)

where a_1>a_2>… are the negative Airy zeros. In particular the first two singular values have a positive gap of order i^−2/3. The normalized leading right singular vector, under mesh-3ε interpolation, tends to the positive normalized Ai(a_1+x), where ε=i^−1/3.

Proof candidate. Consider the self-adjoint forms

 E_i(u)=[9||u||²_ω−||T_i u||²_ω]/(18ε²).

Their lower bound is −O(ε)||u||², by (4). On input phase r write x_k=ε(r+3k+1), and interpolate

 G_i(x_k)=u(r+3k)/[sqrt(3) ε^(3/2)(r+3k+1)],  F_i=xG_i.

Interpolate G_i linearly between mesh points and constantly between 0 and x_0. Compactly supported smooth test functions satisfy, by direct Riemann sums in (4),

 ||u||²_ω→∫x²|G|²dx=∫|F|²dx,
 E_i(u)→∫[x²|G′|²+x³|G|²]dx
        =∫[|F′|²+x|F|²]dx.                               (6)

Here the first and third terms in (4) each contribute (1/2)∫x|F|². To check constants, on a fixed compact subinterval of (0,∞), v_i(j)=3xε²+O(ε³), while both column and row losses are xε²+O(ε³). The variance term tends to ∫x²|G′|². In (1), for input height t, its coefficient is 2ω(t+1)(t+1)(t+4); after division by 18ε² it is precisely the Riemann approximation to this radial energy.

For completeness, the required compactness bounds are as follows. A bounded norm and bounded E_i imply, by (3),

 Σ_(εj≥R) ω(j)|u(j)|² ≤ C/R.                             (7)

On every fixed scaled interval 0<x<R, the variance coefficients in (4) are uniformly comparable to those in (1); therefore the piecewise-linear G_i have bounded local radial energy ∫_0^R x²|G_i′|². The interpolation constants are uniform even at the first interval: x_k≥ε and x_k(x_k+3ε) is uniformly comparable to the average of x² on [x_k,x_k+3ε]. A localized Hardy estimate gives

 ∫_0^δ x²|G_i|²dx ≤ C_R δ²[∫_0^R x²|G_i′|²dx+∫_(R/2)^R x²|G_i|²dx],  (8)

uniformly for 0<δ<R/2. One proof of (8) extends G_i from an interior point of [R/2,R] constantly or linearly to zero in [R,2R], then applies ∫G²≤4∫x²G′², the latter following by integration by parts and Cauchy–Schwarz. Endpoint interpolation changes norm estimates only by bounded factors, and these factors tend to one off zero. Equations (7),(8) and ordinary one-dimensional compactness on [δ,R] give strong compactness of F_i in L²(0,∞).

Using the positive decomposition (4), discard all terms outside [δ,R]. Weak lower semicontinuity on that interval gives the lower bound in (6). Then δ↓0 and R↑∞. The resulting radial form domain transforms exactly to H¹_0(0,∞) with ∫x|F|²<∞: for compactly supported approximants, ∫x²|(F/x)′|²=∫|F′|²; completion and the Hardy bound preserve the identity and the zero trace. Smooth functions compactly supported inside (0,∞) give the recovery sequences. Min–max upper bounds follow from finite-dimensional recovery spaces. For lower bounds, take orthonormal discrete eigenvectors with bounded form values; the compactness just proved preserves their orthonormality in the limit and supplies the corresponding min–max lower bound. The limiting operator is −d²/dx²+x with Dirichlet boundary, whose eigenvalues are −a_m. Therefore (9−σ_(i,m)²)/(18ε²)→−a_m, proving (5). Simplicity of the first limiting eigenvalue gives the stated ground-vector convergence.

An alternative exact compactness check avoids a radial Hardy theorem. On a phase r, put H_k=r+3k+1 and extend u by zero at infinity. Direct telescoping gives

 Σ_(k≥0) H_k H_(k+1)|u_(k+1)/H_(k+1)−u_k/H_k|²
 =Σ_(k≥0)|u_(k+1)−u_k|²+3|u_0|²/(r+1).                 (7a)

Thus a localized version of the variance bound controls both the ordinary mesh gradient and the left trace. To localize, multiply u by a cutoff equal to one on x≤R and zero on x≥2R; the added variance energy is O(ε²)||u||², since its stepwise change is O(ε) and adjacent H ratios are bounded. On the support of the cutoff, U_i is bounded below uniformly for large i. Equation (7a) therefore gives Σ|Δu|²+|u_0|²≤C_R ε². The piecewise-linear interpolation of u/sqrt(3ε), extended to zero at x=0, has bounded H¹ energy on [0,R], and its leftmost value tends to zero. This directly proves (8), compactness at zero, and the Dirichlet trace. The extension energy to zero is |u_0|²/[3ε²(r+1)], also uniformly bounded. These are estimates for self-adjoint singular forms, not an assertion that T_i itself is self-adjoint.

## 4. Analytic lemma R: an evolving quasimode

Write a=a_1, f(x)=Ai(a+x), and

 p(x)=−5x²/12−a x/6,    g(x)=p(x)f(x).

Choose a smooth cutoff χ_i equal to 1 for x≤log i and 0 for x≥2log i, with uniformly controlled scaled derivatives. Set

 F_i(j)=χ_i(ε(j+1))[f(ε(j+1))+εg(ε(j+1))],
 N_i=||F_i||_ω,    ψ_i=F_i/N_i,
 t_i=3[1+a i^−2/3+(5/2)i^−1],
 s_i=t_i N_i/N_(i−1).

For large i, F_i≥0 and ψ_i(0), when 0 is on the phase, is positive. Its support lies within the physical interval. The claim is

 ||T_i ψ_(i−1)/s_i−ψ_i||_ω=O(i^−4/3),                    (9)
 ||T_i† ψ_i/s_i−ψ_(i−1)||_ω=O(i^−1),                    (10)
 N_i≍i^(1/6),     N_i/N_(i−1)=1+O(i^−1),
 ψ_i(0)≍i^−1/2.                                         (11)

The profiles are evolving profiles, not frozen eigenvectors. The preceding time scale must be retained in (9):

 (i−1)^−1/3=ε(1+ε³/3+O(ε⁶)).

At fixed x=ε(j+1), direct Taylor expansion of T_iF_(i−1) yields

 3f+3εg+3ε²(f″−xf)
 +ε³[f‴+4xf′+9f+3(g″−xg)]+O(ε⁴),                      (12)

in a polynomially weighted Airy envelope. The 4xf′ contains 3xf′ from the shifted potential and xf′ from the time dilation. Using f″=(x+a)f, the ε³ term before g is 10f+(5x+a)f′. Since

 3[g″−(x+a)g]=−(5/2)f−(5x+a)f′,

(12) equals t_i(f+εg)+O(ε⁴). This proves (9) after summing squares and dividing by N_i. It holds at the bottom row as well: F_(i−1)(−1)=0 exactly. Cutoff errors are smaller than every power of i by the Airy decay exp(−c(log i)^(3/2)).

For (10), the exact weighted adjoint is

 (T_i†u)(t)=[U_i(t+1)ω(t+1)u(t+1)+ω(t−2)u(t−2)]/ω(t),

with negative indices zero. The leading ε² equation is again f″−xf=af. There is a useful exact commutator check. Let T_0* be the unweighted critical adjoint, and B=ω^−1 T_0*ω. For t≥2 put a_t=2[ω(t+1)−ω(t)]/ω(t). Since both B and T_0* send h to 3h at those sites,

 [(B−T_0*)F](t)=a_t h(t+1)[F(t+1)/h(t+1)−F(t−2)/h(t−2)].

Here |a_t h(t+1)|≤C[(t+1)^−1+2^−t]. Write F(t)/h(t)=εΦ_ε(ε(t+1)), with Φ_ε(x)=[f(x)+εg(x)]/x. On 0≤x≤1, |Φ_ε′(x)|≤C(x+ε), because f(0)=f″(0)=0. Hence this commutator is O(ε³) per site near the boundary; for x≥1 the Airy derivative bounds give O(ε³) times a square-integrable polynomial Airy envelope. The difference T_0*−T_0 is a third finite difference, also O(ε³). At the two exceptional bottom sites check directly: (BF)(0)=(3/2)F(1), (BF)(1)=2F(2), while (T_0F)(0)=F(2) and (T_0F)(1)=2F(0)+F(3). Their linear terms cancel and the quadratic f term vanishes, leaving O(ε³). Finally, the difference between the adjoint and forward inhomogeneous perturbations is

 v_i(t)F(t−1)−v_i(t+1)[ω(t+1)/ω(t)]F(t+1),

which has the same O(ε³) normalized norm by a first difference estimate; near fixed t it is even O(ε⁴). Replacing F_i by F_(i−1) costs O(ε³N_i) by the exact time dilation. Consequently the difference between the adjoint action and the forward evolving expression has weighted norm O(ε³N_i). A way to check the uniform boundary estimate is to use the exact cancellation T†h=Th=3h and subtract the linear term Ai′(a)εh before estimating the weight commutator. For t≤ε^−1, the remaining profile and its discrete derivatives of orders q≤3 are bounded by Cε³(t+1)^(3−q)+Cε³(t+1)^(2−q). The nonoscillating part of ω−1 is 1/[3(t+1)], whose first and second differences are O((t+1)^−2) and O((t+1)^−3); the remaining part decays geometrically. Their commutator is O(ε³) per site. For t≥ε^−1, the same estimate follows from Airy derivative bounds and the inverse-power weight differences. Squaring and summing over O(ε^−1) sites gives O(ε³N_i). The inhomogeneous up-weight and time-shift contributions have the same bound. This proves (10).

Finally, Riemann sums give N_i²=(3ε)^−1∫f²+O(1). To obtain the adjacent-time ratio in (11), use Euler–Maclaurin on each residue: the bulk integral and its first corrections are smooth in ε, while the residue-dependent lower-end terms first enter at relative order ε³ because f(0)=0. The geometric part of ω contributes at the same or smaller order. Thus adjacent phases change N_i by a factor 1+O(ε³). The endpoint estimate follows directly from f(ε)=Ai′(a)ε+O(ε³).

Audit point: the commutator paragraph must retain the exact linear cancellation. Bounding the two adjoint weight errors separately without that cancellation gives an incorrect larger boundary error.

## 5. Tracking theorem from S and R

This step is a finite-dimensional Hilbert-space argument; no reversibility or changing norm is used. Let

 A_i=T_i/s_i,
 y_i=A_i y_(i−1),
 y_i=a_i ψ_i+z_i,  z_i perpendicular to ψ_i in the fixed phase norm.

By (9),(10), the 2×2 block decomposition relative to ψ_(i−1),ψ_i has

 a_i=(1+O(i^−4/3))a_(i−1)+b_i z_(i−1),   ||b_i||=O(i^−1),
 z_i=v_i a_(i−1)+D_i z_(i−1),             ||v_i||=O(i^−4/3).       (13)

Claim S and the leading profile convergence imply

 ||D_i||≤1−c i^−2/3.                                     (14)

Indeed ψ_(i−1) has overlap tending to one with the leading right singular vector. On its orthogonal complement, the maximum squared singular Rayleigh quotient is at most σ_2²+(σ_1²−σ_2²)o(1). Since s_i=3[1+a_1 i^−2/3+O(i^−1)], (5) gives (14). No estimate of the top norm excess or Temple inequality is needed here.

Let A=|a| and Z=||z||. The Lyapunov quantity A_i+K i^−1/3 Z_i is bounded for sufficiently large fixed K: the negative Kc i^−1 Z term from (14) absorbs the O(i^−1)Z cross term, and the remaining multiplicative errors are summable O(i^−4/3). Iterating the second inequality in (13), with bounded A, gives

 Z_i=O(i^−2/3).

For example its convolution kernel is bounded by exp[−c′(i^(1/3)−m^(1/3))], and the source m^−4/3 has mass O(i^−2/3) in the effective i^(2/3)-length window. The first inequality in (13) now gives a convergent a_i with

 a_i=a_∞+O(i^−1/3).

At the endpoint of the residue-0 phase, the fixed weight is bounded and ψ_i(0)≍i^−1/2. Consequently

 z_i(0)/ψ_i(0)=O(i^−1/6)→0.                              (15)

This is why the first-order evolving correction is useful: an uncorrected O(i^−1) forward residual would give only Z_i=O(i^−1/3), inadequate for pointwise extraction by this argument.

Undo the scalar normalization. Since s_i=t_i N_i/N_(i−1), its norm factors telescope. Also

 Π_(m≤i)t_m = C 3^i exp(3a_1 i^(1/3)) i^(5/2)(1+O(i^−1/3)),
 F_i(0) = Ai′(a_1)i^−1/3(1+O(i^−2/3)).

Therefore the exact relaxed solution satisfies, provided Claims S and R stand,

 d_(3n)(0) ∼ C_d 27^n exp(3·3^(1/3)a_1 n^(1/3)) n^(13/6). (16)

The limiting constant is finite. Its positivity follows from the published lower Theta bound for this very solution together with (15); no unproved positivity of a nonnormal spectral projection is being assumed.

Using the exact transformation R_n=(2n)! d_(3n)(0)/16^n and Stirling,

 R_n ∼ C_R (n!)² (27/4)^n exp(3·3^(1/3)a_1 n^(1/3)) n^(5/3),

with C_R>0. The comparison theorem for ternary DFAs gives only Theta at this stage. To get a DFA amplitude one still needs convergence of finite-level perturbed endpoint ratios (or a direct perturbative evolution theorem); neither follows merely from the displayed relaxed amplitude.

## 6. Sources and exact checks

The primary paper is Dastidar–Wallner, *Asymptotics of relaxed k-ary trees*, arXiv:2404.08415v1 and AofA 2024, DOI 10.4230/LIPIcs.AofA.2024.15. Its Theorem 1 supplies the relaxed Theta bound; it does not state a positive limiting amplitude. Its transformed recurrence (3)–(5) fixes the normalizations used above. The present fixed-weight identities and the proposed limiting-amplitude argument are additional work, not claims attributed to that paper.

Primary URLs:
- https://arxiv.org/html/2404.08415v1
- https://doi.org/10.4230/LIPIcs.AofA.2024.15

The rational script exact_blocks.py verifies the physical three-step blocks against the original recurrence through n=12. The independent audit directory verifies the critical h,l profiles, all three residue blocks, and a quantitative critical singular-dissipation inequality. None of these finite computations verifies Claims S or R.
