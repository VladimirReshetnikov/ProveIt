# A leading Airy amplitude for each fixed arity

Date: 2026-10-02. Status: proof extension, submitted for independent review. All constants may depend on the fixed integer k≥3. Nothing here is uniform as k tends to infinity. This addresses relaxed trees only, not DFA ratios, compacted trees, or all-orders expansions.

## Statement

Put q=k−1 and let a_1 be the largest negative Airy zero. For the exact relaxed recurrence in Dastidar–Wallner, there is C_k>0 such that

R_n ~ C_k (n!)^q (k^k/q^q)^n exp[3(kq/2)^(1/3)a_1 n^(1/3)] n^((2k−1)/3).

The proof below also gives relative error O_k(n^(−1/6)). It extends the independently approved ternary fixed-weight proof by proving the additional general-k algebra and verifying every place where the ternary argument used a special coefficient. Positivity uses the published lower Theta bound for this exact relaxed sequence.

## 1. Exact fixed harmonic weight

The phase at time i is J_i={0≤j≤i:j≡i mod k}. Missing entries are zero. The exact transfer is

(T_i u)(j)=U_i(j)u(j−1)+u(j+q),
U_i(j)=q²(i−j+k)/(qi+j)=q−v_i(j),
v_i(j)=qk(j−q)/(qi+j).

On infinite nonnegative phase spaces let T have coefficients q,1, and h_j=j+1. The forward boundary input h_(−1) is zero. Define l_j by

L(z)=Σ_(j≥0) l_j z^j=(qk/2)/(q−kz+z^k),

and l_j=0 for negative j. Coefficient extraction gives

q l_(j+1)+l_(j−q)=k l_j (j≥0), l_0=k/2.

Thus Th=kh and T* l=kl exactly, including all bottom equations. Put ω_j=l_j/h_j and π_j=l_j h_j. The weighted adjoint T† has T†h=kh too.

### Positivity and asymptotics

The denominator factors as

q−kz+z^k=(1−z)[q−Σ_(m=1)^q z^m]=(1−z)² S(z),
S(z)=Σ_(r=0)^(q−1)(q−r)z^r.

The renewal representation

L(z)=(k/2)(1−z)^−1 [1−q^−1Σ_(m=1)^q z^m]^−1

has positive coefficients, so l_j≥k/2. There are no zeros of q−Σz^m in |z|<1 by the strict triangle inequality. Equality on |z|=1 requires every z^m=1, hence z=1. This root is simple because the derivative there is −qk/2. Consequently S has all zeros strictly outside the closed unit disk.

Since S(1)=qk/2 and S′(1)=qk(q−1)/6, expansion at z=1 gives

L(z)=(1−z)^−2+(q−1)/[3(1−z)]+analytic remainder,
l_j=j+(q+2)/3+E_j,
|Δ^m E_j|≤C_(k,m) ρ_k^j, 0<ρ_k<1,

for each fixed finite derivative order m. Multiple exterior poles, if present, merely contribute polynomial times exponential terms absorbed into a slightly larger ρ_k<1. Therefore

ω_j=1+(q−1)/[3(j+1)]+E_j/(j+1),
0<c_k≤ω_j≤C_k,
|Δ^m(ω_j−1)|≤C_(k,m)(j+1)^(−m−1) (m≥0).

Positivity on every site and convergence to 1 prove the positive lower bound; no sign assertion about E_j is needed.

## 2. Exact critical variance and gradient/trace identity

For input u of finite support on one phase, write g_j=u_j/h_j. The h-Doob kernel P(j,t)=T(j,t)h_t/(k h_j) has row sum one and invariant phase masses π. Conditional variance gives

k²||u||²_ω−||Tu||²_ω
=Σ_(j≥1, output phase) q ω_j h_(j−1)h_(j+q)|g_(j−1)−g_(j+q)|².                 (1)

Equivalently the coefficient in the normalized defect ||u||²−||Tu/k||² is (q/k²)ω_(t+1)h_t h_(t+k), indexed by input t=j−1. This includes the final edge to zero beyond the support.

For a phase r∈{0,…,k−1}, set H_m=r+km+1 and u_m=u(r+km). Direct expansion and telescoping give

Σ_(m≥0) H_m H_(m+1)|u_(m+1)/H_(m+1)−u_m/H_m|²
=Σ_(m≥0)|u_(m+1)−u_m|²+k|u_0|²/(r+1).                 (2)

The coefficient of |u_m|² cancels for m≥1 because H_(m−1)+H_(m+1)=2H_m; at m=0 the uncancelled increment is k/H_0. This proves (2) for complex inputs as well as real ones. Equations (1),(2) give two-sided critical dissipation bounds by the ordinary mesh-gradient and bottom trace, with positive constants depending only on k.

## 3. Positive confined form, including all extra bottom sites

Let α_i=1+(q²−1)/(qi+1). At every present up edge j≥1, U_i(j)≤q α_i, with equality at j=1. The absent j=0 up edge plays no role. Put

Q_i(j,t)=T_i(j,t)h_t/(k α_i h_j),
r_i(j)=Σ_t Q_i(j,t),
c_i(t)=π_t^−1 Σ_j π_j Q_i(j,t).

Entrywise domination by the critical Doob kernel proves 0≤r_i,c_i≤1. Every physical input t has its up output t+1, and its down output t−q if nonnegative, so the exact column loss is

1−c_i(t)=[α_i−1+v_i(t+1)l_(t+1)/(k l_t)]/α_i.          (3)

The extra negative-v bottom sites for q>2 cannot be discarded. For 0≤t≤q−1, the left recurrence gives l_(t+1)/l_t=k/q. Consequently

1−c_i(t)=k t(qi+q)/[α_i(qi+1)(qi+t+1)].                (4)

It vanishes exactly at t=0 and is ≥c_k t/i for 1≤t≤q−1. For t≥q−1, v_i(t+1)≥0; the scalar α_i−1 controls the finitely many heights up to 2(q−1), while for t≥2(q−1), v_i(t+1)≥c_k t/i on the physical range t≤i−1. The positive bounded l-ratio then proves

1−c_i(t)≥c_k t/i for all physical t≥1.                 (5)

At a row with present probabilities p=Q_i(j,j−1), b=Q_i(j,j+q), missing entries having probability zero, exact elementary algebra yields

k²α_i²||u||²−||T_i u||²
=k²α_i²{Σ_t π_t(1−c_i(t))|g_t|²
 +Σ_j π_j p b |g_(j−1)−g_(j+q)|²
 +Σ_j π_j(1−r_i(j))[p|g_(j−1)|²+b|g_(j+q)|²]}.         (6)

All terms are nonnegative. Relative to the unshifted defect, the additional scalar is O_k(i^−1)||u||².

## 4. Singular Airy limit and compactness

Let ε=i^−1/3 and

E_i(u)=[k²||u||²_ω−||T_i u||²_ω]/(2k² ε²).

Use mesh kε and x=ε(j+1). For smooth compactly supported G, take u_j=√k ε^(3/2)h_j G(x), so F=xG. Riemann sums in (6) give

||u||²_ω→∫|F|²,
E_i(u)→∫[(q/2)x²|G′|²+x³|G|²]
       =∫[(q/2)|F′|²+x|F|²].                           (7)

Indeed v_i(j)=kx ε²+O_k(ε³(1+x²)); the row and column losses each equal xε²+O_k(ε³) on compact intervals away from zero, and each supplies half the potential. The variance term in (1), divided by 2k²ε², supplies q/2 times radial energy.

Here is a direct complete compactness route. A bounded norm and form imply by (5),(6)

Σ_(εj≥R) ω_j|u_j|²≤C_k/R.

For each fixed R, multiply u by a smooth cutoff in x equal to one up to R and zero after 2R. On this support U_i is bounded below uniformly for sufficiently large i, and variance coefficients in (6) are comparable to those in (1). The cutoff costs at most C_(k,R)ε²||u||² in the unscaled defect, by |Δχ|≤C_(k,R)ε and the bounded adjacent h-ratios. Apply (2) to this localized vector, including its final zero edge; its support is far below the moving physical top. One obtains

Σ|Δu|²+|u_r|²≤C_(k,R)ε².

The linear interpolation of u/√(kε), with zero value at x=0, has bounded H¹ energy on [0,R]. The extension energy from zero to the first site is |u_r|²/[kε²(r+1)], hence bounded. Weighted and unweighted interpolated norms agree asymptotically off zero, while the H¹ bound gives uniform negligible mass near zero. Rellich compactness on bounded intervals plus the tail estimate yields strong L² compactness and a zero Dirichlet trace. No top edge of the physical confined form has been assumed present.

For the liminf, retain only the nonnegative terms in (6) on δ≤x≤R, use weak lower semicontinuity, and then send δ↓0,R↑∞. The scalar shift tends to zero. Smooth functions supported inside (0,∞) give recovery sequences. Min–max applied to these recovery spaces and compact eigenvector sequences proves convergence of every fixed low form eigenvalue to that of

H=−(q/2)∂_x²+x on L²(0,∞), with Dirichlet boundary.

Put B=(2/q)^(1/3). Its eigenvalues are −a_m/B, eigenfunctions Ai(a_m+Bx). Thus the singular values satisfy

σ_(i,m)=k[1+(a_m/B)i^−2/3+o_k(i^−2/3)].                 (8)

The first two have a positive order-i^−2/3 gap. Simplicity gives convergence of the leading normalized right singular profile to the positive Airy ground state.

## 5. Evolving quasimode: explicit general-k correction

Let a=a_1, λ=a/B, f(x)=Ai(a+Bx), so (q/2)f″−xf=λ f. Define

p(x)=−(q+3)x²/(6q)−(q−1)λ x/(3q), g=p f,
β=(7k−6)/6,
F_i(j)=χ(x/log i)[f(x)+ε g(x)],
N_i=||F_i||_ω, ψ_i=F_i/N_i,
t_i=k[1+λ ε²+β ε³], s_i=t_i N_i/N_(i−1).

The smooth nonnegative cutoff is one for its argument≤1 and zero for ≥2. Its errors are smaller than every fixed power of i by Airy decay. For large i, 1+εp is positive on its support and that support lies below the physical top.

The previous-time dilation is ε_(i−1)=ε(1+ε³/3+O(ε⁶)). Critical shift moments are 0, qk/2, qk(q−1)/6 at derivative orders 1,2,3. Direct expansion gives

T_iF_(i−1)=k f+kεg+kε²[(q/2)f″−xf]
 +kε³[(q(q−1)/6)f‴+(4/3)xf′+k f+(q/2)g″−xg]
 +O_k(ε⁴ W(x)),                                      (9)

where W has integrable square and is a polynomial envelope of |Ai(a+Bx)|+|Ai′(a+Bx)|. In particular W need not vanish at x=0: this is an absolute residual estimate, not a pointwise relative-to-f bound at the bottom. Using f‴=(2/q)[f+(x+λ)f′], the uncorrected ε³ term divided by k is

[(4q+2)/3]f+[(q+3)x+(q−1)λ]f′/3.

Meanwhile

(q/2)g″−(x+λ)g=(q/2)p″f+q p′f′
=−(q+3)f/6−[(q+3)x+(q−1)λ]f′/3.

The sum is β f. The bottom forward row is included, since its absent input is at h=0 and f(0)=g(0)=0 exactly. Thus

||T_iψ_(i−1)/s_i−ψ_i||_ω=O_k(ε⁴).                    (10)

This p reproduces the ternary correction when q=2, rather than assuming that correction is independent of arity.

## 6. Weighted adjoint and adjacent-phase norms

The critical weighted adjoint is

(T†F)(t)=q[ω_(t+1)/ω_t]F(t+1)+1_(t≥q)[ω_(t−q)/ω_t]F(t−q).

For t≥q, let D=T†−T. With h=t+1, A=ω_(t+1)/ω_t and C=ω_(t−q)/ω_t, its Taylor moments have

M_0=qA+C−k=O_k(h^−3),
M_1=qA−qC=O_k(h^−2),
M_2=qA+q²C−q−q²=O_k(h^−2),

and all fixed higher moments are bounded. Exact harmonicity gives D h=0, or h M_0+M_1=0. These follow directly from the weight derivative bounds; cancellation of the first differences in M_0 gains its additional power. The exponential part is retained throughout.

Let c=f′(0) and R(h)=f(εh)+εg(εh)−cεh. Because f(0)=f″(0)=0 and g(x)=O_k(x²), for 1≤h≤ε^−1+O_k(1),

|R^(m)(h)|≤C_k ε³[h^(3−m)+h^(2−m)] (m=0,1,2),
|R‴(h)|≤C_k ε³.

Taylor expansion using the displayed moments proves |D R|≤C_kε³. At the finitely many exceptional bottom sites 0≤t<q, directly use D h=0 and the finite coefficients: all remaining values are O_k(ε³). Thus no extrapolation to negative adjoint inputs occurs. For h≥ε^−1, the same moment estimates and Airy derivative envelope give O_k(ε³W(εh)). Hence

||D F_i||_ω=O_k(ε³N_i).

The adjoint inhomogeneous term is −v_i(t+1)[ω_(t+1)/ω_t]F_i(t+1); its leading term is −kxε²F_i(t), with error O_k(ε³N_i). The time shift F_(i−1)−F_i also has this admissible norm. Therefore

||T_i†ψ_i/s_i−ψ_(i−1)||_ω=O_k(ε³).                    (11)

It remains essential to justify the norm ratio at this accuracy. On each phase r, Euler–Maclaurin and the exact weight decomposition yield

N_(r,ε)²=C_(−1)ε^−1+C_0+C_1ε+O_k(ε²),
C_(−1)=(1/k)∫f²>0,

with the three written constants independent of r. For H=(f+εg)², H(0)=H′(0)=0, so the first phase-dependent ordinary mesh correction is O(ε²). The algebraic weight term is [(q−1)/3]ε times the mesh sum of H(x)/x, whose quotient vanishes at zero; its first phase-dependent term is again O(ε²). Finally the exponential weight contributes O(ε²), since |F_i(j)|≤C_k εh_j and Σ|E_j|h_j<∞. Cutoff errors are negligible. Adjacent times change ε by O(ε⁴), yielding

N_i/N_(i−1)=1+O_k(ε³), N_i≍_k ε^−1/2,
ψ_i(0)≍_k ε^(3/2)=i^−1/2 on residue zero.              (12)

All estimates (8),(10)–(12) are thus proved for each fixed k.

## 7. Tracking, positive amplitude and conversion

Start at a sufficiently large fixed I. Let A_i=T_i/s_i and decompose its evolution as y_i=a_iψ_i+z_i, with z_i perpendicular to ψ_i. Equations (10),(11) give the blocks

a_i=(1+O_k(i^−4/3))a_(i−1)+b_i z_(i−1), ||b_i||=O_k(i^−1),
z_i=v_i a_(i−1)+D_i z_(i−1), ||v_i||=O_k(i^−4/3).

The singular gap (8) and convergence of ψ to the ground profile give ||D_i||≤1−c_k i^−2/3: on the complement of ψ, the Rayleigh quotient is at most σ_2²+(σ_1²−σ_2²)o(1), and s_i has the leading σ_1 asymptotics.

The Lyapunov quantity |a_i|+K i^−1/3||z_i|| stays bounded for sufficiently large fixed K. The damping contribution −Kc_k i^−1||z|| absorbs the O_k(i^−1)||z|| scalar coupling; all remaining multiplicative errors are summable. Iterating the stable z-recurrence with bounded a gives ||z_i||=O_k(i^−2/3), using the kernel exp[−c_k(i^(1/3)−m^(1/3))]. Thus a_i converges with error O_k(i^−1/3). At residue zero,

z_i(0)/ψ_i(0)=O_k(i^−1/6).

The factors N_i/N_(i−1) telescope, while

Π_(m=I+1)^i t_m=C_I k^i exp[3λ i^(1/3)]i^β[1+O_k(i^−1/3)],
F_i(0)=B Ai′(a) i^−1/3[1+O_k(i^−2/3)].

Hence d_(kn,0), divided by

k^(kn) exp[3λ(kn)^(1/3)] n^((7k−8)/6),

has a finite limit with absolute error O_k(n^−1/6). The exact conversion is R_n=(qn)!q^(−2qn)d_(kn,0). Stirling changes the polynomial exponent by 1−k/2 and yields the stated normalization. Theorem 1 of the primary paper supplies a strictly positive lower bound on this same normalized sequence, so the limiting constant is positive. The absolute normalized error then becomes relative O_k(n^−1/6).

## Sources and scope

Primary source verified 2026-10-02: Dastidar–Wallner, Asymptotics of relaxed k-ary trees, arXiv:2404.08415v1, https://arxiv.org/html/2404.08415v1 . Equations (3)–(5) supply the exact recurrence and conversion; Theorem 1 supplies the lower Theta estimate. The amplitude theorem and the fixed harmonic-weight argument above are additional work, not statements attributed to that paper.

Base proof and independent approval: /workspace/shared/ternary-airy-amplitude-research/amplitude-proof-candidate.md and independent-gap-audit/leading-amplitude-verdict.md. This extension does not modify those files or address their separate all-orders and DFA investigations.

Exact arithmetic supplement: `python check_exact.py` passes 2,095 rational checks for q=2,…,10, covering critical harmonicity, all residue-channel variance and telescoping identities, and the confined column-loss boundary formula. These checks guard algebra only; they are not the proof of the analytic limits.
