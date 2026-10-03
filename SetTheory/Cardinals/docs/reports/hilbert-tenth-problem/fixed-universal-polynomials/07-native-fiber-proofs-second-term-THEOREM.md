# Two terms for the unsmoothed entire native-fiber count

Date: 2026-10-03. This is a separate analytical addendum. Earlier reports, the whole-fiber classification packet, and all pinned source files are unchanged.

## 1. Result and hypotheses

Assume the proved entire-fiber classification and native height law in `../entire-fiber/THEOREM.md`. Thus the twenty-two-coordinate positive native witnesses are in bijection with

    m = M l,       l = 1,2,...,
    n = p, or 4mk−p, or 4mk+p,       k = 1,2,...,

and their maximum supplied-coordinate height is exactly ψ_(R_m)(n). Here the fixed data satisfy

    A ≥ 3, Δ = A²−1, α = A+√Δ, λ = log α,
    p ≡ 3 (mod 4), p ≥ 3, c = ψ_A(p),
    M = M0 = pc/gcd(c,Δ) ≥ c > 2p,
    R_m = Δψ_A(m) = √Δ sinh(mλ),
    β_m = arcosh R_m = log(R_m+√(R_m²−1)).

All logarithms are natural. Constants in every O-term may depend on these fixed data. Set T = log H and

    κ = 1/[M(p−1)λ] + Σ_(l≥1) 1/[2Ml β_(Ml)],
    d = ζ(1/2)/(M√λ).

Then the ordinary, unsmoothed count of complete witness tuples satisfies

    N(H) = κT + d√T + O(T^(1/3))                 as H → ∞.       (1)

In particular d < 0. The convergent series in κ uses the exact β_(Ml), not its linear approximation. No averaging, Riesz mean, or generic-position hypothesis is used. The estimate holds for every sufficiently large real H, including exact Pell-height jump boundaries.

List all complete witness tuples in nondecreasing height, counting different tuples separately even if they have equal height; any ordering within a tie is allowed. If H_v is the height of the v-th tuple, v ≥ 1, then

    log H_v = v/κ − [ζ(1/2)/(M√λ κ^(3/2))]√v + O(v^(1/3)).      (2)

Thus the square-root correction in (2) is positive. Equation (2) is a logarithmic asymptotic. It does not imply that H_v divided by the exponential of the two displayed terms tends to 1.

## 2. Exact energy and uniform estimates

Write

    q = Mλ, b = (log Δ)/2, β_l = β_(Ml),
    a = 4λM², a_l = 4Ml β_l,
    n_σ(l,k) = 4Mlk + σp,       σ ∈ {−1,+1},
    E_σ(l,k) = log ψ_(R_(Ml))(n_σ(l,k)).

The exact geometric-sum identity gives, for every n ≥ 1,

    log ψ_(R_(Ml))(n) = (n−1)β_l + θ(l,n),
    θ(l,n) = log(1−exp(−2nβ_l)) − log(1−exp(−2β_l)),
    0 ≤ θ(l,n) ≤ d_* := −log(1−exp(−2q)).                    (3)

The bounds established in the whole-fiber counting review give

    ql ≤ β_l ≤ ql+b.                                          (4)

Consequently

    E_σ(l,k) = a_l k + (σp−1)β_l + θ(l,n_σ(l,k)),             (5)
    a_l = a l² + O(l),
    1/a_l = 1/(a l²) + O(l^(−3)).                            (6)

The θ-term in (5) is retained. In fact θ is exponentially small in l, but boundedness suffices here. Likewise the sharper expansion β_l = ql+b+O(exp(−2ql)) is not needed for the error exponent in (1).

More explicitly, using k,l ≥ 1 in (3)–(4),

    |E_σ(l,k)−a k l²| ≤ C k l,                               (7)
    C = 4Mb + (p+1)(q+b) + d_*.

Both signs have n_σ ≥ p ≥ 3, so E_σ > 0. From (7), with D=C/a,

    |√(E_σ(l,k)/(ak))−l|
      = |E_σ(l,k)/(ak)−l²| / [√(E_σ(l,k)/(ak))+l]
      ≤ D.                                                   (8)

This is a uniform exact-energy bound, not the substitution of an asymptotic energy inside a floor.

For fixed l, let r_σ(l,T) be the number of k ≥ 1 with E_σ(l,k) ≤ T. Formula (5) gives the pointwise sandwiches

    max(0, floor((T−(σp−1)β_l−d_*)/a_l))
      ≤ r_σ(l,T)
      ≤ max(0, floor((T−(σp−1)β_l)/a_l)).                    (9)

Since |(σp−1)β_l/a_l| ≤ (p+1)/(4M) and a_l ≥ a, this proves

    r_σ(l,T) = T/a_l + O(1)                                  (10)

uniformly in every l ≥ 1 and T ≥ 0. The positive-part clipping is covered by the Lipschitz bound |max(0,x+c)−x| ≤ |c| for x ≥ 0; the remaining floor discrepancy is at most one.

For fixed k put x_k=√(T/(ak)). Estimate (8) proves that all integers l ≤ x_k−D are admitted and every admitted l satisfies l ≤ x_k+D. Therefore the column count restricted to l>L obeys

    #{l>L : E_σ(l,k)≤T} = (x_k−L)_+ + O(1),                  (11)

uniformly in k,T and integers L≥0. This follows directly by bounding the count between max(0,floor(x_k−D)−L) and max(0,floor(x_k+D)−L). No floor is assumed stable under a small perturbation.

## 3. Hyperbola split and every boundary column

For T large enough set

    L = floor(T^(1/3)),   X = T/a,   K = floor(X/L²).

Then L and K are each comparable to T^(1/3), with constants allowed to depend on a, and eventually L>D+1 and K≥1.

Split one sign's count into l≤L and l>L. The first part, by (10), is

    Σ_(l≤L) r_σ(l,T) = T Σ_(l≤L) 1/a_l + O(L).              (12)

The remaining part can have no nonzero column with

    k > X/(L+1−D)²,                                         (13)

because admission of some l≥L+1 and (8) imply L+1≤x_k+D. The right side of (13) differs from X/L² by O(X/L³)=O(1). Thus at most O(1) possible columns lie above K. For every k>K we have x_k<L, and the upper count in (11) is at most D+1. All such extra columns therefore contribute O(1) in total. This also covers the case where the cutoff in (13) falls below K.

For k≤K, x_k≥L and (11) may be summed without clipping. It follows that

    Σ_(l>L) r_σ(l,T)
      = √X Σ_(k≤K) k^(−1/2) − LK + O(K+1).                  (14)

Equations (12) and (14) are an unsmoothed hyperbola decomposition with all outer boundary columns accounted for. No rectangular boundary error has been silently discarded.

## 4. Cancellation, exact coefficient, and the zeta term

The tail estimate in (6), together with the integral estimate for Σ_(l>L) l^(−2), yields

    Σ_(l>L) 1/a_l = 1/(aL) + O(L^(−2)).                     (15)

The classical Euler–Maclaurin / zeta partial-sum formula gives

    Σ_(k≤K) k^(−1/2) = 2√K + ζ(1/2) + O(K^(−1/2)).         (16)

For example, (16) follows immediately from NIST DLMF 25.2.8 at s=1/2: the remainder is one-half of an integral of {x}x^(−3/2), bounded in absolute value by K^(−1/2). See https://dlmf.nist.gov/25.2.E8. This is the classical generalized-divisor hyperbola / Euler–Maclaurin method, specialized here to the exact Pell energy. The negative sign of ζ(1/2) also follows from the alternating-series representation https://dlmf.nist.gov/25.2.E3.

Let C0=Σ_(l≥1)1/a_l. Combining (12)–(16) gives

    Q_σ(T) = C0 T + ζ(1/2)√X
             + [2√(XK)−LK−X/L]
             + O(L+K+T/L²+√(X/K)+1).                         (17)

The bracket cancels to

    2√(XK)−LK−X/L = −L(√K−√X/L)².                         (18)

Because K=floor(X/L²), its absolute value is O(L/K)=O(1). Every other error in (17) is O(T^(1/3)). Therefore, separately for each sign,

    Q_σ(T) = T Σ_(l≥1) 1/[4Mlβ_l]
             + [ζ(1/2)/(2M√λ)]√T + O(T^(1/3)).             (19)

The two signs are disjoint since 0<p<2m. The exceptional n=p family is also disjoint from them. The baseline count, already proved without summing row discrepancies over its Θ(T) support, satisfies

    B(T) = T/[M(p−1)λ] + O(1).                              (20)

Adding (19) for the two signs and (20) proves (1).

Importantly, the exact infinite sum C0 is retained before estimating its tail. Replacing β_l by ql in C0 generally changes the leading coefficient by a nonzero constant and hence causes an order-T error. Boundedness of β_l−ql affects only the controlled tail error T/L² after the exact coefficient is extracted.

## 5. Ranked-height inversion, including ties

Define F(T)=N(exp T), and write T_v=log H_v. F counts tuples with multiplicity, is finite at every finite T, and is unbounded. Hence T_v is defined for every v, and T_v→∞. Independently of any equal heights,

    F(T_v−1) < v ≤ F(T_v).                                  (21)

Applying (1) at T_v and T_v−1 shows

    v = κT_v + d√T_v + O(T_v^(1/3)).                         (22)

This uses only a fixed logarithmic interval below T_v; no bound on jump multiplicity and no uniqueness of heights is assumed. First (21) and F(T)~κT yield T_v~v/κ, with κ>0. Next (22) yields T_v−v/κ=O(√v), so

    √T_v = √(v/κ)+O(1).

Substitution in (22) proves (2). In particular, for suitable fixed C and all sufficiently large v,

    exp(v/κ−d κ^(−3/2)√v−Cv^(1/3))
      ≤ H_v ≤
    exp(v/κ−d κ^(−3/2)√v+Cv^(1/3)).                         (23)

A multiplicative equivalent with ratio tending to one would require an o(1) logarithmic error, which has not been proved here.

If maximum bit length is bounded by b_int, H=2^(b_int)−1 gives

    N_bits(b_int) = κ(log 2)b_int
      + [ζ(1/2)√(log 2)/(M√λ)]√b_int + O(b_int^(1/3)).       (24)

## 6. Scope, evidence, and provenance

The classification, positive reconstruction, exact native maximum height, and pinned Pell rank/congruence results are prerequisites from the earlier packet. This addendum proves a stronger count and ranked-height consequence for that already classified fiber. It does not simplify the source circuit, prove finite-foldness, materialize its astronomical tuples, or claim literature-wide novelty.

The analytic proof is elementary and uses the classical generalized divisor hyperbola idea and the classical Euler–Maclaurin expansion. Finite computational checks in this directory are secondary evidence only. They use small auxiliary Pell-count models, clearly distinguished from the complete padded native source. The exact theorem does not rely on floating-point agreement.

Independent review: `INDEPENDENT-COUNT-REVIEW.md`. Numerical and exact boundary checks: `CHECKS.md` and `../../check_second_term.py`. Reproduction instructions and file hashes: `README.md` and `../../provenance/second-term-original-MANIFEST.sha256`.
