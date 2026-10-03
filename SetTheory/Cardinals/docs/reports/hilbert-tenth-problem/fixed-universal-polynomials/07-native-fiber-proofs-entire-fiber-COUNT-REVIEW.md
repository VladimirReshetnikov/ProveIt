# Conditional whole-fiber height count: independent review

Date: 2026-10-03. Result: **PASS, conditional on the proposed whole-fiber parametrization and exact height law.** This note does not classify the permitted main indices or prove the other native coordinates are forced.

## 1. Hypotheses and answer

Fix integers A≥3 and p≥3 with p≡3 modulo 4. Set

    Δ=A²−1, α=A+√Δ, a=log α,
    c=ψ_A(p)>2p, M=pc/gcd(c,Δ)≥c,
    m_l=Ml  (l=1,2,...),
    R_m=Δψ_A(m)=√Δ sinh(ma),
    b_m=log ε_m=arcosh(R_m), ε_m=R_m+√(R_m²−1).

Assume the fiber is in bijection with the pairs (m,n) for which m=Ml and

    n=p, or n=4mk−p, or n=4mk+p  (k≥1),

and assume its height is exactly max(C,ψ_(R_m)(n)), where C≥1 is fixed, independent of m and n. Every logarithm in this note is natural.

Then, as H→∞,

    N(H)=κ log H+O_(A,p,M,C)(√log H),

where

    κ = 1/[M(p−1)log α]
        + Σ_(l≥1) 1/[2Ml log ε_(Ml)].                 (1)

The first summand comes exclusively from the baseline indices n=p. Separately,

    N_baseline(H) = log H/[M(p−1)log α]+O(1),
    N_nonbaseline(H)
        = (Σ_(l≥1) 1/[2Ml log ε_(Ml)]) log H
          +O(√log H).                                (2)

The candidate coefficient is therefore correct under these hypotheses. Neither counting baseline slices with a fixed-m O(1) estimate nor replacing log ε_m by m log α in the convergent coefficient would prove this coefficient: both can introduce an error of order log H.

### Native-height corollary

Apply the separately established native reconstruction and coordinate domination: the fixed supplied coordinates are <c², the normalized base is R_m=ic²≥c² with i a positive integer, and the other varying supplied coordinates are bounded by y=ψ_(R_m)(n). Since n≥p≥3,

    y≥ψ_(R_m)(3)=4R_m²−1>R_m≥c².

Consequently the complete native supplied-coordinate height is exactly y. Under that reconstruction, all exact formulas below hold for **every H≥1**, with no fixed-coordinate cutoff, and the asymptotic (1) is the entire native-fiber asymptotic. This corollary uses the separate classification and coordinate-domination proof; those facts are not independently established by this counting review.

## 2. Exact finite formulas

For H<C the count is zero. For H≥C, write L=log H and define

    t_m(H)=asinh(H√(R_m²−1))/b_m,
    K_0(H)=floor(L/[M(p−1)a]).

An explicit finite formula, with an empty sum interpreted as zero, is

    N(H)=Σ_(l=1)^(K_0(H)) {
        floor((t_(Ml)(H)+4Ml−p)/(4Ml))
        +floor((t_(Ml)(H)+p)/(4Ml)) }.                (3)

This cutoff is an upper bound, not a claim that every included slice is nonempty. Each summand is a nonnegative integer even when t_m<p. The exact inverse-height argument, rather than an asymptotic approximation to it, is required inside the floors.

Here is a second exact formula that explicitly isolates the baseline. Define

    B(H)=#{l≥1: ψ_(R_(Ml))(p)≤H},
    K_1(H)=floor(√(L/(3a))/M),
    Q_m(H)=max(0,floor((t_m(H)−p)/(4m)))
           +floor((t_m(H)+p)/(4m)).

Then

    N(H)=B(H)+Σ_(l=1)^(K_1(H)) Q_(Ml)(H).            (4)

The function B(H) is the endpoint of a strictly increasing one-variable sequence, so it is obtainable by exact integer comparisons. If an analytic expression is wanted, let ρ_p(H) be the unique real R≥1 satisfying ψ_R(p)=H, for H≥p. Here ψ_R(p) is the Chebyshev polynomial U_(p−1)(R). Then

    B(H)=floor(asinh(ρ_p(H)/√Δ)/(Ma))  (H≥p),
    B(H)=0                            (1≤H<p).       (5)

Equation (5) concerns the baseline count before applying the full-height condition H≥C. The polynomial is strictly increasing on [1,∞), since ψ_(cosh b)(p)=e^((p−1)b)+e^((p−3)b)+...+e^(−(p−1)b), paired into strictly increasing hyperbolic cosines for b>0; its value at R=1 is p.

## 3. Uniform estimates with the Pell base growing

Put β=(log Δ)/2>0. For every m≥1,

    ma ≤ b_m ≤ ma+β.                                (6)

For the lower bound, R_m≥cosh(ma) is equivalent to √Δ tanh(ma)≥1. At m=1 the left side is Δ/A>1, and it increases with m. The upper bound follows from arcosh R≤log(2R) and

    2R_m=√Δ e^(ma)(1−e^(−2ma)).

For every integer n≥1, the exact closed form gives

    log ψ_(R_m)(n)
      =(n−1)b_m+θ_(m,n),
    θ_(m,n)=log(1−e^(−2nb_m))−log(1−e^(−2b_m)),
    0≤θ_(m,n)≤d_*:=−log(1−e^(−2Ma)).                (7)

This bound is uniform in both m and n. In particular, for n=p,

    (p−1)ma ≤ log ψ_(R_m)(p)
              ≤(p−1)ma+(p−1)β+d_*.                (8)

For the inverse-height coordinate, uniformly for all H≥1 and all m=Ml,

    0 ≤ t_m(H)−L/b_m ≤1.                            (9)

Indeed asinh(H sinh b)≥log(2H sinh b)≥log H because b≥a and 2sinh(a)=2√Δ>1. On the other hand,

    sinh(b+log H)−H sinh b
      =e^(−b)(H−H^(−1))/2≥0,

and monotonicity of sinh gives asinh(H sinh b)≤b+log H. A more precise bound is

    1+L/b_m−d(b_m)/b_m ≤ t_m(H) ≤1+L/b_m,
    d(b)=−log(1−e^(−2b)).                           (10)

Thus the changing denominator √(R_m²−1) has not been hidden in a nonuniform constant. In particular the extra 1 in the inverse-height scale explains why the baseline growth exponent is p−1, rather than p.

For completeness, the stronger expansion

    b_m=ma+β+O_A(e^(−2ma))                          (11)

also holds uniformly for m≥1. To see this, write

    b_m−ma−β
      =log(1−e^(−2ma))
       +log((1+√(1−R_m^(−2)))/2).

Both terms are O_A(e^(−2ma)); all their arguments stay uniformly away from zero for m≥1. Consequently

    log ψ_(R_m)(p)=(p−1)ma+(p−1)β
                   +O_(A,p)(e^(−2ma)).             (12)

No expansion is substituted into a floor in this proof.

## 4. Baseline count without accumulated slice errors

The sequence ψ_(R_(Ml))(p) strictly increases with l. Equation (8), with D_0=(p−1)β+d_*, gives

    max(0,floor((L−D_0)/[M(p−1)a]))
       ≤B(H)≤floor(L/[M(p−1)a]).                   (13)

Hence B(H)=L/[M(p−1)a]+O(1). This is a single monotone threshold count. There is no sum of O(1) errors over the Θ(log H) slices that admit n=p.

Equation (8) also proves the cutoff in (3): if a slice contains any tuple below H, its least index p does, and m≤L/[(p−1)a]. The fixed-slice exact formula quoted in the prior slice theorem then gives (3).

## 5. Only O(√log H) slices have nonbaseline points

The least nonbaseline index is n_0(m)=4m−p. Since m≥M≥c>2p, we have m≥p+1 and therefore

    log ψ_(R_m)(4m−p)
      ≥(4m−p−1)b_m
      ≥3am².                                      (14)

It follows that every nonbaseline-active slice has

    m≤√(L/(3a)),

which proves (4) and the bound K_1(H)=O(√L). This is the only family over which fixed-slice floor discrepancies will be summed.

The actual number J(H) of nonbaseline-active slices has the sharper estimate

    J(H)=√L/(2M√a)+O(1).                            (15)

Indeed the least nonbaseline height is strictly increasing with m, and (6)–(7) give

    4am²−(p+1)am
      ≤log ψ_(R_m)(4m−p)
      ≤4am²+4βm+d_*.

Solving the two quadratic threshold inequalities locates the endpoint at m=√L/(2√a)+O(1); restricting to multiples of M proves (15). Estimate (15) is useful but is not needed for the error bound below.

## 6. Nonbaseline asymptotic and the infinite coefficient tail

For every t≥0 and m≥M, set

    Q_m(t)=max(0,floor((t−p)/(4m)))
             +floor((t+p)/(4m)).

Then

    |Q_m(t)−t/(2m)|≤2.                             (16)

For t≥p this follows by subtracting the two fractional parts. For 0≤t<p, Q_m(t)=0 and t/(2m)<p/(2m)<1/4. Combining (9) and (16) yields the uniform estimate

    |Q_m(H)−L/(2m b_m)|≤2+1/(2m).                  (17)

Summing (17) over the deterministic cutoff K=K_1(H), including any inactive slices inside that cutoff, proves

    N_nonbaseline(H)
       =L Σ_(l=1)^K 1/[2Ml b_(Ml)]+O(K).           (18)

The coefficient converges absolutely by b_(Ml)≥Ml a. Its tail satisfies, for K≥1,

    0≤Σ_(l>K) 1/[2Ml b_(Ml)]
       ≤1/(2aM²) Σ_(l>K) 1/l²
       ≤1/(2aM²K).                                (19)

As H→∞, K∼√L/(M√(3a)). Thus extending the finite sum in (18) to infinity costs O(L/K)=O(√L), while its summed floor error is O(K)=O(√L). This proves the second line of (2), and (13) proves the first. Together they prove (1).

For example, when L≥12aM², K≥√L/(2M√(3a)), so a fully explicit error estimate available directly from this proof is

    |N_nonbaseline(H)−κ_nonbaseline L|
      ≤(2+1/(2M))√L/(M√(3a))
        +√3 √L/(M√a).

The baseline error is at most 1+D_0/[M(p−1)a]. These constants are deliberately simple, not optimal.

## 7. Further checks and evidence boundary

The nonbaseline coefficient obeys

    0<κ_nonbaseline≤π²/[12aM²].                     (20)

Its partial sums have the rigorous computable error bound (19). The dependence on the exact normalized auxiliary base ε_(Ml) is genuine; asymptotically replacing it by α^(Ml) changes κ in general.

The proof does not establish that the permitted m are exactly the multiples of M, that the native reconstruction has no other freedoms, or the native supplied-coordinate domination. Those are separate classification and domination obligations. With those obligations established, the native-height corollary removes the fixed-coordinate cutoff and gives the exact count for every H≥1, along with the asymptotic above. Without those obligations, this note still counts the stipulated pair family and must not be presented as an unconditional native-fiber theorem.

The fixed-slice exact formula used in (3) was inspected in the existing local slice theorem. Everything else here follows from the displayed Pell closed forms and elementary inequalities. No author code was run and no frozen artifact was edited.
