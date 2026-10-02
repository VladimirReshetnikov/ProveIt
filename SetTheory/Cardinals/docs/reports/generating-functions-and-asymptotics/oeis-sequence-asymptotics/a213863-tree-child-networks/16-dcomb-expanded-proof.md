# Fixed-d combining tree-child networks: contractive Airy extension

Research proof draft, 2 October 2026. Separate from the frozen A213863 release.
All asymptotic assertions below fix an integer d >= 2. Constants may depend on d and the requested finite order. No uniformity as d tends to infinity is asserted. This document is not externally peer reviewed.

## 1. Sources, target, and exact reduction

Chang–Fuchs–Liu–Wallner–Yu, *Enumerative and Distributional Results for d-combining Tree-Child Networks*, Advances in Applied Mathematics 157 (2024), 102704:
https://web.math.nccu.edu.tw/mfuchs/d-comb-journal-rev.pdf

Their Proposition 3.7 and equations (17)–(18) give

    b[n,m] = binom(d*n+m-2,d-1) sum_{j=1}^m b[n-1,j],
    b[1,1]=1, b[n,m]=0 for m>n or m<1,
    c[n]=sum_m b[n,m], c[0]=1.

Theorem 3.4 gives the exact maximal-reticulation identity

    T[n,n-1] = n! c[n-1].

Define q[n,m]=b[n,m]/binom(d*n+m-2,d-1) on 1<=m<=n. Then for n>=2,

    q[n,m]=q[n,m-1]+binom(d*(n-1)+m-2,d-1)q[n-1,m],

with q[n,0]=0 and the preceding row extended by zero beyond its diagonal. Put

    A[n,k]=q[n+1,k+1], 0<=k<=n; A[0,0]=1.

Consequently, exactly,

    A[n,k]=A[n,k-1]+binom(d*n+k-1,d-1) A[n-1,k], 1<=k<=n,
    A[n,0]=prod_{i=1}^n binom(d*i-1,d-1),
    A[n-1,n]=0, a[n]:=A[n,n]=c[n].                     (1)

The boundary identity is q[n+1,n+1]=q[n+1,n]=sum_{j=1}^n b[n,j]=c[n]; equivalently A[n,n]=A[n,n-1]=c[n]. This checks the otherwise important shift at the upper boundary. At d=2 this is exactly the A213863 triangle. At d=3 its diagonal begins

    1,1,25,2305,482825,183500625,111174597625,98734811198625.

Set

    Lambda=(d+1)^(d-1)/(d-1)!, Gamma=4 Lambda,
    c=2(d-1)/(d+1), ell=c^(2/3) z,
    eta=(d-1)^2/[2(d+1)], rho=-eta-1/2,
    B=3 z ((d-1)/(d+1))^(2/3),

where z is the largest negative Airy zero. The cited Theorem 1.8 and exact identity imply

    a[n] = Theta((n!)^(d-1) Gamma^n exp(B n^(1/3)) n^rho).  (2)

For clarity, the source uses the leaf variable v and exponent

    alpha=-d(3d-1)/[2(d+1)].

Put v=n+1 and divide the two-sided source bound for T[v,v-1] by (n+1)!. The remaining factorial is ((n+1)!)^(d-1)=(n!)^(d-1)(n+1)^(d-1). Also Gamma^(n+1)=Gamma*Gamma^n and exp(B[(n+1)^(1/3)-n^(1/3)]) tends to one. The polynomial exponent becomes alpha+d-1=-(d^2-d+2)/[2(d+1)]=rho. Hence both the upper and the lower bound in (2) hold with fixed positive d-dependent constants.

The new target proved below is existence of gamma_d>0 and, for each finite M,

    a[n] = gamma_d (n!)^(d-1) Gamma^n exp(B n^(1/3)) n^rho
           * (1+sum_{r=1}^M C[d,r] n^(-r/3)+O_d,M(n^(-(M+1)/3))). (3)

Coefficients are uniquely computable and belong to Q[B] for each fixed integer d. The claim concerns finite Poincare expansions, not convergence of an infinite series.

The cited paper proves only the Theta estimate and explicitly flags the missing equivalent in Remark 1.12. Corollary 1.11 proves total/maximal -> 1 for d>=3. Thus (3) yields a positive leading equivalent for total counts, but does not by itself yield their higher-order corrections.

## 2. Exact contractive cocycle

For N=n+k and j=n-k put

    D_N(j)=A[n,k]/[Lambda^n (n!)^(d-1)],

and put D_N=0 off its physical parity and interval. Then D_0=e_0 and (1) gives

    D_N(j)=D_(N-1)(j+1)+p_N(j)D_(N-1)(j-1),
    p_N(j)=prod_{h=1}^{d-1} (1-2(j+h)/[(d+1)(N+j)]).       (4)

The downward term is absent at j=0. At j=N, (4) reproduces precisely the initial column in (1), so no initial boundary is omitted. Recover a[n]=Lambda^n(n!)^(d-1)D_(2n)(0).

For N>=1 and j>=1, each factor on the relevant interval j<=N+1 is positive and at most one. In fact every factor is at least 1/(d+1), since d*N+(d-2)*j>=2h for N,j>=1 and h<=d-1. Its derivative with respect to N is

    2(j+h)/[(d+1)(N+j)^2] > 0.

Thus p_N increases with N. Let G_N(0)=1, G_N(j)^2=prod_{k=1}^j p_N(k). Let S_N have edge sqrt(p_N(j)) between j-1 and j on 0,...,N+1, and zero-pad outside. Let Q_N(j)=G_(N-1)(j)/G_N(j) for N>=2 on that interval, and zero outside; Q_1 is projection onto e_0. With v_N=G_N^(-1)D_N the exact identity is

    v_N=S_N Q_N v_(N-1).                                  (5)

Since Q_N is a diagonal contraction and S_N has all edges at most one,

    0<=S_NQ_N<=J entrywise; ||S_NQ_N||<=lambda_N,           (6)

where J is half-line adjacency and lambda_N is the Perron eigenvalue of S_N. This is the essential structural replacement for merely assuming the published two-weight recurrence behaves like the binary case.

## 3. Global spectral input

Let epsilon=N^(-1/3), x_j=(j+1)epsilon. The quadratic form of 2I-S_N is the sum of weighted squared adjacent differences plus potentials 2-b_j-b_(j+1), with boundary terms 2-b_1 and 2-b_(N+1). Split the first as 1+(1-b_1) to retain the Dirichlet interval from 0 to epsilon.

The lower bound on the edge weights is positive for fixed d. Also

    1-sqrt(p_N(j)) >= (1-p_N(j))/2
                      >= (j+1)/[(d+1)(N+j)].

Therefore the scaled form controls a positive constant times sum_j x_j |v_j|^2, as well as local discrete gradient energy. Piecewise-linear interpolation with nodal values epsilon^(-1/2)v_j, zero at the fictitious endpoint x=0, is locally H^1-bounded for bounded scaled energy. The potential bound makes L^2 tails uniformly small. Hence the interpolations are strongly L^2 precompact; their lower limiting form is

    integral_0^infty (|f'|^2+c*x*|f|^2) dx,

with Dirichlet trace. Conversely sampling compactly supported smooth Dirichlet functions supplies recovery vectors. Min–max gives convergence of every fixed low eigenvalue to that of -partial_x^2+c*x. Consequently

    lambda_N=2+ell N^(-2/3)+o(N^(-2/3)),
    lambda_N-lambda_(2,N) ~ c^(2/3)(z-z_2) N^(-2/3).       (7)

The matrix is bipartite. Its negative top eigenvalue has the same modulus; the needed gap is the singular-value gap between opposite parity spaces, not a full spectral-radius gap.

## 4. Finite quasimodes and drift

The exact downward factor on the scaled window is

    p_-(epsilon,x)=prod_{h=1}^{d-1}
          [1-2(x epsilon^2+(h-1)epsilon^3)/
                   ((d+1)(1+x epsilon^2-epsilon^3))],

and the other frozen edge is p_+(epsilon,x)=p_-(epsilon,x+epsilon). Write

    kappa0=(d-1)(d-2)/(d+1).

Then p_-=1-c*x*epsilon^2-kappa0*epsilon^3+O(epsilon^4), so

    sqrt(p_-)F(x-epsilon)+sqrt(p_+)F(x+epsilon)
      =2F+epsilon^2(F''-c*x*F)
        -(c/2+kappa0)epsilon^3 F+O(epsilon^4).

For F(x)=Ai(z+c^(1/3)x), this yields

    lambda_N=2+ell N^(-2/3)-2 eta N^(-1)+O_d(N^(-4/3)).    (8)

All finite frozen correcting profiles exist. Indeed with L=partial_x^2-c*x-ell,

    L(PF+QF')=(P''+2(c*x+ell)Q'+cQ)F+(2P'+Q'')F'.

Eliminating P' yields the polynomial operator

    Q -> -Q'''/2+2(c*x+ell)Q'+cQ,

which is triangular with nonzero diagonal c(2j+1) on x^j. A new scalar eigenvalue coefficient changes Q by a nonzero constant; choose it so Q(0)=0, then choose the free constant of P to impose P(0)+Q'(0)=0. This proves solvability without resonant logarithms.

Construct through epsilon^5 and cut off smoothly at j<=2 sqrt(N), identically one at j<=sqrt(N). Taylor remainders are epsilon^6 times a fixed polynomial–Airy envelope. Cutoff terms are exponentially small in N^(1/4). Normalize samples in ell^2. The residual is O_d(epsilon^6); (7) gives eigenvector error O_d(epsilon^4). In particular the positive unit Perron vectors satisfy

    ||psi_N-psi_(N-1)||=O_d(N^-1),
    psi_N(0)=sqrt(c) N^-1/2(1+O_d(N^-1/3)).               (9)

For the second assertion use integral F^2=c^(-1/3)Ai'(z)^2; a global sign can be chosen so F'(0)>0.

On the cutoff support, logarithmic differentiation of the finite factor product gives

    0<=1-Q_N(j)<=C_d*j(j+d)/N^2.

The polynomial–Airy moments and O(N^-4/3) eigenvector error therefore give

    ||(I-Q_N)psi_N||+||(I-Q_N)psi_(N-1)||=O_d(N^-4/3).    (10)

The same derivative estimates give -log G_N(j)<=C_d*j(j+d)/N, so G_N^-1 is uniformly bounded on the cutoff support. None of these constants is asserted uniform over unbounded d.

## 5. Positive scalar amplitude, with boundary recovery

Set P_N=prod_{i=1}^N lambda_i, u_N=v_N/P_N, M_N=S_NQ_N/lambda_N. They are contractions and ||u_N||<=1. Let g_N and h_N be sqrt(2) times psi_N restricted to current and preceding parity respectively. Both have norm one and S_N h_N=lambda_N g_N. Equations (9)–(10) imply

    ||h_N-g_(N-1)||=O(N^-1),
    ||(I-Q_N)h_N||+||(I-Q_N)g_(N-1)||=O(N^-4/3).

Write u_N=A_N g_N+w_N, w_N perpendicular to g_N. The singular gap gives

    ||w_N|| <= (1-a N^-2/3)||w_(N-1)||+C N^-1,

hence ||w_N||=O(N^-1/3), by the convolution estimate

    sum_{k<=N} k^-r prod_{i=k+1}^N(1-a i^-2/3)
      =O_r(N^(2/3-r)).

The exact adjoint identity M_N^* g_N=Q_N h_N gives

    A_N=t_N A_(N-1)+<Q_N h_N-g_(N-1),w_(N-1)>,
    t_N=<Q_N h_N,g_(N-1)>=1+O(N^-4/3).

Therefore A_N converges to A_infinity>=0 with error O(N^-1/3).

A coordinate cannot be recovered from the ell^2 error alone. Instead, for U(N,k)=M_N...M_(k+1), entrywise domination (6) and the Catalan identity yield, for L<=N^(2/3),

    ||e_0^T U(N,N-L)||_2
       <= ||e_0^T J^L||_2/(lambda_(N-L+1)...lambda_N)
       <= C_d(L+1)^(-3/4).

Here ||e_0^T J^L||_2^2=Catalan(L)<=C4^L(L+1)^(-3/2), and (8) bounds the denominator correction on this time window. Duhamel applied to the exact w recurrence over L=floor(N^(2/3)) gives

    w_N(0)=O_d(N^-5/6).                                  (11)

From (8),

    P_N=kappa_d 2^N exp((3ell/2)N^(1/3)) N^-eta
          (1+O_d(N^-1/3)), kappa_d>0.                    (12)

One convergent exact definition is

    log kappa_d=(ell/2)zeta(2/3)-eta*EulerGamma
       +sum_{N>=1}[log(lambda_N/2)-(ell/2)N^-2/3+eta/N].

Combining (9), (11), (12), for even N,

    D_N(0)=kappa_d sqrt(2c) A_infinity
             2^N exp((3ell/2)N^(1/3)) N^rho
            +O_d(2^N exp((3ell/2)N^(1/3)) N^(rho-1/3)).

If A_infinity=0 this contradicts the lower half of (2). Hence it is strictly positive, and

    gamma_d = kappa_d A_infinity sqrt(c) 2^-eta > 0.      (13)

This already proves the leading equivalent, rather than only subsequential compactness or a formal ansatz.

## 6. All finite orders and exact remainder transfer

For the original unsymmetrized recurrence (4), seek

    Z_N(j)=H_N sum_{r>=0} epsilon^r F_r(x_j), F_0=F,
    F_r(0)=F_r'(0)=0 (r>=1),
    H_N/H_(N-1) ~ 2(1+sum_{m>=2}s_m epsilon^m).

At the preceding time, arguments are (x±epsilon)(1-epsilon^3)^(-1/3), and profile powers acquire (1-epsilon^3)^(-r/3). The product p_- above is analytic on each growing cutoff window. At order m the new equation is

    L F_(m-2)-2s_m F+R_m F+T_m F'=0,

where R_m,T_m are previously known polynomials. The same triangular inverse from Section 4 gives the unique normalized F_(m-2) and s_m. In particular

    s_2=ell/2, s_3=-eta-1/6.

For example the order-three forcing is

    -kappa0 F+(c+2/3)x F'.

Its F-inner product, using integral xFF'=-(1/2)integral F^2, gives exactly 2s_3=-kappa0-c/2-1/3. This checks the changed polynomial exponent independently.

Choose a genuine finite scalar expression

    log H_N=N log2+(3ell/2)N^(1/3)+(-eta-1/6)log N
                  +sum_{r=1}^J h_r N^(-r/3).

Its successive h_r enter one-step logarithmic matching with nonzero coefficient -r/3 at order epsilon^(r+3). Fix its multiplicative constant to one at every truncation. After sufficiently many orders, cut off and restrict Z_N to j congruent to N modulo 2, setting all other coordinates to zero. Symmetrization then gives

    z_N=G_N^-1 Z_N/P_N,
    ||z_N||=O_d(1),
    r_N=z_N-M_N z_(N-1)=O_d,p(N^-p)

for any prescribed p>1. The sample norm is asymptotic to N^(1/6)sqrt(I/2), while H_N/P_N~kappa_d^-1 N^-1/6, so all truncations have the same positive limiting projection

    <g_N,z_N> -> q_0=kappa_d^-1 sqrt(I/2).

Put e_N=u_N-(A_infinity/q_0)z_N and write e_N=alpha_N g_N+W_N. Its scalar projection tends to zero. The already proved gap and adjoint estimates imply

    ||W_N|| <= (1-aN^-2/3)||W_(N-1)||
                  +C N^-1 |alpha_(N-1)|+C N^-p,
    |alpha_N-alpha_(N-1)| <= C N^-4/3 |alpha_(N-1)|
                  +C N^-1 ||W_(N-1)||+C N^-p.

If alpha_N=O(N^-q), the first estimate and convolution imply

    ||W_N||=O(N^(-q-1/3)+N^(2/3-p)).

Summing the second estimate backwards from its zero limit gives alpha_N=O(N^(-q-1/3)+N^(1-p)). Starting at q=0 and iterating finitely many times yields ||e_N||=O(N^(1-p)). Boundary smoothing over the last N^(2/3) steps then gives e_N(0)=O(N^(1/2-p)); relative to the leading endpoint N^-1/2 this is O(N^(1-p)). Since p is arbitrary, every finite formal order transfers to the exact diagonal with the same gamma_d. This proves (3).

For the coefficient field, use t=(N/2)^(-1/3), y=(j+1)t. The Airy equation becomes

    Ftilde''=(((d-1)/(d+1))*y+B/3)Ftilde.

The recurrence coefficient, time dilation, polynomial inverses and scalar matching all have rational coefficients for fixed integer d. Thus the normalized endpoint coefficients are in Q[B].

## 7. Network consequence and inversion

The exact identity T[n,n-1]=n!a[n-1] transfers (3) to every finite order:

    T[n,n-1]=(gamma_d/Gamma)(n!)^d Gamma^n exp(B n^(1/3))
                n^alpha (1+sum_{r=1}^M E[d,r]n^(-r/3)
                                +O_d,M(n^(-(M+1)/3))),
    alpha=-d(3d-1)/[2(d+1)].

For d>=3 the published total/maximal ratio implies

    T[n] ~ (gamma_d/Gamma)(n!)^d Gamma^n exp(B n^(1/3)) n^alpha.

It does NOT imply all finite corrections for T[n]; that would need a separate uniform deficit argument. No binary Pons–Batle identity is imported here.

For either a[n] or the maximal-network sequence let f(x) be the log-asymptotic smooth scale, with factorial power p=d-1 or d and polynomial exponent r=rho or alpha. Stirling gives

    f(x)=p*x*log x+(log Gamma-p)*x+B*x^(1/3)
             +(r+p/2)log x+K+sum_{j>=1}L_j*x^(-j/3),

where K=log(amplitude)+(p/2)log(2pi), and Stirling terms are included in L_j. For y=log(target), write a=log Gamma-p and

    x_0 = (y/p)/W_0(exp(a/p)*y/p).

This solves the leading x log x+x equation exactly. Newton/Taylor reversion with f'(x)=p log x+log Gamma+o(1)>0 produces every desired finite inverse order; for example the first correction is

    x=x_0-[B*x_0^(1/3)+(r+p/2)log x_0+K]/
                  [p log x_0+log Gamma]
           +O_d(x_0^(-1/3)/log x_0).

The O bound includes both the first omitted Airy term and quadratic Taylor error (the latter is smaller by two logarithmic factors). For a truncation with log-error O(x^-R/3), the corresponding root uncertainty is O(x^-R/3/log x). Integer thresholds are described by bracketing the monotone count at neighboring integers; blindly taking a ceiling is not certified when the asymptotic root is within its error of an integer.

### Explicit ternary-combining diagonal coefficients

For d=3, Gamma=32, rho=-1 and B=3z/2^(2/3). Exact polynomial recursion through degree six gives

    log[a[n]/(gamma_3 (n!)^2 32^n exp(B*n^(1/3))*n^-1)]
       = (B^2/162)n^-1/3+(11B/324)n^-2/3
          +(4B^3/6561-3/16)n^-1+O(n^-4/3).

These are symbolic coefficients, not fitted values. The separate binary replay must recover the frozen A213863 coefficients.

## 8. Status and limitations

This is a fixed-d structural proof, not a claim that the binary proof automatically generalizes. The changed recurrence, all boundaries, factor positivity, monotonicity, global spectral confinement, changed eta, and unchanged summable drift mechanism have each been identified explicitly. Reproducible finite algebra and recurrence tests accompany it; they verify calculations, not the asymptotic estimates on their own.

A bounded current-source search found no later published amplitude theorem, consistent with the 2026-listed Chang dissertation repeating the missing-equivalent statement. Universal novelty is not certified. A213863 is the d=2 member; no d>=3 OEIS accession was verified by phrase and initial-term web searches, so none is asserted.
