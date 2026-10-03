# Bounded label multiplicity in ascent sequences: factorial root limit

Research proof, 1 October 2026. This file treats every fixed integer b >= 3. The separately proved b=2 case has the same formula. The exact combinatorial reduction is proved in `compaction-proof.md`; its independent finite checks are in `compaction-verify.py` and `compaction-validation.json`.

## Theorem

Let a_n^(b) count ascent sequences of length n in which every value occurs at most b times, with a_0^(b)=1. Put

    E_b(v) = sum_{j=0}^b v^j/j!,
    T_b = integral_0^infinity log E_b(v)/(E_b(v)-1) dv.

For every fixed integer b >= 3,

    lim_{n -> infinity} (a_n^(b)/n!)^(1/n) = 1/T_b.

The exponential generating function has radius T_b. Equivalently,

    log a_n^(b) = log(n!) - n log T_b + o(n).

This is a factorial exponential growth theorem, not an asymptotic equivalent or a ratio-limit theorem. The family is OEIS A294220, with b=2 column A202058 and b=3 column A317784. The previously proved b=2 result is T_2=3*pi^2/8. For b=1 there is just one increasing word at each length, and T_1=infinity agrees with the zero normalized root limit.

## 1. Exact grouped operator

Take s_j labels currently used exactly j times, 1 <= j < b, and u unused labels; exhausted labels have been deleted. Sort the remaining budgets increasingly, so physical groups are j=b-1,b-2,...,1,0, where j=0 denotes unused labels. Let

    m = u + sum_j s_j,
    u >= 1, 0 <= k < m.

The threshold k is the number of active labels not exceeding the last value. It remains meaningful when that last value has just been exhausted and deleted.

For every rank i=0,...,m-1, let j be its usage group, and set alpha=1_{i>=k}. The transition consumes one occurrence, creates an additional unused label iff alpha=1, and then sorts the budgets below the new threshold. Explicitly:

* If j=0: s_1 increases by one and u changes by alpha-1.
* If 1 <= j < b-1: s_j decreases by one, s_{j+1} increases by one, and u increases by alpha.
* If j=b-1: s_{b-1} decreases by one and u increases by alpha.

The child threshold is i+1 in the first two cases, and i in the last. This is an exact suffix-count operator, by the arbitrary-budget adjacent-swap bijection in `compaction-proof.md`.

Every transition has m' <= m+1 and preserves u>=1 and 0<=k'<m'. In particular a descending unused choice can occur only when u>=2. Define (Tf)(x)=sum_i f(x_i), x_1=(s_1=1,u=1,k=1), with all other s_j zero. Then

    T^n 1(x_1)=a_{n+1}^(b),
    F(t,x)=sum_{n>=0} T^n 1(x) t^n/n!,
    F(t,x_1)=A_b'(t).

The identity uses nonnegative extended-real series whenever needed.

## 2. Characteristic curve

Use v>=0 as parameter and define

    q=log E_b(v),
    p_j=log E_{b-j}(v), 1<=j<b,
    p_0=q, p_b=0,
    t(v)=integral_0^v log E_b(z)/(E_b(z)-1) dz.

The integrand has value 1 at zero. For b>=2, T_b=t(infinity)<infinity. On 0<=t<T_b these functions satisfy

    q' = e^{p_1}(1-e^{-q})/q,
    p_j' = (e^q-1)e^{p_{j+1}-p_j}/q.

Primes in these identities mean t derivatives, with removable values 1 at t=0. Thus p_j and q are strictly increasing.

Set a=(b-1)/b. Polynomial asymptotics give, as q->infinity,

    p_j = ((b-j)/b)q + c_j + O_b(e^{-q/b}),
    p_{j+1}-p_j = -q/b + O_b(1),
    e^{p_1} ~ c_b e^{a q},
    q' ~ c_b e^{a q}/q,

where c_b=(b!)^a/(b-1)!>0. These estimates and their fixed-order derivatives follow from polynomials in v and q=log E_b(v).

Define weights

    rho_j = p_j'/q' = E_b(v) E_{b-j-1}(v)/(E_{b-1}(v) E_{b-j}(v)), 1<=j<b,
    rho_0=1, rho_b=0.

They obey

    1=rho_0 >= rho_1 >= ... >= rho_{b-1} > rho_b=0.

Indeed E_r(v)^2 >= E_{r-1}(v)E_{r+1}(v): writing d_r=v^r/r!, the difference equals

    d_r [E_r(v) - (v/(r+1))E_{r-1}(v)],

whose bracket has strictly positive coefficients. Therefore E_{r-1}/E_r increases with r, proving the weight ordering. Also rho_j -> (b-j)/b. Consequently, for this fixed b there are constants c>0 and K<infinity such that, for all q>=0 and 0<=j<b,

    c <= rho_j <= 1,    |d rho_j/dq| <= K.

The derivative bound follows from continuity on finite intervals and the convergent rational asymptotics at infinity. We do not need explicit c or K.

## 3. Weighted rank profile and exact child identity

For state x, define

    D = u + sum_j rho_j s_j,
    h(y) = integral_0^y rho_{usage(z)} dz, 0<=y<=m,
    r(y)=h(y)/D,
    r=r(k),
    psi(t,x)=exp(sum_j p_j s_j + q u - q r).

The group usage is constant on each unit rank interval. We have D>=u>=1, c m<=D<=m, 0<=r<=1, psi(0,x)=1, and

    exp(sum_j p_j s_j + qu-q) <= psi(t,x) <= exp(sum_j p_j s_j + qu).

For a choice i in group j, put H=h(i), d_j=rho_j-rho_{j+1} in [0,1], and alpha=1_{i>=k}. Sorting the modified budget only permutes labels below the new last threshold. Therefore the exact child formulas are

    D_i = D-d_j+alpha,
    h_child(k_i) = H+rho_{j+1},
    r_i = (H+rho_{j+1})/(D-d_j+alpha).

They include j=0 and exhausted j=b-1 (rho_b=0). Since the child has u_i>=1, D_i>=1. Together with D_i>=D-1 this gives D_i>=D/2 and hence

    |r_i-r(i)| <= 4/D.                                      (1)

For an ascent, k<=i and the more important one-sided bound is

    r(k)-r_i <= H/D - H/(D+1)
                 <= 1/(D+1) <= 1/2.                         (2)

Here r_i >= H/(D+1), since rho_{j+1}>=0 and D_i<=D+1. This bound is deliberately coarse; b>=3 makes it sufficient.

## 4. Uniform residual

For real y in group j, define

    g(y) = exp(p_{j+1}-p_j + q 1_{y>=k})
           * exp(-q[r(y)-r(k)]).

The exact transition ratio psi(t,x_i)/psi(t,x) is this expression at y=i with r(i) replaced by r_i.

### 4.1 Frozen integral identity

Set lambda=q'D=sum_j p_j' s_j+q'u. Then

    integral_0^m g(y)dy=lambda.                              (3)

To check this, let phi(y)=exp(-q h(y)/D). On group j,

    phi'(y)=-(q rho_j/D)phi(y),
    exp(p_{j+1}-p_j)=q q' rho_j/(e^q-1).

Also phi(0)=1 and phi(m)=e^{-q}. Integrating on [0,k] and [k,m], with the second interval multiplied by e^q, yields exactly q'D phi(k), before division by phi(k). The q=0 case follows by continuity.

### 4.2 Discrete and shifted-rank errors

There is a constant C_b for which every frozen ratio is at most C_b e^{a q}. For ascending choices this follows from r(y)>=r(k); for descending choices it follows from r(k)-r(y)<=1 and p_{j+1}-p_j=-q/b+O_b(1).

On each of at most b+1 intervals cut out by the group boundaries and k, g is decreasing. All boundaries are integers. The error of a left Riemann sum on each such interval is at most its left endpoint value. Thus

    |sum_i g(i)-lambda| <= (b+1) C_b e^{a q}.                (4)

Every exact descending ratio is also at most C_b e^{a q}, since 0<=r_i,r(k)<=1. By (2), every exact ascending ratio is at most C_b e^{(a+1/2)q}. Apply

    |e^z-e^w| <= |z-w| max(e^z,e^w)

and (1), then sum m<=D/c terms. This gives

    |(T psi)/psi - sum_i g(i)|
       <= (4C_b/c)q e^{(a+1/2)q}.                           (5)

### 4.3 Time derivative

The bounded weight derivatives imply |r_q|<=2K/c, uniformly in the state, because |h_q|,|D_q|<=Km. Hence

    (partial_t psi)/psi = lambda-q'[r+q r_q],
    |(partial_t psi)/psi-lambda| <= C_b(1+q)e^{a q}.          (6)

Combining (4)-(6), after enlarging C_b,

    |(partial_t psi)/psi-(T psi)/psi|
       <= C_b(1+q)e^{(a+1/2)q} =: C(q).                     (7)

This estimate is uniform over the entire grouped state space.

## 5. Two-sided comparison without an infinite-state gap

Define

    E(q)=integral_0^q C(z)/q'(z) dz,
    g_-(t,x)=e^{-E(q(t))}psi(t,x),
    g_+(t,x)=e^{ E(q(t))}psi(t,x).

Then partial_t g_- <= T g_-, partial_t g_+ >= T g_+, and both start at 1. Moreover the characteristic estimates give

    E(q)=O_b((1+q)^3 e^{q/2})=o(e^{p_1(q)}),                (8)

because a>1/2 for b>=3.

For completeness, the infinite-state comparison is justified as follows. Let X have each discrete transition at rate 1, so its generator is L=T-mI. Since m increases by at most one per jump, this chain is nonexplosive by comparison with a Yule process. Expanding over jump paths gives the Feynman-Kac identity

    F(t,x)=E_x exp(integral_0^t m(X_s)ds),

with infinity allowed. Stop at the first exit tau_N from m<=N; the stopped region is finite. The supersolution comparison, followed by N->infinity, proves F<=g_+ for t<T_b.

For the lower comparison fix epsilon>0 with t+epsilon<T_b. On the compact interval 0<=v<=t, strict increase of all p_j and q gives an eta>0 and a finite constant C such that, for every state y,

    g_-(v,y)/g_+(v+epsilon,y) <= C exp(-eta m(y)).

Stopped Dynkin comparison bounds g_-(t,x) by the terminal expectation plus the exit expectation with remaining-time g_-. Replace that exit g_- by the displayed bound times the later g_+; supersolution comparison bounds the exit contribution by

    C exp(-eta(N+1))g_+(t+epsilon,x) -> 0.

Thus the lower comparison also holds:

    e^{-E(q)}psi(t,x) <= F(t,x) <= e^{E(q)}psi(t,x),
    0<=t<T_b.                                               (9)

## 6. Exact radius

Let x_N=(s_1=N,u=1,k=N), N>=1. The increasing word 0,1,...,N-1 reaches this state. Its weighted rank is rho_1 N/(rho_1 N+1), so (9) gives, uniformly in N,

    log F(t(q),x_N)=N p_1(q)+O_b(E(q)+q),
    F(t(q),x_N)>=exp(Np_1(q)-E(q)).                         (10)

The positive semigroup identity and the deterministic new-maximum prefix imply, for every delta>0,

    F(t+delta,x_1)
      = sum_{n>=0} delta^n/n! (T^n F(t,.))(x_1)
      >= sum_{n>=0} delta^n/n! F(t,x_{n+1})
      >= exp(p_1(q)-E(q)+delta e^{p_1(q)}).

By (8), this tends to infinity as t increases to T_b. Monotonicity yields F(T_b+delta,x_1)=infinity. Equation (9) proves finiteness for t<T_b. Therefore F(t,x_1), and equivalently A_b(t), has exact radius T_b. In particular

    limsup (a_n^(b)/n!)^(1/n)=1/T_b.

## 7. Upgrade to the full root limit

Write p=p_1, d(q)=(log t(q))_q, and M(q)=p_q(q)/d(q)=t(q)p_t(q). The polynomial characteristic asymptotics and their derivatives give

    p_q -> a,    p_qq -> 0,
    d(q) ~ q e^{-a q}/(c_b T_b),
    d'(q)/d(q) -> -a,
    M(q) ~ a c_b T_b e^{a q}/q.                             (11)

All limits are uniform after q is shifted by a bounded amount.

For c_j=T^j 1(x_N), give J the probability law

    Pr(J=j)=c_j t(q)^j/[j! F(t(q),x_N)].

Let K=NM(q). The growing-state estimate (10) and a two-sided Chernoff argument imply, for sufficiently large q and 0<epsilon<1/2,

    Pr(|J-K|>epsilon K)
       <= 2 exp[-c_b' N epsilon^2+2E(q+1)+O_b(q+1)]         (12)

with c_b'>0 independent of N,q,epsilon. Here is the calculus justification, including the needed uniformity. Set

    H_q(v)=p(q+v)-p(q)-M(q)[log t(q+v)-log t(q)].

For |v|<=1, H_q(0)=H_q'(0)=0, and (11) gives uniformly

    H_q''(v) -> a^2 e^{-a v},
    M(q)d(q+v) -> a e^{-a v}.

Consequently there are constants B,c>0 depending only on b for which

    |H_q(v)|<=B v^2,
    M(q)|log t(q+v)-log t(q)|>=c|v|.

For v=+eta or -eta, choose eta=min(1,c/(2B))*epsilon/2. Comparing the probability generating function at q+eta for the upper tail and q-eta for the lower tail gives a negative term -c_b' N epsilon^2, plus the two errors in (10). This proves (12).

For every sufficiently large integer n, take

    q=(1/2)log n,
    epsilon=(log n)^(-2),
    N=floor((1-4epsilon)n/M(q)).

Then

    N asymp_b n^{1-a/2}log n,
    K=(1-4epsilon)n+O_b(n^{a/2}/log n),
    N epsilon^2 asymp_b n^{1-a/2}/(log n)^3,
    E(q+1)=O_b(n^{1/4}(log n)^3)=o(N epsilon^2).

Since 1/2<a<1, the floor error is o(epsilon n) and N=o(epsilon n). Equation (12) puts probability at least 1/2 in |J-K|<=epsilon K. Some integer j there satisfies

    c_j t(q)^j/j! >= F(t(q),x_N)/(4epsilon K+6).

It follows that

    log c_j >= log(j!)-j log t(q)+Np(q)-E(q)-O_b(log n).

The choices ensure

    (1-6epsilon)n <= j,    N+j <= n.

The increasing prefix reaches x_N in N-1 transitions, so a_{N+j}^(b)>=c_j. Any allowed word can be extended injectively by appending its next new maximum 1+asc(word), repeatedly. Thus a_n^(b)>=a_{N+j}^(b)>=c_j. Finally,

    log(a_n^(b)/n!)
      >= -j log t(q)-log(n!/j!)+Np(q)-E(q)-O_b(log n)
      >= -n log T_b-o(n).

Indeed t(q)->T_b, j/n->1, log(n!/j!)<=6epsilon n log n=o(n), E(q)=o(n), and Np(q)>=0. This proves the matching liminf and the theorem.

## 8. Dependence on the cap

The function f(x)=log x/(x-1) is strictly decreasing for x>1, because 1-1/x-log x<0. Hence T_b strictly decreases with b, and mu_b=1/T_b strictly increases. Since E_b(v) increases pointwise to e^v, domination by the integrable b=2 integrand yields

    T_b decreases to integral_0^infinity v/(e^v-1)dv=pi^2/6,
    mu_b increases to 6/pi^2.

Numerically,

    T_3 = 2.21206776091119219106803...,
    mu_3 = 0.452065717728321870283209...,
    T_4 = 1.871791135820212368029126...,
    mu_4 = 0.5342476416642519661877701....

The finite b theorem does not identify the cap with bounded entries or bounded weights in a Fishburn-matrix model; those statistics need not be preserved by a standard bijection.

## Audit status and sources

The compaction lemma and the three-way finite enumeration are independently supplied. The analytic proof in this file is newly derived and requires an independent audit before being represented as checked. The b=2 analytic proof is separate and is not altered here.

Current OEIS family links: https://oeis.org/A294220 ; https://oeis.org/A202058 ; https://oeis.org/A317784 . Prior b=2 recurrence/compaction: A. R. Conway, M. Conway, A. Elvey Price and A. J. Guttmann, Pattern-Avoiding Ascent Sequences of Length 3, Electronic Journal of Combinatorics 29(4) (2022), P4.25, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/ . The exact general-cap asymptotic theorem above is not claimed to be prior art.
