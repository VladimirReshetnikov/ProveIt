# A022629: an elementary proof of the logarithmic asymptotic and its inverse

Research note, 1 October 2026. Complete ordinary proof submitted for independent review. The current OEIS entry credits the displayed asymptotic conjecture to Václav Kotešovec (8 May 2018). No literature-wide novelty claim is made.

Let a_n=[q^n]∏_{k≥1}(1+kq^k), with a_0=1. All logarithms below are natural. Then, as n→∞,

log a_n = √(2n)(log√(2n)−1)+O(√n/log n).

In particular, this proves the OEIS conjecture and retains its second, order-√n term with a smaller error. For y>1 let N(y)=min{n≥0:a_n≥y}, and put s=log y. Then

N(y)= 1/2 [s/W(s/e)]² {1+O((log s)^(−2))},

where W is the positive real Lambert function. The same formula holds for the ordinary inverse of the strictly increasing piecewise-linear interpolation of log a_n on n≥1.

## 1. Lower bound

Let M be the largest integer with T_M=M(M+1)/2≤n, and r=n−T_M. The distinct partition

1,2,…,M−1,M+r

has weight (M−1)!(M+r)≥M!. Thus log a_n≥log M!. Writing m=√(2n), we have M=m+O(1). The integral estimates for log M! give

log a_n ≥ m(log m−1)−O(log m).

This also covers r=0 without repeated parts.

## 2. Coefficient upper bound

Set L=log m and t=L/m. Positivity of all coefficients gives

log a_n≤nt+f(t),  f(t)=Σ_{k≥1}log(1+k e^(−tk)).

For g(x)=log x−tx and K=floor m, the exact soft-cutoff identity gives

f(t)=Σ_{k=1}^K g(k)+R,

where R≥0 and R=O(m/L). The k=1 term is negative but its correction is bounded: log(1+e^(g(1)))−g(1)=log(1+e^t)=O(1). For all sufficiently large m, g(k)≥0 for 2≤k≤K, since g is concave, g(2)>0 and g(m)=0.

Here are elementary bounds proving the stated remainder. On 2≤k≤m/2,

log(1+e^(−g(k)))≤e^(−g(k))=e^(tk)/k≤√m/k,

so their total is O(√m log m)=O(m/L). On m/2<k≤m, write x=k/m. Since log x≥−2(1−x),

g(k)=L(1−x)+log x≥(L−2)(1−x).

The resulting geometric series is O(m/L). For k>m,

log(1+e^(g(k)))≤(k/m)exp(−L(k−m)/m),

whose sum is also O(m/L) by the elementary geometric-series formulas. Endpoints or empty subranges only change the absolute constants.

Finally,

nt+Σ_{k=1}^K g(k)
= log K! + t(n−K(K+1)/2)
= m(log m−1)+O(L),

because n=m²/2, K=m+O(1), and Stirling's elementary integral bounds suffice. This proves the asserted upper bound. Together with Section 1 it proves the theorem.

## 3. Monotonicity and discrete inversion

View a_n as counting distinct-size partitions in which a part k receives one of k colors. Increase the largest part by one, preserving its color and all other parts. This is an injection from the objects counted by a_n into those counted by a_(n+1): the largest part remains distinct, and the inverse on the image decreases it by one. For n≥1 the one-part object of size n+1 and color n+1 is outside the image. Hence a_(n+1)>a_n for n≥1, while a_0=a_1=1.

Write H(m)=m(log m−1). For s→∞ its positive solution H(m_0)=s is exactly

m_0=s/W(s/e).

The proved estimate is log a_n=H(√(2n))+O(√n/log n). For any sufficiently large fixed C, evaluating at the integers immediately surrounding

n_±=m_0²/2 · [1±C/(log m_0)²]

puts log a_(floor n_−)<s<log a_(ceil n_+). Indeed H'(m)=log m, so the main perturbation has magnitude comparable to C m_0/log m_0, and dominates the bounded remainder; rounding changes the main term by O(log m_0/m_0). Monotonicity traps N(y) between these bounds. Since log m_0~log s, this yields the stated inverse error. The same trapping proof applies to the increasing interpolation.

## Sources and scope

- OEIS A022629, https://oeis.org/A022629, accessed 1 October 2026: defining product, colored-partition interpretation and Kotešovec's conjecture.
- A separate current literature check located Naranjo–Ramírez, “On colored partitions and Euler-type identities,” INTEGERS 26 (2026), A20, https://math.colgate.edu/~integers/aa20/aa20.pdf; its discussion identifies this sequence, while no asymptotic proof was located in that paper by the screening worker. This note does not rely on that negative search claim.

This proof establishes a logarithmic two-term asymptotic and a rigorous inverse estimate. It does not yet establish a relative asymptotic for a_n, an all-orders expansion, or an exponentially complete transseries.
