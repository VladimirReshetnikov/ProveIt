# Independent audit of the A202058 full normalized root limit

Audit date: 2026-10-01 (UTC).

## Verdict and scope

PASS: no substantive gap found in `root-limit-proof.md`. Conditional on the
two-sided, all-state barriers in `radius-proof.md`, the addendum proves

    lim (a_n/n!)^(1/n) = 1/T = 8/(3 pi^2),   T = 3 pi^2/8,

and the stated, deliberately coarse two-sided estimate

    log(a_n/n!) + n log T = O(n^(9/13) (log n)^3).

The prerequisite radius/barrier proof was independently certified by
`/root/check_a202058_radius_proof`, for the same radius-proof SHA below. Its
audit is `/workspace/shared/audit-a202058-radius/audit.md`. This audit supplies
independent analytic derivations of the addendum; no finite numerical tests,
asymptotic fits, or extrapolations are used as proof evidence.

This conclusion gives neither a ratio limit nor a prefactor, an asymptotic
equivalent, or an all-orders transseries. The power 9/13 is only an upper
bound on an error scale, not a predicted true correction exponent.

## Sources pinned at audit

- `/workspace/shared/oeis-a202058-research/root-limit-proof.md`
  SHA-256 `14c56e5d26ddc6e6204b782dfb93be231265a43782f1151f854164d7152b0e49`
- `/workspace/shared/oeis-a202058-research/radius-proof.md`
  SHA-256 `51005a5ccb4c7bbfd0fd94139f6fc61e08ceebfbf307f5e98484e7417755c9c4`

The author files were read only and were not modified. To avoid the source's
notational collision, write `L` for the positive transition operator and `T`
for the real constant 3 pi^2/8 throughout this audit.

## 1. Uniformity in the growing state

At x_N=(N,1,N), D=N+R and r=N/(N+R). Hence the prerequisite barriers give
the more explicit statement

    log F(t(q),x_N) = N p(q) + a_N(q) + delta_N(q),
    a_N(q) = q R/(N+R),
    0 <= a_N(q) <= q,   |delta_N(q)| <= E(q).

These inequalities hold simultaneously for all integers N>=1. In particular
no hidden constant is permitted to depend on N, and none does. The defined
E(q) is nonnegative and increasing. Its bound is

    E(q) = O((1+q)^3 exp(q/8)).

## 2. Explicit derivative calculation

Put z=exp(-q), R=2-z, d(q)=t_q(q)/t(q), and M(q)=p_q(q)/d(q). Direct
differentiation gives

    p_q = 1/(2-z),
    p_qq = -z/(2-z)^2,
    t_q = q / [sqrt(2 exp(q)-1) (1-z)],
    d_q/d = 1/q - p_q - z/(1-z) - d.

Since T-t(q)=O(q exp(-q/2)), these imply

    d(q) = q exp(-q/2)/(sqrt(2) T)
           * (1+O(q exp(-q/2))),
    M(q) ~ T exp(q/2)/(sqrt(2) q).

All required bounded-shift limits are uniform, not just pointwise. For
example, for |v|<=1 the following exact factorization proves this directly:

    d(q+v)/d(q)
      = (q+v)/q * exp(-v/2)
        * sqrt[(1-exp(-q)/2)/(1-exp(-(q+v))/2)]
        * (1-exp(-q))/(1-exp(-(q+v)))
        * t(q)/t(q+v).

Every factor other than exp(-v/2) tends uniformly to 1. Consequently

    M(q)d(q+v) -> (1/2)exp(-v/2),
    d_q(q+v)/d(q+v) -> -1/2

uniformly on this interval. For

    H_q(v)=p(q+v)-p(q)-M(q)[log t(q+v)-log t(q)],

one has exactly H_q(0)=H_q'(0)=0, and

    H_q''(v)=p_qq(q+v)-M(q)d_q(q+v)
             -> (1/4)exp(-v/2)

uniformly. In particular there is a single q_0 such that for q>=q_0 and
|v|<=1, both |H_q''(v)|<=1 and M(q)d(q+v)>=1/4 hold: the respective
limiting maximum and minimum are exp(1/2)/4<1 and exp(-1/2)/2>1/4.
Taylor's integral formula gives |H_q(v)|<=v^2/2. Integration of the
second inequality yields the two claimed lower bounds for the absolute
log-time shifts. The threshold q_0 does not depend on N or epsilon.

## 3. Both Chernoff tails, with an explicit error

For c_j=L^j 1(x_N), the series defining F is finite and positive at t(q),
so P(J=j)=c_j t(q)^j/[j! F(t(q),x_N)] is a genuine probability law.
For h=log(t(q+v)/t(q)) its moment generating function is exactly

    E exp(hJ) = F(t(q+v),x_N)/F(t(q),x_N).

Let K=NM(q), 0<epsilon<1/2, eta=epsilon/8. For v=+eta, the upper-tail
Markov bound at the real threshold (1+epsilon)K has log at most

    N H_q(eta) - epsilon N M(q) h + B(q),
    B(q)=2E(q+1)+q+1.

This B is valid without unspecified N-dependent terms: the difference of
the a_N terms is at most q+1, while each delta term is bounded by E(q+1).
Since M(q)h>=eta/4,

    N eta^2/2 - epsilon N eta/4
      = -3N epsilon^2/128.

For v=-eta, h<0. Applying Markov to exp(hJ) for
J<(1-epsilon)K gives N H_q(-eta)+epsilon N M(q)h+B(q), which has exactly
the same bound. Thus

    P(|J-K|>epsilon K)
      <= 2 exp[-3N epsilon^2/128+2E(q+1)+q+1].

There is no integer-rounding loss at this step: Markov's inequality works
at real thresholds. The estimate is uniform even for very small positive
epsilon (when the right side might be uninformative but remains valid).

## 4. Coefficient extraction and exact index accounting

For q=log n and epsilon=(log n)^(-2), define

    N=floor((1-4epsilon)n/M(q)),   K=NM(q).

All subsequent statements hold for sufficiently large n, so epsilon<1/4
and N>=1. Write the floor loss explicitly as

    K=(1-4epsilon)n-theta M(q),   0<=theta<1.

The asymptotic scales are

    M(q) ~ (T/sqrt(2)) sqrt(n)/log n,
    N ~ (sqrt(2)/T) sqrt(n) log n,
    N epsilon^2 ~ (sqrt(2)/T) sqrt(n)/(log n)^3,
    E(q+1)=O(n^(1/8)(log n)^3).

Therefore E(q+1)+q+1=o(N epsilon^2), and the central closed interval
|j-K|<=epsilon K has mass at least 1/2. There are at most 2epsilon K+1
integers in it, so some integer j satisfies the (weaker, hence safe) source
bound

    c_j t(q)^j/j! >= F(t(q),x_N)/(4epsilon K+6).

Using a_N(q)>=0 and the lower barrier, this proves

    log c_j >= log(j!)-j log t(q)+Np(q)-E(q)
               -log(4epsilon K+6).

The last logarithm is O(log n). The inequalities needed to transfer this
coefficient to a_n hold at every sufficiently large n:

    j >= (1-epsilon)[(1-4epsilon)n-M(q)]
       >= (1-6epsilon)n,

since M(q)=o(epsilon n), and

    j <= (1+epsilon)(1-4epsilon)n
       = (1-3epsilon-4epsilon^2)n.

Since N=o(epsilon n), the latter yields N+j<=n.

The prefix index is correct: the initial state x_0=(1,1,1) is x_1 in the
growing-state notation. From x_r=(r,1,r), choosing i=r is an N-ascent and
reaches x_(r+1). Exactly N-1 transitions reach x_N. Therefore

    a_(N+j)=L^(N+j-1)1(x_0) >= L^j 1(x_N)=c_j.

There is no missing or extra factor of n or factorial in this unnormalized
counting comparison.

For padding, every ascent sequence satisfies max(label)<=number of
ascents. This follows inductively: a label that exceeds the previous
maximum necessarily creates an ascent, and the allowed new label is at
most one plus the previous number of ascents. Appending that latter value
is thus allowed and is a fresh label. It preserves 000-avoidance and
determines an injective extension (the old sequence is a recoverable
prefix). Iteration proves a_n>=a_(N+j)>=c_j.

## 5. Normalization and full root limit

The normalization must pay n!/j!, rather than (N+j)!/j! alone, because the
final length is n. The source does pay the full required loss:

    log(n!/j!) <= (n-j)log n <= 6epsilon n log n = o(n).

An even simpler sign-safe bound than the source's limiting argument is
available: because 0<t(q)<=T, T>1, and 0<=j<=n, one has t(q)^j<=T^n,
hence

    -j log t(q) >= -n log T.

Dropping the nonnegative Np term gives the explicit lower bound

    log(a_n/n!)+n log T
      >= -6epsilon n log n-E(q)-O(log n)= -o(n).

This is valid for every sufficiently large integer n, not a subsequence.
The prerequisite radius theorem supplies the reverse limsup through the
power-series radius formula. Thus the full normalized root limit exists
and has the asserted value.

## 6. Quantitative choice and two-sided error

For q=(8/13)log n and epsilon=n^(-4/13)(log n)^2, the precise leading
scales are

    M(q) ~ (13T/(8sqrt(2))) n^(4/13)/log n,
    N ~ (8sqrt(2)/(13T)) n^(9/13) log n,
    N epsilon^2 ~ (8sqrt(2)/(13T)) n^(1/13)(log n)^5,
    E(q+1)=O(n^(1/13)(log n)^3).

Thus E(q+1)+q+1=o(N epsilon^2). Moreover

    N/(epsilon n)=O(1/log n) -> 0,
    M(q)/(epsilon n)=O(n^(-5/13)/(log n)^3) -> 0.

All concentration, floor, coefficient, prefix, and padding arguments
therefore remain applicable. The same sign-safe inequality gives

    log(a_n/n!)+n log T
      >= -O(epsilon n log n+E(q)+log n)
      = -O(n^(9/13)(log n)^3).

For the opposite side, positivity of the root series gives

    a_n/n! <= A(t(q))/t(q)^n.

The identity A(t)=1+integral_0^t F(v,x_0)dv and positivity of the
coefficients imply A(t)<=1+tF(t,x_0). At x_0,

    log psi(t(q),x_0)=p(q)+qR/(1+R)=O(q+1),

so the superbarrier and t(q)<=T give log A(t(q))<=E(q)+O(q+1).
Finally T-t(q)=O(q exp(-q/2)) implies

    log(T/t(q))=O(q exp(-q/2)),

since t(q) stays bounded away from zero for large q. Consequently

    log(a_n/n!)+n log T
      <= O(E(q)+q+1+nq exp(-q/2))
      = O(n^(9/13)log n).

Together these are stronger on the upper side than, and imply, the
advertised absolute O(n^(9/13)(log n)^3) estimate.

## Audit disposition

No correction is required for the asserted theorem or quantitative error.
Optional editorial improvements are to distinguish the transition operator
from T, display the exact d_q/d identity, and use t(q)^j<=T^n to simplify
the normalization step. These are clarifications, not repairs.
