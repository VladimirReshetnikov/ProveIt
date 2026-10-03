# Independent audit: bounded label multiplicity, every fixed cap b >= 3

Audit date: 1 October 2026.

## Verdict and scope

I independently checked the combinatorial reduction and the analytic argument in `compaction-proof.md` and `general-cap-proof.md`. I found no mathematical gap requiring a repair. In particular, the proposed argument establishes, for every fixed integer b >= 3,

    lim_n (a_n^(b)/n!)^(1/n) = 1/T_b,
    T_b = integral_0^infinity log E_b(v)/(E_b(v)-1) dv.

This verdict is based on the arguments below, not on finite enumeration or numerical residual tests. I inspected the independent raw/grouped/direct enumeration script as a consistency check; no computation is needed for the proof audit.

The audited proof does **not** establish an asymptotic equivalent, a ratio limit, or a uniform-in-b theorem. Its b=2 assertion refers to a separate proof, which I have not audited here. I have not independently verified the historical attribution, OEIS labels, decimal evaluations, or novelty claim. Those are separate from the theorem proved for b >= 3.

The versions read had these SHA-256 hashes:

- `general-cap-proof.md`: bcedcb0759c73f8aba6472f0be109d20083fae12dfc5db0cd3d1b633f75570a1
- `compaction-proof.md`: 774969038da3b3ad438adaf206b9488f0aedf0a8b16be59d5ed5132d446d17c2

## 1. Raw states and the interchange involution

The raw state really is sufficient. For an ascent sequence, induction gives

    max(prefix) <= asc(prefix).

Indeed a new maximum creates an ascent and is at most one plus the previous ascent count; a nonascent cannot increase the maximum. Thus the current top admissible label, 1+asc(prefix), is unused and strictly above the last value. Every ascent makes exactly one further top label available. Exhausted labels never return. The number of active labels at or below the last value therefore records exactly which active choices are ascents, including when the last label is exhausted.

The adjacent-budget involution is valid for arbitrary positive budgets, rather than only neighboring budget values. Reverse each maximal binary block and complement its two labels. Applying this twice restores the word, exchanges the total usages of those labels, and preserves the number of internal block ascents. Since every prefix usage is bounded by total usage, exchanging the total quotas also enforces every intermediate quota.

There are two possible legality hazards, and the proof handles both:

1. No outside suffix letter lies strictly between the two initially adjacent active labels: any omitted intermediate labels are already exhausted, and all new labels are above the initial active set. Consequently every entry/exit comparison with an outside letter is invariant.
2. The initial boundary comparison is invariant because both labels are at or below the original last value. Cumulative ascent counts agree after each transformed block and before every unchanged outside letter. Although ascent timing can change inside a block, the two block labels were already admissible initially, and the admissible upper bound never decreases.

This supplies a genuine involution on legal suffixes. The scope restriction to swaps below the last boundary is essential and is respected by canonical compaction.

After decrementing an entry of remaining budget r>1 in a sorted tuple, the only possible disorder is with preceding entries of budget r. The selected entry need only move to the start of its old r-group. Every swap is wholly within ranks 0 through i, which are the first i+1 entries under the new boundary. The boundary stays i+1 during this rearrangement. When the entry is exhausted, removal leaves the tuple sorted and gives boundary i. Thus the grouped operator is exactly suffix-count preserving. No claim that arbitrary raw tuples can be globally sorted is used.

## 2. Characteristic equations and weights

Differentiating t(v), q(v), and p_j(v) directly gives the displayed characteristic equations. All apparent quotients at v=q=0 have removable singularities, and all time derivatives there equal 1.

The polynomial identity used to order the weights is correct:

    E_r^2 - E_(r-1) E_(r+1)
      = (v^r/r!) [E_r - v E_(r-1)/(r+1)].

For powers v^k, 1<=k<=r, the bracket coefficient is

    (r+1-k)/((r+1) k!) > 0,

and the constant coefficient is 1. It follows that E_(r-1)/E_r increases with r. Hence

    1=rho_0 >= rho_1 >= ... >= rho_(b-1) > rho_b=0.

The limits rho_j -> (b-j)/b and their bounded q-derivatives follow from rational functions of v and q_v=E_(b-1)/E_b. Positivity, continuity, and the positive limits at infinity yield a fixed-b lower bound c>0 for every nonzero group weight. This bound need not be uniform in b.

For large q, v is a constant times exp(q/b), with relative error O(exp(-q/b)). Therefore

    p_1 = a q + O_b(1),
    p_(j+1)-p_j = -q/b + O_b(1),
    q_t ~ c_b exp(aq)/q,
    a=(b-1)/b.

The stated differentiated asymptotics are justified by the same rational expansions; they do not require differentiation of an arbitrary unstructured error term.

## 3. Exact child rank and the one-sided ascent estimate

For an old choice of rank i and group j, put H=h(i). Before sorting, the new prefix below its boundary consists of all old lower ranks and the selected label with weight rho_(j+1), unless that label has exhausted. The new top label, when present, is outside this prefix. All compaction swaps stay inside it. Consequently the identities

    D_i = D - rho_j + rho_(j+1) + alpha,
    h_child(k_i) = H + rho_(j+1)

are exact, including unused-label choices, saturation, and virtual last boundaries.

Writing d_j=rho_j-rho_(j+1), one has 0<=d_j<=1. Because the child still has an unused label, D_i>=1; also D_i>=D-1. Thus D_i>=D/2 for all D>=1. Direct subtraction gives

    |r_i-H/D|
      <= rho_(j+1)/D_i + (H/D)|d_j-alpha|/D_i
      <= 2/D_i <= 4/D.

For an ascent, i>=k and D_i<=D+1, so

    r(k)-r_i
      <= H/D-H/(D+1)
      <= 1/(D+1) <= 1/2.

No assumption that the chosen budget remains at its old rank occurs here. Confusing budget rank with the fixed boundary would break this argument, but the proof makes the required distinction.

## 4. Frozen integral and uniform residual

Let phi(y)=exp(-q h(y)/D). The identity

    exp(p_(j+1)-p_j) = q q_t rho_j/(exp(q)-1)

holds also for the unused group j=0. Since phi_y=-(q rho_j/D)phi within each group, the two integrals before dividing by phi(k) are

    q_t D/(exp(q)-1) [1-phi(k)]

and

    q_t D exp(q)/(exp(q)-1) [phi(k)-exp(-q)].

Their sum is exactly q_t D phi(k). This verifies the frozen integral identity, including arbitrary locations of k among or inside groups. The q=0 identity follows by continuity.

All frozen ratios are bounded by C_b exp(aq): for ascents use r(y)>=r(k), and for descents use r(k)-r(y)<=1. Every interval endpoint used for splitting into groups and at k is an integer. Within an interval the ratio is decreasing, so its left-sum error is between zero and its left endpoint value. There are at most b+1 intervals, giving a state-independent error.

Exact descending ratios obey the same bound. Exact ascending ratios obey C_b exp((a+1/2)q) by the preceding one-sided rank inequality. The exponential difference inequality, multiplied by q|r_i-r(i)|, and the relation m/D<=1/c therefore give

    |(T psi)/psi - sum_i g(i)|
       <= C_b q exp((a+1/2)q).

The time derivative is also uniform in the state. Since |h_q| and |D_q| are at most Km and 0<=h<=D,

    |r_q| <= 2Km/D <= 2K/c.

Differentiating log psi then gives

    (log psi)_t = q_t D - q_t(r+q r_q).

Combining these bounds proves the claimed uniform residual

    |psi_t/psi - Tpsi/psi|
      <= C_b (1+q) exp((a+1/2)q).

This is an absolute residual estimate relative to psi, uniform even for very small D and arbitrarily large populations. No large-state approximation is hidden in it.

The integrated correction satisfies, even with the proof's generous polynomial factor,

    E(q)=O_b((1+q)^3 exp(q/2)).

For b>=3, a>1/2, so E(q)=o(exp(p_1(q))). This is the precise strict inequality that makes this proof work for b>=3 and prevents its direct use for b=2.

## 5. Infinite-state comparison, expanded

The continuous-time chain with one rate-1 edge per rank choice has total jump rate m and generator L=T-mI. Along any path, the population after j jumps is at most m(initial)+j. The holding times therefore dominate those of a linear pure-birth chain. The latter is nonexplosive, so this chain is nonexplosive too.

Expanding according to finite jump paths cancels each holding-time survival factor against exp(integral m). Integrating jump times over the simplex gives t^n/n!, hence the extended-real identity

    F(t,x) = E_x exp(integral_0^t m(X_s) ds).

For each N, the set of admissible states with m<=N is finite. Stop on first exit at tau_N. If Y_s=exp(integral_0^s m(X_r)dr), applying the finite stopped Dynkin formula to

    Y_s g_+(t-s,X_s)

uses drift T g_+ - (g_+)_t <=0. Positivity allows the boundary term to be discarded, and nonexplosion gives F(t,x)<=g_+(t,x) on letting N increase.

The lower bound needs more than positivity, and the proof supplies it correctly. Fix epsilon>0 with t+epsilon<T_b. On the compact time interval 0<=v<=t, all increments

    p_j(v+epsilon)-p_j(v), q(v+epsilon)-q(v)

have a common positive lower bound eta. The rank correction in the log ratio is bounded above by q(t+epsilon), and the E corrections have favorable signs. Consequently

    g_-(v,y) <= C exp(-eta m(y)) g_+(v+epsilon,y)

uniformly in y and v. The constant C may depend on the fixed t and epsilon, which is harmless.

The stopped subsolution inequality gives

    g_-(t,x)
      <= E[Y_t ; tau_N>t]
         + E[Y_tau_N g_-(t-tau_N,X_tau_N); tau_N<=t].

Every upward jump changes m by at most one. Starting inside m<=N, an exit therefore has m(X_tau_N)=N+1. The boundary term is at most

    C exp(-eta(N+1))
      E[Y_tau_N g_+(t+epsilon-tau_N,X_tau_N); tau_N<=t]
    <= C exp(-eta(N+1)) g_+(t+epsilon,x).

The last inequality is the already valid stopped supersolution comparison with horizon t+epsilon. The expression tends to zero, while the first expectation increases to F(t,x). This proves g_-<=F. There is no reliance on an unproved uniqueness theorem for an infinite ODE system, and no uniform-integrability assumption is being silently imposed.

## 6. Exact radius

For the increasing-prefix state x_N, the rank correction is particularly explicit:

    log psi(t,x_N) = N p_1(q) + q/(rho_1(q)N+1).

Thus log F(t,x_N)=N p_1(q)+O_b(E(q)+q), with constants independent of N, and F(t,x_N)>=exp(Np_1-E).

The positive semigroup identity used in the proof holds as an identity of nonnegative extended-real sums, by the binomial formula and Tonelli. A repeated new-maximum path reaches x_(n+1) in n transitions from x_1. Therefore

    F(t+delta,x_1)
      >= exp(p_1(q)-E(q)+delta exp(p_1(q))).

For each fixed delta>0 this diverges as q increases to infinity, because E=o(exp(p_1)). Monotonicity then forces F(T_b+delta,x_1)=infinity. Together with the comparison's finiteness for t<T_b, this proves the exact radius. Differentiation of an EGF preserves its radius, so passing between F(t,x_1)=A_b'(t) and A_b is valid.

This part alone establishes only a limsup. The next section is necessary for the full asserted limit.

## 7. Uniform Chernoff estimate and extraction for every n

There is no unjustified differentiation of log F in the concentration argument. Its center K=N M(q) is a chosen deterministic comparison center, not an asserted exact mean. Only the already uniform values

    log F(t(q),x_N) = N p(q) + O_b(E(q)+q)

are used at q and q+v.

Writing d=(log t)_q and M=p_q/d, direct differentiation of the characteristic asymptotics gives, uniformly for |v|<=1,

    M(q)d(q+v) -> a exp(-av),
    d'(q+v)/d(q+v) -> -a,
    p_qq(q+v) -> 0.

Hence

    H_q''(v)=p_qq(q+v)-M(q)d'(q+v)
       -> a^2 exp(-av).

Since H_q(0)=H_q'(0)=0, it follows that |H_q(v)|<=Bv^2, and the positive lower bound on M(q)d(q+v) gives

    M(q)|log t(q+v)-log t(q)| >= c|v|.

Both bounds hold for all sufficiently large q, uniformly for the entire interval |v|<=1. They remain valid when v shrinks with epsilon; convergence is not used pointwise at an uncontrolled moving argument.

For upper and lower tails, the exponential Markov bound therefore has a main exponent at most

    N [B eta^2 - c epsilon eta],

using v=eta and v=-eta respectively. With the proof's eta proportional to epsilon, this is at most -c'_b N epsilon^2. The errors from the two values of F are bounded by 2E(q+1)+O_b(q+1), independently of N and epsilon. Thus the displayed two-sided Chernoff estimate is justified.

For q=(log n)/2, epsilon=(log n)^(-2), and the specified integer N,

    M(q) asymp_b n^(a/2)/log n,
    N asymp_b n^(1-a/2) log n,
    N epsilon^2 asymp_b n^(1-a/2)/(log n)^3,
    E(q+1)=O_b(n^(1/4)(log n)^3).

Because a<1, N epsilon^2 dominates the error. Moreover both N and M(q), the maximum floor loss in K, are o(epsilon n). Thus with probability at least 1/2 one has |J-K|<=epsilon K, and that interval contains only O(epsilon K+1) integers. Extracting a single coefficient gives exactly the lower estimate claimed in the proof.

The buffer is sufficient in both directions. For all large n, such an extracted j satisfies

    j >= (1-6epsilon)n,
    N+j <= n.

The increasing prefix realizes x_N as an actual state, so c_j counts legitimate extensions and a_(N+j)>=c_j. Appending 1+asc(word) is a new maximum by max(word)<=asc(word), respects the cap, and provides an injective extension to length n. Therefore a_n>=c_j.

Finally,

    log(n!/j!) <= (n-j)log n <= 6epsilon n log n=o(n),
    -j log t(q)=-n log T_b+o(n),
    E(q)=o(n).

Dropping the favorable nonnegative term Np(q) gives the asserted liminf. Combined with the exact-radius limsup, this proves the full root limit for every n, not merely a subsequence.

## 8. Cap dependence and presentation notes

For x>1, log(x)/(x-1) has strictly negative derivative. Since E_(b+1)(v)>E_b(v) for every v>0, the integral T_b strictly decreases. The b=2 integrand is integrable: it tends to 1 near zero and is O(log(v)/v^2) at infinity. It dominates all b>=2 integrands. Dominated convergence therefore yields

    T_b -> integral_0^infinity v/(exp(v)-1)dv = pi^2/6.

The last equality follows by the nonnegative exponential series and the sum of 1/k^2. These dependence statements are consistent with, and follow independently from, the fixed-cap proof.

No correction is required for the theorem. For a standalone polished version, useful optional clarifications would be:

- State max(word)<=asc(word) explicitly before the new-maximum extension argument
- Expand the stopped lower comparison with its boundary expectation, as above
- Explain that the Chernoff center need not be the exact mean and that no derivative of the barrier error is taken
- Keep the separate b=2 proof, numerical values, and bibliographic verification clearly distinct from the audited b>=3 result

These are exposition improvements, not unresolved assumptions.
