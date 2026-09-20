# A compact proof of the mixed-base counterexample

This note gives a negative answer to the universal rationality part of
Richard Stanley's MathOverflow question 431075, using exactly the stated
hypotheses and adding no monotonicity assumption on the exponents. It
mirrors the merged article: the enumeration is done once (section 1), and
the algebraic obstruction is given twice (sections 2 and 3), because the two
routes reach different conclusions.

Consider Richard Stanley's rationality question (MathOverflow 431075).
Let, for j ≥ 0,

\[
G_{2j+1}=2^j,\qquad G_{2j+2}=3^j.
\]

This is a positive integer sequence tending to infinity, and

\[
\sum_{N\ge1}G_Nt^N=\frac{t}{1-2t^2}+\frac{t^2}{1-3t^2}
\]

is rational. Let ν(N) count the coefficients equal to one in
\(P_N(x)=\prod_{i=1}^N(1+x^{G_i})\), and put \(a_n=\nu(2n)\).
We prove that the generating function of ν is not rational.

## 1. Count coefficients by intervals

Unique binary expansion gives

\[
P_{2n}(x)=(1+x+\cdots+x^{2^n-1})\sum_{s\in S_n}x^s,
\qquad
S_n=\left\{\sum_{j<n}\epsilon_j3^j:\epsilon_j\in\{0,1\}\right\}.
\]

Thus the coefficient of \(x^s\) is the number of intervals
\([u,u+2^n)\), \(u\in S_n\), containing the integer s.

Between consecutive elements of sorted \(S_n\), a carry through t trailing
ones has gap

\[
g_t=3^t-\sum_{j<t}3^j=(3^t+1)/2,
\]

and occurs \(2^{n-1-t}\) times. The first and last gaps are one, and every
nonunit gap is surrounded by unit gaps.

For equal integer-length intervals, an internal interval with neighboring
gaps d and e has exactly

\[
\max(0,\min(d,L)+\min(e,L)-L)
\]

uniquely covered integers. This follows by intersecting it with the region
after its predecessor ends and before its successor starts. The two boundary
intervals each contribute one when their neighboring gaps are one.

Here L ≥ 2 and one of d,e is one. Consequently an internal interval contributes
one exactly when its other gap is at least L. Every such large gap contributes
twice, once on each side. Hence the total is two plus twice the number of gaps
of size at least L.

Let

\[
T(n)=\min\{t\ge0:3^t\ge2^{n+1}-1\}.
\]

For n ≥ 1, \(T(n)\le n\), since \(3^n+1\ge2^{n+1}\).
The number of large gaps is
\(\sum_{t=T(n)}^{n-1}2^{n-1-t}=2^{n-T(n)}-1\), also valid when the sum is empty.
Therefore

\[
a_0=1,\qquad a_n=2^{n-T(n)+1}\quad(n\ge1).
\]

## 2. Rationality would force a rational doubling frequency (route A: mod p)

This is the elementary route. It needs no invertibility and no field
extension, and it proves nonrationality. Route B in section 3 proves more.


The threshold is nondecreasing, and \(T(n+1)-T(n)\in\{0,1\}\) for n ≥ 1:
multiplying \(3^{T(n)}\ge2^{n+1}-1\) by three reaches the next threshold.
Moreover \(T(n)/n\to\log_3 2\). Thus, writing \(e_n=n-T(n)+1\),

\[
a_n=2^{e_n},\qquad e_{n+1}-e_n\in\{0,1\},\qquad
\frac{e_n}{n}\longrightarrow1-\log_3 2.
\]

Suppose \(\sum a_nz^n\) were rational. It would satisfy an eventual linear
recurrence with rational constant coefficients. Choose an odd prime p not
occurring in the denominators of those coefficients. The recurrence modulo p
is a deterministic map on finitely many states, so \(a_n\bmod p\) is eventually
periodic. Every \(a_n\) is nonzero modulo p. Therefore the quotients
\(a_{n+1}/a_n\bmod p\) are eventually periodic too.

But each actual quotient is either one or two, and these are distinct modulo
p. The actual quotient sequence, and hence \(e_{n+1}-e_n\), must therefore be
eventually periodic. Its average would be rational: the number of ones in an
eventual period divided by the period length. This contradicts the irrational
number \(1-\log_3 2\). The latter is irrational because a rational logarithm
would give an equality between positive powers of two and three.

The even section of a rational generating function is rational, so the
nonrationality of \(\sum a_nz^n\) implies the nonrationality of
\(\sum\nu(N)t^N\). This is the required counterexample.

## 3. A second, independent route (route B: normalized states)

The article keeps both routes, because they buy different things. Route A
above is elementary and finite, but reducing a *polynomial*-coefficient
recurrence modulo a prime does not give a finite-state system, so route A
yields nonrationality only. Route B below works over **C**, uses no prime,
and rules out polynomial-coefficient recurrences as well.

Suppose a nonzero sequence \(u_n\) satisfies an eventual constant-coefficient
recurrence of order s with nonzero leading coefficient, and its adjacent
quotients lie in a fixed finite set. The normalized states

\[
W_n=\left(1,\frac{u_{n+1}}{u_n},\ldots,\frac{u_{n+s-1}}{u_n}\right)
\]

form a finite set: each coordinate is a product of at most s members of that
set. The recurrence determines \(u_{n+s}/u_n\) from \(W_n\), and dividing the
shifted coordinates by \(u_{n+1}/u_n\) determines \(W_{n+1}\) from \(W_n\).
So the states follow a deterministic map on a finite set; their trajectory,
and hence the adjacent quotients, are eventually periodic. An order-one
recurrence gives a constant quotient directly.

The polynomial-coefficient case reduces to this one. Suppose
\(\sum_{j\le s}p_j(n)u_{n+j}=0\) eventually. The normalized vectors
\(V_n=(1,u_{n+1}/u_n,\ldots,u_{n+s}/u_n)\) again range over a finite set. For
each attainable v put \(q_v(X)=\sum_j p_j(X)v_j\). A nonzero \(q_v\) has
finitely many integer roots, and there are finitely many v, so past some
\(N_0\) every \(q_{V_n}\) that vanishes at n must vanish identically.
Comparing top-degree coefficients of \(q_{V_n}\equiv0\) gives
\(\sum_j c_j u_{n+j}=0\) with the \(c_j\) the leading coefficients of the
\(p_j\), not all zero. That is a constant-coefficient recurrence, so the
previous paragraph applies.

Now apply this to \(a_n\). Its adjacent quotients are 1 or 2, and

\[
\lim_{n\to\infty}\frac{\log_2a_n}{n}=1-\log_3 2,
\]

which is irrational. If the quotients were eventually periodic, with j
doublings in a period of length p, that limit would be j/p. Contradiction.
So \(a_n\) is neither eventually C-finite nor P-recursive; its generating
function is neither rational nor D-finite.

Finally, arithmetic subsequences inherit both properties. Writing an order-s
recurrence as \(X_{N+1}=M(N)X_N\) with entries rational in N and sampling at
\(N=dn+r\) gives \(Y_{n+1}=B(n)Y_n\) of the same dimension. The first
coordinates of \(Y_n,\ldots,Y_{n+s}\) are s+1 linear forms in s variables over
**C**(n), hence dependent; clearing denominators gives a recurrence for the
sampled sequence. For constant M this is just \(B=M^d\). So non-P-recursiveness
of \(a_n=\nu(2n)\) forces non-P-recursiveness of \(\nu(N)\), and the full
count generating function is not D-finite either.

## 4. Exact closed form and further results

For n ≥ 2 the threshold equals \(\lceil(n+1)\log_3 2\rceil\). The only possible
obstruction would be \(3^t=2^{n+1}-1\), which is impossible modulo eight.
Checking n = 0,1 separately yields

\[
a_n=2^{n-\lfloor(n+1)\log_3 2\rfloor}+\boldsymbol1_{\{n=1\}}.
\]

The full article proves a natural boundary — twice, once directly and once
from a general theorem about \(\sum_n q^{\lfloor n\theta\rfloor}t^n\) for
irrational θ — and a two-base classification in which rationality,
D-finiteness of the even section, D-finiteness of the full series, and
multiplicative dependence of the bases are all equivalent. For binomial
factors this reads: rational exactly when the second base is a power of two,
and not even D-finite otherwise. Those stronger results are not needed for
the counterexample.
The exponent sequence is not monotone; monotonicity is not a hypothesis of
the source question.

Source: https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

See `RESEARCH_STATUS.md` for the literature audit and research-status limits.
