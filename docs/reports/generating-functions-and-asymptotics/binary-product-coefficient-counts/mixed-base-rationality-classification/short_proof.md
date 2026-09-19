# A compact proof of the mixed-base counterexample

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

## 2. Rationality would force a rational doubling frequency

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

## 3. Exact closed form and further results

For n ≥ 2 the threshold equals \(\lceil(n+1)\log_3 2\rceil\). The only possible
obstruction would be \(3^t=2^{n+1}-1\), which is impossible modulo eight.
Checking n = 0,1 separately yields

\[
a_n=2^{n-\lfloor(n+1)\log_3 2\rfloor}+\boldsymbol1_{\{n=1\}}.
\]

The full article proves a natural boundary and a two-base rationality
classification. Those stronger results are not needed for the counterexample.
The exponent sequence is not monotone; monotonicity is not a hypothesis of
the source question.

Source: https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

See `RESEARCH_STATUS.md` for the literature audit and research-status limits.
