# A binary/ternary counterexample

This note gives a negative answer to the universal rationality part of
Richard Stanley's MathOverflow question 431075. It uses exactly the stated
hypotheses, without adding a monotonicity assumption on the exponents.

Let

\[
G_{2j+1}=2^j,\qquad G_{2j+2}=3^j\quad(j\ge0).
\]

These positive integers tend to infinity, and

\[
\sum_{i\ge1}G_i z^i=\frac{z}{1-2z^2}+\frac{z^2}{1-3z^2}.
\]

Let \(\nu(N)\) count the coefficients equal to one in
\(P_N(x)=\prod_{i=1}^N(1+x^{G_i})\), and put \(a_n=\nu(2n)\).
We will prove

\[
a_0=1,\quad a_1=2,\quad
 a_n=2^{\lfloor(n+1)(1-\log_3 2)\rfloor}\quad(n\ge2)
\]

and show that this sequence cannot have a rational generating function.

## Exact enumeration

Binary expansion gives

\[
P_{2n}(x)=(1+x+\cdots+x^{2^n-1})
          \sum_{s\in S_n}x^s,
\qquad
S_n=\left\{\sum_{j=0}^{n-1}\epsilon_j3^j:
\epsilon_j\in\{0,1\}\right\}.
\]

Thus coefficients count coverage by the integer intervals
\([s,s+2^n-1]\), \(s\in S_n\). Order the starts as
\(s_0<s_1<\cdots<s_{2^n-1}\). Their successive gaps are

\[
s_i-s_{i-1}=\frac{3^{v_2(i)}+1}{2}.
\]

Indeed, incrementing the binary index replaces \(r=v_2(i)\) trailing ones
by zeros and the next zero by one, so the corresponding base-three value
increases by \(3^r-(1+3+\cdots+3^{r-1})=(3^r+1)/2\). The gap
\((3^r+1)/2\) occurs \(2^{n-r-1}\) times.

Every interior start has a neighboring gap of one. For equal-length
intervals of length \(M\), an interior interval with neighboring gaps
\(d,e\) contributes

\[
\max(0,\min(M,d)+\min(M,e)-M)
\]

positions covered only by it. When one gap is one and \(M\ge2\), this
contribution equals one precisely when the other gap is at least \(M\).
The two end intervals always contribute one each. Therefore

\[
a_n=2+2\sum_{r=0}^{n-1}2^{n-r-1}
       \mathbf1_{\{(3^r+1)/2\ge2^n\}}.
\]

Let \(r_n\) be the least \(r\) for which \(3^r\ge2^{n+1}-1\).
Since \((3^n+1)/2\ge2^n\), we have \(r_n\le n\), and summing the geometric
series gives

\[
a_n=2^{n-r_n+1}\qquad(n\ge1).
\]

For \(n\ge2\), equality \(3^r=2^{n+1}-1\) is impossible modulo eight:
powers of three are 1 or 3 modulo eight, whereas the right side is 7.
Consequently

\[
r_n=\lceil(n+1)\log_3 2\rceil,
\]

which proves the claimed floor formula. The values at 0 and 1 follow
directly from the empty product and \((1+x)^2\).

## Why the generating function is not rational

We use an elementary observation. Suppose a nonzero sequence \(u_n\)
satisfies an eventual constant-coefficient recurrence of order \(s\), and
its adjacent quotients lie in a fixed finite set. The normalized states

\[
\left(1,\frac{u_{n+1}}{u_n},\ldots,
           \frac{u_{n+s-1}}{u_n}\right)
\]

form a finite set. The recurrence determines the next normalized state
from the current one. Hence those states, and therefore the adjacent
quotients, are eventually periodic. An order-one recurrence gives a
constant quotient directly.

Now put \(\delta=1-\log_3 2\). This number is irrational, since a rational
value of \(\log_3 2\) would equate a positive power of three with a positive
power of two. Our formula shows that the adjacent quotients of \(a_n\)
are 1 or 2 and that

\[
\lim_{n\to\infty}\frac{\log_2a_n}{n}=\delta.
\]

If the quotients were eventually periodic, with \(q\) doublings in a
period of length \(p\), this limit would be \(q/p\), a contradiction.
Therefore \(a_n\) is not eventually C-finite, so its ordinary generating
function is not rational.

Finally, arithmetic subsequences of C-finite sequences are C-finite:
sampling a matrix representation \(u_n=vM^nw\) every second term replaces
\(M\) by \(M^2\). Thus rationality of the full count generating function
would imply rationality for its even subsequence \(a_n\). This contradiction
settles the universal rationality claim negatively.

## Stronger results in the full article

The same normalized-state argument, preceded by a finite-polynomial-root
argument, rules out polynomial-coefficient recurrences as well. The full
article proves non-P-recursiveness, a natural boundary, and the exact
classification for exponents interleaving powers of two and an integer
\(b\ge3\): rationality holds exactly when \(b\) is a power of two.

The example is not monotone (9 is followed by 8). The stated question does
not require monotonicity; a version with that additional hypothesis is
not answered by this construction. Historical priority and independent
referee verification are not claimed.
