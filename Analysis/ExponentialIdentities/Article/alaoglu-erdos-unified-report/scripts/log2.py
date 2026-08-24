p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
old = r"""\subsection{Integer-valued exponential polynomials on the solution semigroup (dead end)}"""
assert t.count(old) == 1
new = r"""\subsection{Column divisibility in interpolation determinants (dead end, quantified)}
\label{log:determinant-column}

The structural-prime gain of Section~\ref{log:structural-relaxation} is additive over
points, so it is natural to put it into an interpolation determinant, where the arithmetic
side is a \emph{sum} over columns.  Take $L=N^2$ functions $2^{az}3^{bz}$ ($1\le a\le N$,
$0\le b<N$) and the $L$ points $z_{n,k}$, $0\le n,k<N$.  The determinant
$\Delta=\det\bigl(2^{az_{n,k}}3^{bz_{n,k}}\bigr)$ is a rational integer; the column of
$z_{n,k}$ is divisible by $r^{ek}$, hence
\[
 v_r(\Delta)\ \ge\ e\sum_{n,k<N}k\ =\ \tfrac{e}{2}N^3(1+o(1)),
\]
a \emph{cubic} lower bound for the arithmetic size of a nonzero $\Delta$.  The archimedean
side (Laurent's lemma, with the points in a disc of radius $\rho=(1+\beta)N$ and the
functions bounded on $|z|=R=e\rho$ by $6^{NR}$) gives
$\log|\Delta|\le-\tfrac12L^2+L\cdot NR\log6=\bigl(e(1+\beta)\log6-\tfrac12\bigr)N^4$.
The right side is positive, i.e.\ the archimedean bound is already useless before the cubic
$r$-adic term is subtracted; and even if the archimedean constant could be made negative, a
cubic gain cannot compensate a quartic deficit.  Summing valuations over columns turns a
linear gain per point into a cubic total, one degree short of the quartic scale of the
determinant.  \emph{Dead end.}  A quadratic gain \emph{per point} would be needed
(Section~\ref{log:directions}, item~3).

\subsection{Integer-valued exponential polynomials on the solution semigroup (dead end)}"""
t = t.replace(old, new)
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
