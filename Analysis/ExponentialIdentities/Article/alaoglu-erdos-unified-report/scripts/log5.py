p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
old = r"""\subsection{The LP layer of the linear-width factorial target is empty for the control
(computed)}"""
assert t.count(old) == 1
new = r"""\subsection{The terminal factorials are multiplicatively independent (proved)}
\label{log:factorial-independence}

Analyzing the exact-unit case of the factorial target yields a clean unconditional
statement.  Let $1<M<A$ with $A^{7/12}<M^{1-\varepsilon_0}$ --- satisfied by every
mesoscopic pair, where $M=A^{\alpha}$ with $\alpha=\log2/\log3=0.6309\ldots$ --- and
$F_t=(A^t)!/(A^t-M^t)!$.

\begin{proposition}[Multiplicative independence of the terminal factorials]
\label{log:prop-factorial-independence}
There is $n_0=n_0(M,A)$ such that the integers $F_{n_0},F_{n_0+1},F_{n_0+2},\ldots$ are
multiplicatively independent: $\prod_jF_{n+j}^{c_j}=1$ with integer exponents forces every
$c_j=0$.  Consequently $\mathcal F_{P,n}=1$ is impossible for a nonzero $P\in\Z[T]$ once
$n\ge n_0$.
\end{proposition}

\begin{proof}
The interval $(A^t-M^t,A^t]$ has length $X^{\alpha}$ with $X=A^t$ and
$\alpha>0.525$, so for $X$ large it contains a prime $p_t$ (Baker--Harman--Pintz
\cite{BakerHarmanPintz2001}); fix such a prime for each $t\ge n_0$.  Suppose
$\prod_jF_{n+j}^{c_j}=1$ with not all $c_j=0$, and let $j^*$ be the \emph{largest} index
with $c_{j^*}\ne0$.  The prime $p_{n+j^*}$ divides $F_{n+j^*}$ exactly once, divides no
$F_{n+j}$ with $j<j^*$ (it exceeds $A^{n+j}$), and the levels above $j^*$ carry zero
exponent.  Taking $v_{p_{n+j^*}}$ of the relation gives $c_{j^*}=0$, a contradiction.
\end{proof}

\statusnew{}, with the short-interval prime existence \statusknown{}.  (Bertrand's postulate
does not suffice: the window has sublinear length.  Huxley's asymptotic used in
Theorem~\ref{fc:thm-window} is stronger than needed here; existence at exponent
$0.525$ is enough.)  The proposition removes the exact-unit branch of
Target~\ref{fc:target-linear} in full generality: a factorial cocycle that is an integer
and converges to $1$ must eventually \emph{be} $1$, and by independence its exponent
polynomial is then zero.  What the elementary argument does not exclude is an integer value
$\ge2$; that is exactly what the LP computation below addresses.

\subsection{The LP layer of the linear-width factorial target is empty for the control
(computed)}"""
t = t.replace(old, new)

# bibliography entry
anchor4 = "\\bibitem{BakerWustholz1993}"
assert t.count(anchor4) == 1
bib = r"""\bibitem{BakerHarmanPintz2001}
R.~C. Baker, G. Harman, and J. Pintz, \emph{The difference between consecutive primes, II},
Proc. London Math. Soc. (3) 83 (2001), 532--562.

"""
t = t.replace(anchor4, bib + anchor4)
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
