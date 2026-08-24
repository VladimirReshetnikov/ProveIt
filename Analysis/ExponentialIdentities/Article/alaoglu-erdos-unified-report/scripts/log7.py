p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
def rep(old, new):
    global t
    assert t.count(old) == 1, old[:70]
    t = t.replace(old, new)

rep(r"""The proposition removes the exact-unit branch of
Target~\ref{fc:target-linear} in full generality: a factorial cocycle that is an integer
and converges to $1$ must eventually \emph{be} $1$, and by independence its exponent
polynomial is then zero.  What the elementary argument does not exclude is an integer value
$\ge2$; that is exactly what the LP computation below addresses.""",
    r"""The proposition does more than remove the exact-unit case: it \emph{closes the
constructive branch of Target~\ref{fc:target-linear} entirely}.

\begin{corollary}[The constructive branch of the linear-width target is empty]
\label{log:cor-target-dead}
Let $(M,A)$ be any pair in the mesoscopic window (in particular the output pair of any
hypothetical counterexample), and let $P_n\in\Z[T]$ be nonzero polynomials of arbitrary
degrees with $v_p(\mathcal F_{P_n,n})\ge0$ for every prime $p$ and
$\mathcal F_{P_n,n}\to1$.  Then no such sequence exists: for all large $n$ the two
conditions force $P_n=0$.
\end{corollary}

\begin{proof}
Nonnegative valuations make $\mathcal F_{P_n,n}$ a positive integer; convergence to $1$
puts it in $(0,2)$, hence equal to $1$, for all large $n$; and
Proposition~\ref{log:prop-factorial-independence} then forces every coefficient of $P_n$ to
vanish.
\end{proof}

No width hypothesis, coefficient bound, or archimedean sign analysis enters: items (2) and
(3) of the target are jointly unsatisfiable with $P_n\ne0$.  The ``linear-width escape''
left open by Theorem~\ref{fc:thm-window} therefore does not exist, and the
factorial-cocycle architecture of Section~\ref{sec:factorialcocycle} is a complete no-go
for proving the conjecture through an integer sequence converging to one.  (The proof is
embarrassingly short in hindsight; what was missing was the multiplicative independence of
the $F_t$, which makes the endgame ``integer $\to1$ is eventually $1$'' terminal rather
than a step.)  What the argument does not exclude is a cocycle that is an integer
\emph{without} converging to $1$ --- there the LP computation below gives strong evidence of
emptiness as well, now the only remaining question in this family.""")

rep(r"""A positive answer with an eventual strict
inequality $\mathcal F_{P_n,n}\ne1$ (e.g.\ a sign-controlled first surviving mode) proves
the conjecture; a negative answer by a dual valuation certificate closes the family.
\end{target}""",
    r"""A positive answer with an eventual strict
inequality $\mathcal F_{P_n,n}\ne1$ (e.g.\ a sign-controlled first surviving mode) proves
the conjecture; a negative answer by a dual valuation certificate closes the family.
\emph{Update (session log): the constructive branch is empty ---
Corollary~\ref{log:cor-target-dead} shows conditions (2) and (3) already force $P_n=0$ for
any mesoscopic pair, so this target is resolved negatively; only integrality without
convergence to $1$ remains, and the LP computation of Section~\ref{log:lp-experiment}
indicates that it is empty too.}
\end{target}""")

rep(r"""are not yet known to be equivalent to the conjecture: the linear-width factorial feasibility
problem (Target~\ref{fc:target-linear}), whose dual certificates are finite integer programs;
shared structural-face capture (Target~\ref{masks:target}), a finite-prime statement about
repeated cancellation on fixed Newton faces coupled by \eqref{masks:eq-transport}; and the
nonlinear prime-top problem of Section~\ref{primetop:remaining}.""",
    r"""are not yet known to be equivalent to the conjecture: shared structural-face capture
(Target~\ref{masks:target}), a finite-prime statement about repeated cancellation on fixed
Newton faces coupled by \eqref{masks:eq-transport}; and the nonlinear prime-top problem of
Section~\ref{primetop:remaining}.  (The third such target at the time of integration, the
linear-width factorial feasibility problem, was resolved negatively during the session:
Corollary~\ref{log:cor-target-dead}.)""")

rep(r"""\item \textbf{Negative closure of the linear-width family.}  Done at the LP layer for the
control pair (Section~\ref{log:lp-experiment}): the cone is empty at every affordable shape,
including width ratios far above critical, and the dual certificate exposes the
dense-plus-capture mechanism.  What remains is to turn the certificate template into a
theorem valid for all $(n,d)$ and all mesoscopic pairs $(M,A)$.""",
    r"""\item \textbf{Negative closure of the linear-width family.}  Done: the constructive
branch (integrality plus convergence to $1$) is empty for every mesoscopic pair
(Corollary~\ref{log:cor-target-dead}), and the LP layer is empty for the control even
without the convergence condition (Section~\ref{log:lp-experiment}).  What remains is the
cosmetic residue: a certificate theorem excluding integer cocycle values $\ge2$ for all
$(n,d)$, for which the dense-plus-capture dual is the template.""")

rep(r"""Terminal factorials multiplicatively independent (window primes as hypothesis; finite core
kernel-checked) & \statuslean{} core; prime existence \statusknown &
\lean{TerminalFactorialIndependence}; Section~\ref{log:factorial-independence} \\""",
    r"""Terminal factorials multiplicatively independent (window primes as hypothesis; finite core
kernel-checked) & \statuslean{} core; prime existence \statusknown &
\lean{TerminalFactorialIndependence}; Section~\ref{log:factorial-independence} \\
Constructive branch of the linear-width factorial target empty for every mesoscopic pair &
\statusnew{} (one-paragraph proof from the independence proposition) &
Corollary~\ref{log:cor-target-dead} \\""")
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
