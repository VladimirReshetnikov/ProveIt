p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
old = r"""\subsection{Directions not yet exhausted}"""
assert t.count(old) == 1
new = r"""\subsection{The LP layer of the linear-width factorial target is empty for the control
(computed)}
\label{log:lp-experiment}

Target~\ref{fc:target-linear} asked whether a factorial cocycle of \emph{linear} width can be
integral; the prime-window theorem closes widths below $\log_23-1=0.585\ldots$ and was
expected to leave the wider regime open.  The LP layer of the target was therefore computed
exactly for the control pair $(M,A)=(2,3)$ (\statusexactcomp{}, exact valuations, floating
LP with margins far from zero).  Writing $P=P_*S$ (which encodes the three archimedean
annihilations identically), the question is whether the rational polyhedral cone
$\{s:\sum_jc_j(s)V_p(n+j)\ge0\ \text{for all }p\le3^{n+d}\}$ contains a nonzero vector.
The result, over every affordable shape --- $n\in\{2,3,4,6\}$, all $4\le d\le12$ with
$3^{n+d}\le3^{15}$, hence width ratios $d/(n+d)$ up to $0.857$ --- is that the cone is
$\{0\}$: the optimal min-margin per unit coefficient is between $-17$ and $-28$ valuation
units and shows no trend toward feasibility as the width ratio passes $0.585$.  In
particular, for these $(n,d)$ \emph{no} real-coefficient multiple of $P_*$ of any size
makes every prime valuation of the cocycle nonnegative; a fortiori no integer one does.

The Farkas dual is more informative than the infeasibility.  At $(n,d)=(2,12)$ the
certificate is carried by eight rows: the \emph{dense} rows of the small primes
$3,11,13$ --- whose leading behaviour $V_p(t)\approx2^t/(p-1)$ contributes nothing against
the family, because $\sum_jc_j2^{n+j}=2^nP(2)=0$ kills the main term identically --- and
five \emph{sparse} rows of medium ``capture'' primes ($107$, $263$, $1129$, $1583$,
$6427$), each a single prime, which price the residual error terms of the dense rows.  The
mechanism is thus not the short-interval window of Theorem~\ref{fc:thm-window} (which needs
$n$ large) but a mixed small--medium-prime balance: the archimedean annihilations force the
dense main terms to cancel, and what the dense rows leave behind is negative against the
sparse captures.

Two caveats and one consequence.  The computation is at small $n$ and for the control pair
only, and the LP is the relaxation of an integer question --- but infeasibility of the
relaxation is the strong direction.  The consequence is a change of expectation:
Target~\ref{fc:target-linear} should be expected to have a \emph{negative} answer at every
width, and the right theorem to attempt is an infeasibility certificate family
$\{\mu_p^{(n,d)}\}$, built from the dense rows of a fixed small-prime set plus $O(1)$
capture primes, valid for all $(n,d)$ and for every pair $(M,A)$ in the mesoscopic window.
Such a theorem would close the entire factorial-cocycle architecture unconditionally,
converting Section~\ref{sec:factorialcocycle} from ``one escape width left open'' to a
complete no-go; the dual data above is the template for its proof.

\subsection{Directions not yet exhausted}"""
t = t.replace(old, new)
# Amend direction list: item 1 accomplished-ish, item 4 deprioritized
old2 = r"""\item \textbf{Negative closure of the linear-width family.}  For the controls the
factorial-cocycle feasibility problem (Target~\ref{fc:target-linear}) must be infeasible.
Computing its LP dual certificates for $(2^m,3^m)$ at increasing $n$ and extracting their
symbolic form could yield a proof that the family is infeasible for \emph{every} pair
satisfying the mesoscopic identities, closing the target negatively; or it could expose the
exact place where a structural prime would have to enter."""
assert t.count(old2) == 1
new2 = r"""\item \textbf{Negative closure of the linear-width family.}  Done at the LP layer for the
control pair (Section~\ref{log:lp-experiment}): the cone is empty at every affordable shape,
including width ratios far above critical, and the dual certificate exposes the
dense-plus-capture mechanism.  What remains is to turn the certificate template into a
theorem valid for all $(n,d)$ and all mesoscopic pairs $(M,A)$."""
t = t.replace(old2, new2)
old3 = r"""\item \textbf{Thirteen doublings.}  Closing the gap between the kernel region and the
directed-rounding scan is mechanical with the semiconvergent device; it converts
\statuscomp{} into \statuslean{} for every exponent bound used in the descent constants."""
assert t.count(old3) == 1
new3 = r"""\item \textbf{Thirteen doublings.}  Closing the gap between the kernel region and the
directed-rounding scan is mechanical with the semiconvergent device; it converts
\statuscomp{} into \statuslean{} for every exponent bound used in the descent constants.
(Deliberately not pursued further in this session: the marginal value of each doubling is
small, and the work is pure arithmetic replay.)"""
t = t.replace(old3, new3)
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
