p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()

old = r"""The theorem says where shared content must go, not that any is forced: real synchronization
does not transparently force modular synchronization.  Note also that a prime dividing both
channels of \eqref{ct:eq-AE-channels} satisfies $A^{2q}\equiv9^p$, $M^{2q}\equiv4^p$, so
$\gcd(D_-,D_+)\mid\gcd(M^{2q}-4^p,A^{2q}-9^p)$, whose logarithm is $o(q)$ by the fixed-group
Corvaja--Zannier bound applied to $\langle(M,A),(2,3)\rangle$: the two channels are
asymptotically disjoint."""
assert t.count(old) == 1
new = r"""The theorem says where shared content must go, not that any is forced: real synchronization
does not transparently force modular synchronization.  The two channels are, however,
asymptotically disjoint, by an exact descent to the original gaps:

\begin{proposition}[Channel descent]\label{ct:prop-descent}
For all integers, $a(ad-bc)+b(ac-bd)=d(a^2-b^2)$ and $d(ac-bd)-c(ad-bc)=b(c^2-d^2)$.  Hence
any common divisor of the two channels divides $d(a^2-b^2)$ and $b(c^2-d^2)$, and a prime
$\ell\nmid6$ dividing both channels of \eqref{ct:eq-AE-channels} divides the doubled gaps
$M^{2q}-4^p=(M^q-2^p)(M^q+2^p)$ and $A^{2q}-9^p=(A^q-3^p)(A^q+3^p)$.
\end{proposition}

\statuslean{} (\lean{dvd_of_dvd_both_channels}, \lean{prime_dvd_doubled_gaps_of_dvd_both_channels}).
The pair $(M^{2q}/4^p,A^{2q}/9^p)$ lies in the fixed group $\langle(M,A),(2,3)\rangle$ with
multiplicatively independent coordinates, so the fixed-group Corvaja--Zannier bound of
Section~\ref{primetop:uniform-gcd} gives $\log\gcd(D_-,D_+)=o(q)$ for $\gcd$ taken prime to
$6$: shared channel support is, up to sign, shared support of the original synchronized
gaps, and it is asymptotically negligible."""
t = t.replace(old, new)

old2 = r"""\paragraph{Where genuinely new input could enter.}"""
assert t.count(old2) == 1
new2 = r"""\paragraph{Does this bring the proof closer?}  Honestly assessed: no theorem in
Sections~\ref{sec:primetop}--\ref{sec:masks} narrows the \emph{truth} of the conjecture;
the open problem is unchanged and still sits exactly on the four-exponentials boundary of
Section~\ref{sec:fourexp}.  What has changed is the map of the search space.  Four
constructions that looked like candidate proof engines are now closed exactly (growing-order
linear stencils, fixed and subcritical-width factorial cocycles, cubic-trace iteration,
one-direction Prouhet masks), one proposed intermediate target has been shown to be the
conjecture itself (Theorem~\ref{sparsequad:thm-scs}), and the finite algebra behind every
closure is kernel-checked, so none of these routes will be re-opened by an oversight.  The
residual targets below are the honest statement of what a proof would still have to supply.

\paragraph{Where genuinely new input could enter.}"""
t = t.replace(old2, new2)
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
