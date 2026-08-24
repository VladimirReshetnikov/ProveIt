p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
old = r"""\subsection{Directions not yet exhausted}"""
assert t.count(old) == 1
new = r"""\subsection{Channel reconnaissance on near-$\thetaq$ pairs (computed)}
\label{log:channel-recon}

Section~\ref{ct:fifth} left open whether the two fifth-trace channels carry a stable
arithmetic signature that a Kummer or $S$-unit argument could grip.  An exact computation
(\statusexactcomp{}, \lean{gmpy2} big integers) over the surrogate pairs
$(M,A)$ with $A=\lfloor M^{\thetaq}\rceil$, $M\in\{5,7,11,13,41\}$, and all convergents
$p/q$ of $\log_2M$ with $q\le4000$ gives: the gcd of the two normalized fifth-trace factors
is $1$ in every case except three, and in those three it is a single small prime
($11$, $19$, $19$) carried with full valuation by exactly one channel --- twice the direct
gap, once the reciprocal gap --- as Theorem~\ref{ct:thm-channels} mandates.  No channel
preference and no growth of shared content along $q$ is visible.  This is what one expects
if nothing forces modular synchronization; as a target for ``forced shared trace content''
(Target~\ref{ct:target}(i)), the fifth trace looks barren, and effort should go to
channel-\emph{incompatibility} (Target~\ref{ct:target}(ii)) or higher traces instead.

\subsection{Directions not yet exhausted}"""
t = t.replace(old, new)
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
