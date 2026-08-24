p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
def rep(old, new):
    global t
    assert t.count(old) == 1, old[:60]
    t = t.replace(old, new)

rep(r"""\statusnew{}, with the short-interval prime existence \statusknown{}.  (Bertrand's postulate
does not suffice: the window has sublinear length.  Huxley's asymptotic used in
Theorem~\ref{fc:thm-window} is stronger than needed here; existence at exponent
$0.525$ is enough.)""",
    r"""The finite core is \statuslean{} in \lean{TerminalFactorialIndependence}: the window
valuation $v_p(F_t)=1$ (\lean{padicValNat_termFall_eq_one}, from pure inequalities
$A^t-M^t<p\le A^t$, $A^t\le2(A^t-M^t)$, $A^t<p^2$), the exclusion $p\nmid F_{t'}$ for
$A^{t'}<p$, and the downward induction
(\lean{termFall_multiplicative_independent}), with the window primes supplied as an
explicit hypothesis.  The short-interval prime existence filling that hypothesis is
\statusknown{} (Bertrand's postulate does not suffice: the window has sublinear length;
Huxley's asymptotic used in Theorem~\ref{fc:thm-window} is stronger than needed, existence
at exponent $0.525$ is enough).""")

rep(r"""Session log: integral Schneider constants, structural-prime relaxation, Pólya/Gel'fond
view, $abc$ against convergent gaps (all quantified dead ends); control principle &
\statusnew & Section~\ref{sec:session-log} \\""",
    r"""Session log: integral Schneider constants, structural-prime relaxation, Pólya/Gel'fond
view, $abc$ against convergent gaps (all quantified dead ends); control principle &
\statusnew & Section~\ref{sec:session-log} \\
Terminal factorials multiplicatively independent (window primes as hypothesis; finite core
kernel-checked) & \statuslean{} core; prime existence \statusknown &
\lean{TerminalFactorialIndependence}; Section~\ref{log:factorial-independence} \\
LP layer of the linear-width factorial target empty for the control; dense-plus-capture
Farkas mechanism & \statusexactcomp &
Section~\ref{log:lp-experiment}; \path{scripts/linear_width_lp.py} \\""")

rep(r"""\lean{.../ExponentLatticeMask} & cleared evaluation, one-direction gap-power theorem and
cleared-value floor, adjacent valuation transport (additive and multiplicative), unshared
structural primes, orthogonality determinant lemma \\""",
    r"""\lean{.../ExponentLatticeMask} & cleared evaluation, one-direction gap-power theorem and
cleared-value floor, adjacent valuation transport (additive and multiplicative), unshared
structural primes, orthogonality determinant lemma \\
\lean{.../TerminalFactorialIndependence} & window-prime valuation $v_p(F_t)=1$ from pure
inequalities, high-prime exclusion, finite-product valuation, and multiplicative
independence of the terminal factorials under a window-prime hypothesis \\""")
open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
