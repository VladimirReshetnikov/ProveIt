p = "C:/ProveIt/Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/alaoglu-erdos-unified-report.tex"
t = open(p, encoding="utf-8").read()
def rep(old, new, count=1):
    global t
    assert t.count(old) == count, (t.count(old), old[:60])
    t = t.replace(old, new)

rep(r"""\begin{theorem}[Zero-free region]
\label{co:thm-finite4096}
If $2^x,3^x\in\Z$ and $2^x<4096$, then $x\in\Z$.  Equivalently, every nonintegral solution
satisfies $x\ge12$, and every candidate that is not a power of two is at least $4096$.
\end{theorem}

\begin{statusbox}{\statuslean{} ---
\lean{integer_of_two_three_rpow_integer_of_two_rpow_lt_4096},
\lean{twelve_le_of_not_integer_of_two_three_rpow_integer},
\lean{le_of_twoBaseNonintegerCandidate_4096} in \lean{FiniteCheck4096}, extending
\lean{FiniteCheck} ($2^x<100$) and \lean{FiniteCheck256} ($2^x<256$, hence $x\ge8$).}
\end{statusbox}
""", r"""\begin{theorem}[Zero-free region]
\label{co:thm-finite4096}
If $2^x,3^x\in\Z$ and $2^x<8192$, then $x\in\Z$.  Equivalently, every nonintegral solution
satisfies $x\ge13$, and every candidate that is not a power of two is at least $8192$.
\end{theorem}

\begin{statusbox}{\statuslean{} ---
\lean{integer_of_two_three_rpow_integer_of_two_rpow_lt_8192},
\lean{thirteen_le_of_not_integer_of_two_three_rpow_integer},
\lean{le_of_twoBaseNonintegerCandidate_8192} in \lean{FiniteCheck8192}, extending
\lean{FiniteCheck4096} ($2^x<4096$, hence $x\ge12$), \lean{FiniteCheck256} ($2^x<256$,
hence $x\ge8$), and \lean{FiniteCheck} ($2^x<100$).  Statements elsewhere in this report that
quote the earlier kernel bound $x\ge12$ remain valid a fortiori; the $4096$ module is kept as
an independent, separately replayable certificate.}
\end{statusbox}
""")

rep(r"""PARI/GP and revalidated independently with exact big-integer arithmetic in Python.  Five
tiers suffice, with tier populations $78$, $488$, $3241$, $28$, $1$:
""", r"""PARI/GP and revalidated independently with exact big-integer arithmetic in Python.  Five
tiers suffice, with tier populations $78$, $488$, $3241$, $28$, $1$.  The further extension
to $8192$ (\lean{FiniteCheck8192}) replays $4095$ certificates the same way, in nine tiers
built from the convergent enclosures below together with one \emph{semiconvergent},
$478245/301739<\thetaq$, which is needed only for $m=5143$ and $m=6714$ (the two values in
$[4096,8192)$ whose $m^{\thetaq}$ lies within $4\cdot10^{-4}$ of an integer); the next
convergent would have required exponents near $1.7\cdot10^7$, while the semiconvergent keeps
the largest exponent at $478245$ and the whole table replays in under two minutes.  The
tier populations for $4096\le m<8192$ are $826$, $3120$, $71$, $12$, $33$, $2$, $2$, $28$,
$2$.  For the $4096$ table:
""")

rep(r"""\textbf{Kernel.}  $2^x<4096$ and $2^x,3^x\in\Z$ imply $x\in\Z$; a nonintegral solution has
$x\ge12$.  \statuslean{} \lean{FiniteCheck4096}.""",
    r"""\textbf{Kernel.}  $2^x<8192$ and $2^x,3^x\in\Z$ imply $x\in\Z$; a nonintegral solution has
$x\ge13$.  \statuslean{} \lean{FiniteCheck8192} (and, independently, $2^x<4096$ in
\lean{FiniteCheck4096}).""")

rep(r"""above.  Nothing in Section~\ref{sec:conditional} or Section~\ref{sec:program} that is tagged
\statuslean{} depends on either scan; wherever a numeric threshold is used inside a
kernel-verified statement, that threshold is $12$.

\paragraph{A drafted extension of the kernel region.}
An attempt to raise the kernel-checked region from $2^x<4096$ to $2^x<16384$ exists in draft.
It follows the \lean{FiniteCheck4096} pattern, splitting the enlarged table into four chunks
so that no single \lean{decide} call carries the whole certificate.  The certificate rows
themselves verify: each chunk's Boolean recursion evaluates and each row's exact integer
comparison is accepted.  What has not been accepted is the assembly --- the per-chunk length
lemmas that glue the four tables into a single covering statement exceeded the elaborator's
recursion limit, so the module does not compile end to end and no theorem is available for
use.  Until that is resolved the kernel bound is unchanged at $x\ge12$.  \statusdraft""",
    r"""above.  Nothing in Section~\ref{sec:conditional} or Section~\ref{sec:program} that is tagged
\statuslean{} depends on either scan; wherever a numeric threshold is used inside a
kernel-verified statement, that threshold is $12$ or $13$.

\paragraph{The $8192$ extension and the drafted $16384$ region.}
The kernel region was raised from $2^x<4096$ to $2^x<8192$ by a single further table of
$4095$ rows (\lean{FiniteCheck8192}, Section~\ref{co:finite}); the only new ingredient is a
semiconvergent enclosure for the two hardest values.  An earlier attempt at $2^x<16384$
exists in draft: it splits the enlarged table into four chunks, every chunk's Boolean
recursion and every row's exact comparison are accepted, but the per-chunk length lemmas
that glue the chunks into one covering statement exceeded the elaborator's recursion limit,
so no theorem is available from it.  \statusdraft{}  The $8192$ module shows that a single
unsplit table of $4096$ rows with exponents up to $4.8\cdot10^5$ replays comfortably, so the
natural next step is one more unsplit table for $[8192,16384)$, whose hardest rows will
again need semiconvergents rather than the $10^7$-denominator convergent.""")

rep(r"""\item $x\ge12$, by the kernel-checked zero-free region $2^x<4096$.  \statuslean""",
    r"""\item $x\ge13$, by the kernel-checked zero-free region $2^x<8192$.  \statuslean""")

rep(r"""zero-free region $2^x<4096$; transcendence of every hypothetical counterexample; multiplicative""",
    r"""zero-free region $2^x<8192$; transcendence of every hypothetical counterexample; multiplicative""")

rep(r"""The zero-free region $2^{x}<4096$ is kernel-verified, while the current software frontier is
$2^{27}$ (\statuscomp{}) in Section~\ref{sec:finite27}.  A source draft aiming at $2^{14}$
has verified arithmetic rows but no accepted assembled theorem, so the next target is a
generated, kernel-replayed certificate beyond $4096$, with $16384$ a useful engineering
milestone rather than an established bound.""",
    r"""The zero-free region $2^{x}<8192$ is kernel-verified, while the current software frontier is
$2^{27}$ (\statuscomp{}) in Section~\ref{sec:finite27}.  The next target is one more
generated, kernel-replayed table for $[8192,16384)$; the semiconvergent device of
\lean{FiniteCheck8192} keeps its exponents far below the $10^7$ scale of the next convergent.""")

rep(r"""$2^x<4096\Rightarrow x\in\Z$\ \ (so $x\ge12$) & \statuslean & \lean{FiniteCheck4096} \\""",
    r"""$2^x<4096\Rightarrow x\in\Z$\ \ (so $x\ge12$) & \statuslean & \lean{FiniteCheck4096} \\
$2^x<8192\Rightarrow x\in\Z$\ \ (so $x\ge13$) & \statuslean & \lean{FiniteCheck8192} \\""")

rep(r"""\lean{.../FiniteCheck4096} & zero-free region $2^x<4096$ (kernel \lean{decide} table) \\""",
    r"""\lean{.../FiniteCheck4096} & zero-free region $2^x<4096$ (kernel \lean{decide} table) \\
\lean{.../FiniteCheck8192} & zero-free region $2^x<8192$ (one unsplit \lean{decide} table,
nine tiers, one semiconvergent enclosure) \\""")

# factorial cocycle: note the sharper q bound
rep(r"""$x$ is needed.  The kernel bound $x\ge12$ (\lean{FiniteCheck4096}) enters only through
$q\le(2/3)^{12}=0.0077\ldots$.""",
    r"""$x$ is needed.  The kernel bound $x\ge12$ (\lean{FiniteCheck4096}; now $x\ge13$ by
\lean{FiniteCheck8192}) enters only through $q\le(2/3)^{12}=0.0077\ldots$.""")

# frontier section: mention the literal advance
rep(r"""\paragraph{Where genuinely new input could enter.}""",
    r"""The one literal advance on the conjecture itself made during this integration is finite:
the kernel-verified zero-free region moved from $2^x<4096$ to $2^x<8192$
(Theorem~\ref{co:thm-finite4096}), so a counterexample now has $x\ge13$ with kernel trust.
The software scans already reach $x>27$; the gap between the two is engineering, not
mathematics, and the semiconvergent device makes each further doubling a routine table.

\paragraph{Where genuinely new input could enter.}""")

open(p, "w", encoding="utf-8", newline="\n").write(t)
print("ok")
