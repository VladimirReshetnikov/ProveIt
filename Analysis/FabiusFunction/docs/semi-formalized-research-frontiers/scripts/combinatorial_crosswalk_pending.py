# -*- coding: utf-8 -*-
r"""Pending formal-crosswalk remarks for
drafts/combinatorial-coefficient-calculus/Combinatorial_Coefficient_Calculus.tex.

Division of labour (2026-09-01): the consolidation owner edits the manuscript
body and rebuilds its PDF; the Lean side supplies crosswalk remarks here.
Each entry is (anchor, remark): the remark is inserted right after the anchor
text, which must occur exactly once.  An entry whose remark is already present
is skipped, so the script is idempotent.  After applying, regenerate the
register with combinatorial_lean_register.py.

Run:  python combinatorial_crosswalk_pending.py <path-to-tex>
"""
import io, sys

path = sys.argv[1]
s = io.open(path, encoding='utf-8').read()


def remark(body):
    return '\n\\begin{remark}[Formal crosswalk]\n' + body + '\n\\end{remark}\n'


PENDING = [
 # --- thm:stirling-egfs ---
 (r"""follows by inserting \cref{eq:second-explicit} and summing exponentials.  Summing over
$k$ with weight $y^k$ proves \cref{eq:second-double-egf}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; formal power series over any commutative
% Q-algebra, with the exponential and log(1+X) series of Mathlib.
The three column identities are formal power-series identities in Lean, over
every commutative $\mathbb Q$-algebra (module
\lean{StirlingGeneratingFunctions}): with $\lean{egf}\,a=\sum_n a_nz^n/n!$,
\cref{eq:second-egf} is \lean{Fabius.exp_sub_one_pow}
($(\EulerE^z-1)^k=\sum_n k!\StirlingSecondKind nk z^n/n!$) and
\lean{Fabius.egf_stirlingSecond};
\cref{eq:unsigned-first-egf} is \lean{Fabius.negLogOneSub_pow} and
\lean{Fabius.egf_stirlingFirst}, where $-\log(1-z)=\sum_{n\ge1}z^n/n$ is
\lean{Fabius.negLogOneSub}; and \cref{eq:signed-first-egf} is
\lean{Fabius.log_pow}, with Mathlib's \lean{PowerSeries.log} for
$\log(1+z)$.  The Lean proofs differ from the text: the second-kind identity
is read off coefficientwise from the binomial expansion of
$(\EulerE^z-1)^k$ into the rescaled exponentials $\EulerE^{mz}$ together with
the surjection formula (\cref{thm:second-explicit}); the unsigned first-kind
identity is proved by induction on $k$ from the first-order equation
$(1-z)\,Y'=(k+1)\,Y_k$ satisfied by both sides, using that a power series over
a torsion-free ring is determined by its derivative and constant term
(\lean{Fabius.eq_of_one_sub_X_mul_derivative_eq}); the signed identity is the
substitution $z\mapsto -z$ (\lean{PowerSeries.rescale}).  The bivariate
generating function \cref{eq:second-double-egf} and the derivative identity
\cref{eq:log-over-one-plus} are not formalized.""")),

 # --- thm:worpitzky ---
 (r"""permutation records the relative order, and its $k$ descents specify $k$ mandatory
separations among the $n$ sorted positions.  Stars and bars gives
$\binom{x+k}{n}$ words for each permutation with $k$ descents.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; Lean defines the Eulerian numbers by the
% recurrence and proves Worpitzky by induction, not by coefficient extraction.
In Lean the Eulerian numbers \lean{Fabius.eulerianNumber} are defined by the
recurrence of \cref{thm:eulerian-recurrence}
(\lean{Fabius.eulerianNumber_succ_left}); the descent count is not
formalized.  Worpitzky's identity is \lean{Fabius.worpitzky_nat} for natural
$x$ and \lean{Fabius.worpitzky_polynomial} in $\mathbb Q[x]$, where
$\binom{x+k}{n}$ is \lean{Fabius.binomialPoly} (module
\lean{EulerianNumbers}); both are stated with the sum over $0\le k\le n$,
the extra term $k=n$ vanishing (\lean{Fabius.eulerianNumber_eq_zero_of_le}).
The Lean proof is an induction on $n$ from the one-step relation
$x\binom{x+k}{n}=(n-k)\binom{x+k+1}{n+1}+(k+1)\binom{x+k}{n+1}$
(\lean{Fabius.mul_choose_add_eq}), and the polynomial identity follows from
the natural-number identity because a polynomial over $\mathbb Q$ is
determined by its values at the natural numbers.  The row sum
$\sum_k\TypeAEulerianNumber nk=n!$ is \lean{Fabius.sum_eulerianNumber_eq_factorial};
the symmetry \cref{eq:eulerian-symmetry} is not formalized.  The power sums of
\cref{cor:eulerian-power-sum} are \lean{Fabius.sum_range_pow_succ_eq_sum_eulerianNumber},
in the form $\sum_{r=0}^{m}r^{n+1}=\sum_{k}\TypeAEulerianNumber{n+1}{k}\binom{m+k+1}{n+2}$.""")),
]

PENDING += [
 # --- thm:bell-poly-specializations ---
 (r"""earlier.  Summing over $k$ yields \eqref{eq:bell-factorial-complete} and
\eqref{eq:bell-number-specialization}.  Finally $x_j=x$ gives
$\exp(x(\EulerE^t-1))$, the EGF of $\TouchardPolynomial{n}(x)$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proofs follow the text exactly
% (column generating functions compared coefficientwise), except for the
% second-kind case, which is proved directly from the vertical recurrence.
In Lean the partial Bell polynomials \lean{Fabius.partialBell} are defined by the
pointing recurrence of \cref{thm:bell-poly-recurrences} over any commutative
semiring (module \lean{PartialBellPolynomials}), and the column generating
function of \cref{thm:bell-poly-egf} is \lean{Fabius.bellWeightSeries_pow}
(module \lean{BellGeneratingFunctions}), proved by induction on $k$ from the
first-order equation $Y'=(k+1)X'\,Y_k$ and the uniqueness of its solution.
The specializations are then read off exactly as in the text:
\cref{eq:bell-first-specialization} is \lean{Fabius.partialBell_factorial_pred}
(comparing with \lean{Fabius.negLogOneSub_pow}), \cref{eq:bell-lah-specialization}
is \lean{Fabius.partialBell_factorial} (comparing with the Lah column
generating function $(t/(1-t))^k=\sum_n k!\LahNumber{n}{k}t^n/n!$,
\lean{Fabius.X_mul_mkOne_pow}, proved here by the same first-order method),
\cref{eq:bell-second-specialization} is \lean{Fabius.partialBell_one} (directly
from the vertical recurrence of the second kind), and
\cref{eq:bell-number-specialization} is \lean{Fabius.bell_complete_one}.  The
complete polynomials are Mathlib-free \lean{Bell.complete}, related to the
partial ones by \lean{Fabius.bell_complete_eq_sum_partialBell}; their
generating function $\exp X(t)$ is \lean{Fabius.exp_subst_bellWeightSeries},
from the equation $Y'=X'Y$, $Y(0)=1$
(\lean{Fabius.eq_zero_of_derivative_eq_mul}).  The factorial row sum
\cref{eq:bell-factorial-complete} and the Touchard identity
\cref{eq:touchard-bell-specialization} are not formalized.""")),

 # --- thm:bell-egf ---
 (r"""coefficient comparison in that equation gives
\eqref{eq:bell-binomial-recurrence} and $\mathscr B(0)=1$, so it uniquely determines
the series.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
The identity $\mathscr B(z)=\exp(\EulerE^z-1)$ is \lean{Fabius.exp_subst_exp_sub_one}
(module \lean{BellGeneratingFunctions}), stated as the substitution of
Mathlib's exponential series into itself minus one, over any commutative
$\mathbb Q$-algebra; it is the case $x=(1,1,\ldots)$ of the complete Bell
generating function \lean{Fabius.exp_subst_bellWeightSeries}, whose Lean proof
is the uniqueness argument of this proof: both sides satisfy
$Y'=\EulerE^z\,Y$ with $Y(0)=1$.""")),
]

applied = 0
for anchor, text in PENDING:
    if text.strip() in s:
        continue
    n = s.count(anchor)
    assert n == 1, (n, anchor[:70])
    s = s.replace(anchor, anchor + text)
    applied += 1

io.open(path, 'w', encoding='utf-8', newline='\n').write(s)
print('applied', applied, 'pending remarks')
