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

PENDING += [
 # --- thm:bell-transform-inverse ---
 (r"""\[
 X=\log(1+Y)=\sum_{k\ge1}\frac{(-1)^{k-1}}{k}Y^k.
\]
Use \eqref{eq:partial-bell-egf} to extract the coefficient of $t^n/n!$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof is this proof made formal.
\cref{eq:bell-transform-x} is \lean{Fabius.bell_transform_inverse} (module
\lean{BellComposition}), over any commutative $\mathbb Q$-algebra, in the form
$x_n=\sum_{k=1}^{n}(-1)^{k+1}(k-1)!\,\ExponentialPartialBellPolynomial nk(y_1,y_2,\ldots)$
with $y_n=\ExponentialCompleteBellPolynomial n(x)$ (Lean's \lean{Bell.complete}).
The proof is the one above: $X=\log(1+Y)$ is
\lean{Fabius.log_subst_exp_sub_one} ($\log\circ(\EulerE^t-1)=t$, from the
derivative and constant term), $\log(1+u)=\sum_{k\ge1}(-1)^{k+1}(k-1)!\,u^k/k!$
is \lean{Fabius.log_eq_egfA}, and the coefficient extraction is the exponential
composition theorem \lean{Fabius.egfA_subst_bellWeightSeries} of
\cref{thm:exponential-composition}.  The recursive, division-free inversion
over every commutative ring is \lean{Bell.complete_cumulant} and
\lean{Bell.cumulant_complete} (\lean{BellPolynomialInversion}).  The general
form \cref{eq:general-bell-inverse} is not formalized.""")),

 # --- thm:exponential-composition ---
 (r"""\eqref{eq:partial-bell-egf}.  The set-partition form is
\cref{thm:bell-poly-partitions} with an additional weight $b_k$ for the number of
blocks.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
This is \lean{Fabius.egfA_subst_bellWeightSeries} (module \lean{BellComposition}):
for $B(t)=\sum_k b_kt^k/k!$ and $A(t)=\sum_{j\ge1}a_jt^j/j!$ over any
commutative $\mathbb Q$-algebra, $B(A(t))=\sum_n\bigl(\sum_{k\le n}b_k
\ExponentialPartialBellPolynomial nk(a)\bigr)t^n/n!$, where substitution is
Mathlib's \lean{PowerSeries.subst}.  The proof reads the coefficients of the
substitution through the powers $A(t)^k$ and the column theorem
\lean{Fabius.bellWeightSeries_pow}.  The block-colour convolution of
\cref{thm:bell-partial-convolution} is the same theorem applied to a product,
\lean{Fabius.factorial_mul_partialBell_add}.""")),
]

PENDING += [
 # --- thm:bell-bihomogeneous ---
 (r"""The coefficient of $t^n/n!$ is
$n!k^{n-k}/(k!(n-k)!)=\binom nk k^{n-k}$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof is by induction on the
% pointing recurrence, over every commutative semiring.
\cref{eq:bell-bihomogeneous} is \lean{Fabius.partialBell_bihomogeneous}, assembled
from the degree homogeneity \lean{Fabius.partialBell_mul_left}
($\ExponentialPartialBellPolynomial nk(\alpha x)=\alpha^k\ExponentialPartialBellPolynomial nk(x)$)
and the weighted homogeneity \lean{Fabius.partialBell_pow_mul}
($\ExponentialPartialBellPolynomial nk(\beta^jx_j)=\beta^n\ExponentialPartialBellPolynomial nk(x)$),
module \lean{BellHomogeneity}; both are proved by induction on the pointing
recurrence rather than from the monomial expansion.  As a consequence the
Touchard specialization \cref{eq:touchard-bell-specialization} of
\cref{thm:bell-poly-specializations} is \lean{Fabius.bell_complete_const} and
\lean{Fabius.bell_complete_const_eq_touchard_eval}, and the Touchard generating
function $\exp(x(\EulerE^t-1))$ is \lean{Fabius.exp_subst_smul_exp_sub_one}.
\cref{eq:bell-linear-arguments} is not formalized.""")),

 # --- thm:merged-bernoulli-stirling-touchard ---
 (r"""whereas $E_1(x)\leq\EulerE^{-x}/x$ for $x\geq1$.
""",
  r"""% ed.: crosswalk added 2026-09-01.
\begin{remark}[Formal crosswalk]
\cref{eq:merged-bernoulli-stirling} is \lean{Fabius.bernoulli_eq_sum_stirlingSecond}
(module \lean{BernoulliStirling}) for Mathlib's Bernoulli numbers
\lean{bernoulli}, whose convention $B_1=-1/2$ matches the generating function
$t/(\EulerE^t-1)$ used here.  The Lean proof is the first paragraph of this
proof made formal: Mathlib's \lean{bernoulliPowerSeries_mul_exp_sub_one}
gives $\mathscr B(t)(\EulerE^t-1)=t$, \lean{Fabius.log_subst_exp_sub_one}
gives $t=\log(1+y)$ at $y=\EulerE^t-1$, cancelling the non-zero-divisor
$\EulerE^t-1=t\cdot(\EulerE^t-1)/t$ identifies $\mathscr B$ with
$\log(1+y)/y$ composed with $\EulerE^t-1$
(\lean{Fabius.bernoulliPowerSeries_eq_logDivSeries_subst}), and the
coefficients are read off by the exponential composition theorem
(\lean{Fabius.egfA_subst_bellWeightSeries}) with the Stirling specialization of
the partial Bell polynomials.  The two integral representations are not
formalized.
\end{remark}
"""),
]

PENDING += [
 # --- thm:second-ogf ---
 (r"""The factorial form follows by direct factorization.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
The product formula is \lean{Fabius.prod_one_sub_mul_X_mul_stirlingColumnOGF}
(module \lean{StirlingOrdinaryGF}): in $R[[x]]$, for every commutative ring
$R$, the column series $\sum_{r\ge0}\StirlingSecondKind{k+r}{k}x^r$ times
$\prod_{j=1}^k(1-jx)$ equals $1$, proved exactly as above from the column
recurrence $(1-kx)F_k=F_{k-1}$ (\lean{Fabius.one_sub_mul_X_mul_stirlingColumnOGF_succ}).
The expansion of each geometric factor is
\lean{Fabius.stirlingColumnOGF_eq_prod_mk_pow}, which identifies the column
series with $\prod_{j=1}^k\sum_{r\ge0}j^rx^r$; the complete-homogeneous
coefficient formula \cref{eq:second-complete-symmetric} is the coefficient
extraction of that product and is not stated separately.""")),

 # --- thm:eulerian-power-series ---
 (r"""\eqref{eq:eulerian-explicit}.  Formula \eqref{eq:eulerian-k1} is its case $k=1$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean route avoids the EGF and goes
% through Worpitzky's identity instead.
\cref{eq:eulerian-power-series} is \lean{Fabius.one_sub_X_pow_mul_succPowSeries}
(module \lean{EulerianGeneratingFunctions}), stated in $R[[t]]$ over any
commutative ring $R$ as $(1-t)^{n+1}\sum_{m\ge0}(m+1)^nt^m
=\sum_{k}\TypeAEulerianNumber nk\,t^k$.  The formal proof reads Worpitzky's
identity \cref{thm:worpitzky} column by column: $(m+1)^n=\sum_k
\TypeAEulerianNumber nk\binom{m+1+k}{n}$ and $\sum_m\binom{m+d}{d}t^m
=(1-t)^{-d-1}$ (Mathlib's \lean{PowerSeries.mk_one_pow_eq_mk_choose_add})
give the identity with $t^{n-1-k}$ in place of $t^k$, and the symmetry
\cref{eq:eulerian-symmetry}, formalized as \lean{Fabius.eulerianNumber_symm}
by induction on the recurrence, reverses the exponents.  The explicit formula
\cref{eq:eulerian-explicit} is its $k$-th coefficient,
\lean{Fabius.eulerianNumber_eq_sum_int}, and \cref{eq:eulerian-k1} is
\lean{Fabius.eulerianNumber_one_right}.""")),

 # --- thm:merged-riordan ---
 (r"""$\overline f$ gives the inverse.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
Module \lean{ExponentialRiordan} defines \lean{Fabius.expRiordan}
$[g,f]_{n,k}=\frac{n!}{k!}[t^n]\,g(t)f(t)^k$ over any
$\RationalNumbers$-algebra.  \cref{eq:merged-riordan-action} is
\lean{Fabius.expRiordan_action} (for $f$ with zero constant term, using the
truncation lemma \lean{Fabius.coeff_mul_subst_eq}: only $k\le n$ contributes
to the $n$-th coefficient of $g\,A(f)$), the product law
\cref{eq:merged-riordan-product} is \lean{Fabius.expRiordan_mul}, and the
inverse law \cref{eq:merged-riordan-inverse} is
\lean{Fabius.expRiordan_mul_inverse} in the form: if $\overline f\circ f=t$
and $g\cdot(h\circ f)=1$ then $[g,f]\,[h,\overline f]$ is the identity array
\lean{Fabius.expRiordan_one_X}.  The Stirling examples are
\lean{Fabius.expRiordan_one_exp_sub_one} ($[1,\EulerE^t-1]$ has entries
$\StirlingSecondKind nk$) and \lean{Fabius.expRiordan_one_log}
($[1,\log(1+t)]$ has entries $\StirlingFirstKindSigned nk$).""")),
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
