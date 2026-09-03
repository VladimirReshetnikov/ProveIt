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
the symmetry \cref{eq:eulerian-symmetry} is \lean{Fabius.eulerianNumber_symm}
(\lean{EulerianGeneratingFunctions}).  The power sums of
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
\cref{eq:bell-factorial-complete} is not formalized; the Touchard identity
\cref{eq:touchard-bell-specialization} is
\lean{Fabius.bell_complete_const_eq_touchard_eval} (\lean{BellHomogeneity}).""")),

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
($[1,\log(1+t)]$ has entries $\SignedStirlingFirstKind{n}{k}$).""")),
]

PENDING += [
 # --- thm:newton-expansion ---
 (r"""with $k<j$ by excessive differencing, and gives $j!a_j$ for $k=j$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\lean{Fabius.newton_expansion} (module \lean{NewtonExpansion}) is the
falling-factorial form of \cref{eq:newton-expansion} in $K[x]$ for every field
$K$ of characteristic zero.  The formal route differs from the basis argument
above: Mathlib's Gregory--Newton formula \lean{shift_eq_sum_fwdDiff_iter}
gives $p(m)=\sum_{k\le m}\binom mk\Delta^kp(0)$ at every natural number $m$,
the terms with $k>\deg p$ vanish by
\lean{Polynomial.fwdDiff_iter_eq_zero_of_degree_lt}
(\lean{Fabius.eval_natCast_eq_sum_choose_fwdDiff}, over any commutative
ring), and two polynomials agreeing at infinitely many points are equal.""")),

 # --- thm:exponential-formula ---
 (r"""with weight $u^k$ proves the second, and setting $u=1$ proves the third.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
All three identities are formal power-series substitutions over any
$\RationalNumbers$-algebra: \cref{eq:partial-bell-egf} is
\lean{Fabius.bellWeightSeries_pow} (module \lean{BellGeneratingFunctions}),
\cref{eq:complete-bell-egf} is \lean{Fabius.exp_subst_bellWeightSeries}, and
\cref{eq:bivariate-bell-egf} is \lean{Fabius.exp_subst_smul_bellWeightSeries}
(module \lean{ExponentialFormula}), obtained from the $u=1$ case by the degree
homogeneity $\ExponentialPartialBellPolynomial nk(ux)=u^k
\ExponentialPartialBellPolynomial nk(x)$.  The formal proofs use the pointing
recurrence of \cref{thm:bell-poly-recurrences} rather than the multinomial
expansion.""")),

 # --- thm:ordered-bell ---
 (r"""size gives \eqref{eq:ordered-bell-recurrence}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
Module \lean{OrderedBell} defines \lean{Fabius.fubini} by
\cref{eq:ordered-bell-stirling}.  \cref{eq:ordered-bell-egf} is
\lean{Fabius.two_sub_exp_mul_egfA_fubini}, in the form
$(2-\EulerE^t)\sum_n\mathsf F_nt^n/n!=1$ over any $\RationalNumbers$-algebra,
proved as in the text: by the exponential composition theorem with block
weights $k!$ the generating function is $1/(1-u)$ at $u=\EulerE^t-1$
(\lean{Fabius.egfA_fubini}), and $(1-u)\cdot1/(1-u)=1$ is substituted.
Reading $1/(1-u)=1+u/(1-u)$ at $u=\EulerE^t-1$ coefficientwise gives
\cref{eq:ordered-bell-recurrence} as \lean{Fabius.fubini_succ}, written
$\mathsf F_{n+1}=\sum_{i\le n}\binom{n+1}{i+1}\mathsf F_{n-i}$; the
ordered-partition count is not formalized.""")),
]

PENDING += [
 # --- thm:merged-complementary-bell ---
 (r"""Absolute convergence follows from the ratio test for $m^n/m!$ at fixed $n$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
Module \lean{ComplementaryBell} defines \lean{Fabius.complementaryBell} by
\cref{eq:merged-complementary-bell} and identifies it with the complete Bell
polynomial at constant weights $-1$
(\lean{Fabius.complementaryBell_eq_bell_complete}), i.e. the Touchard
polynomial at $-1$.  \cref{eq:merged-complementary-egf} is
\lean{Fabius.exp_subst_neg_exp_sub_one}, the substitution of $-(\EulerE^t-1)$
into the exponential series over any $\RationalNumbers$-algebra;
\cref{eq:merged-complementary-recurrence} is
\lean{Fabius.complementaryBell_succ}, read off from the successor recurrence
of the complete Bell polynomials rather than from the differential equation;
and \cref{eq:merged-complementary-dobinski} is
\lean{Fabius.complementaryBell_eq_exp_mul_tsum}, the Poisson moment series
\lean{Fabius.tsum_pow_mul_pow_div_factorial} at parameter $-1$, whose summability
is part of that statement.""")),

 # --- cor:merged-bell-convolution-inverse ---
 (r"""The two EGFs are $\EulerE^{\EulerE^z-1}$ and $\EulerE^{1-\EulerE^z}$, whose product is $1$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\lean{Fabius.sum_choose_bell_mul_complementaryBell} (module
\lean{ComplementaryBell}), proved from the addition law
\lean{Bell.complete_add} of complete Bell polynomials at the weights $+1$ and
$-1$, whose sum is the zero weight sequence with complete Bell polynomials
$\delta_{n0}$ (\lean{Fabius.bell_complete_zero_weights}).""")),
]

PENDING += [
 # --- thm:eulerian-stirling ---
 (r"""using \eqref{eq:eulerian-symmetry}, or simply expanding around $t=1$, gives the
equivalent displayed form.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof takes the expansion around
% $t=1$ directly, with no appeal to symmetry.
\lean{Fabius.sum_eulerianNumber_mul_X_pow_eq_sum_stirlingSecond} (module
\lean{EulerianStirling}) is \cref{eq:eulerian-stirling} in $R[[t]]$ over any
commutative ring $R$, with $\TypeAEulerianPolynomial{n}(t)$ written as
$\sum_k\TypeAEulerianNumber nk\,t^k$.  The formal proof expands $(m+1)^n$ in
the rising-factorial basis, $(m+1)^n=\sum_k(-1)^{n-k}\StirlingSecondKind nk\,
k!\binom{m+k}{k}$ (\lean{Fabius.succ_pow_eq_sum_stirlingSecond_mul_choose}),
uses $\sum_m\binom{m+k}{k}t^m=(1-t)^{-k-1}$ to get
$\sum_m(m+1)^nt^m=\sum_k(-1)^{n-k}\StirlingSecondKind nk\,k!\,(1-t)^{-k-1}$
(\lean{Fabius.succPowSeries_eq_sum_stirlingSecond}), and multiplies by
$(1-t)^{n+1}$ through \cref{eq:eulerian-power-series}.""")),
]

PENDING += [
 # --- thm:second-reverse-recurrences ---
 (r"""$(1-\EulerE^{-x})F_k'(x)=kF_k(x)$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\cref{eq:second-triangular-explicit} is
\lean{Fabius.stirlingSecond_eq_pow_div_factorial_sub_sum} (module
\lean{StirlingTriangularExplicit}), proved exactly as in the first paragraph
from the surjection count $k^n=\sum_r\StirlingSecondKind nr\,r!\binom kr$
(\lean{Fabius.pow_eq_sum_stirlingSecond_mul_factorial_mul_choose}); the
formal statement holds for all $n,k\ge0$ with the sum running from $r=0$
(the extra term $\StirlingSecondKind n0/k!$ vanishes for $n\ge1$).  The
reverse recurrences \cref{eq:second-reverse-row,eq:second-reverse-column}
are not formalized.""")),
]

PENDING += [
 # --- thm:spivey ---
 (r"""classification is unique and gives the summand.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the formal proof is generating-functional,
% not the bijection above.
\lean{Fabius.spivey} (module \lean{BellShiftEGF}) proves
\cref{eq:spivey} from the shifted generating function
\lean{Fabius.egfA_bell_add},
$\sum_{n\ge0}\BellNumber{m+n}\frac{t^n}{n!}
=\TouchardPolynomial{m}(\EulerE^t)\,\EulerE^{\EulerE^t-1}$, which is the $m$-th
derivative of the Bell generating function.  The induction on $m$ uses
$\bigl(\sum_n\BellNumber{n+1}t^n/n!\bigr)=\EulerE^t\sum_n\BellNumber nt^n/n!$
(\lean{Fabius.egfA_bell_succ}, the binomial recurrence) and the Touchard
recurrence at $x=\EulerE^t$,
$\TouchardPolynomial{m+1}(\EulerE^t)=\bigl(\TouchardPolynomial{m}(\EulerE^t)\bigr)'
+\TouchardPolynomial{m}(\EulerE^t)\EulerE^t$
(\lean{Fabius.derivative_touchardExp}); the coefficient of $t^n/n!$ in
$\EulerE^{jt}\EulerE^{\EulerE^t-1}$ is the binomial convolution
$\sum_k\binom nk\BellNumber kj^{n-k}$.""")),

 # --- thm:bell-inversions ---
 (r"""turns it into the right side after expanding
$(X-1)^k$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\cref{eq:bell-inversion-one} is
\lean{Fabius.bell_eq_sum_neg_one_pow_choose_bell_succ} (module
\lean{BellShiftEGF}): binomial inversion
(\lean{Fabius.binomial_inversion_ring}) of the recurrence
\cref{eq:bell-binomial-recurrence} in the form
\lean{Fabius.bell_succ_eq_sum_choose}.  \cref{eq:bell-inversion-two} is not
formalized.""")),
]

PENDING += [
 # --- thm:eulerian-egf ---
 (r"""solves this equation and initial condition.  Formal uniqueness follows by
recursively comparing coefficients of $x$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof derives the EGF from the
% binomial recurrence, not from the differential equation.
\lean{Fabius.egfA_eulerianPolynomial_mul} (module \lean{EulerianEGF}) is
\cref{eq:eulerian-egf} in multiplicative form, as an identity in the ring
$(\RationalNumbers[t])[[x]]$ of formal power series in $x$ with polynomial
coefficients:
$\bigl(\sum_{n\ge0}\TypeAEulerianPolynomial{n}(t)\frac{x^n}{n!}\bigr)
\bigl(t-\EulerE^{(t-1)x}\bigr)=t-1$, where $\EulerE^{(t-1)x}$ is the
exponential series \lean{Fabius.expSeries} at $t-1$.  Comparing the
coefficients of $x^n/n!$, this identity is exactly the binomial recurrence
\cref{eq:eulerian-binomial-recurrence} (for $n\ge1$) together with
$\TypeAEulerianPolynomial{0}=1$, so the formal proof goes through
\cref{thm:eulerian-binomial-recurrence}.""")),

 # --- thm:eulerian-binomial-recurrence ---
 (r"""Using \eqref{eq:eulerian-egf}, this equals $F(x,t)-1$, which is the EGF of the
left sides.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the formal proof is independent of the EGF.
\lean{Fabius.eulerianPolynomial_binomial_recurrence} (module
\lean{EulerianEGF}) is \cref{eq:eulerian-binomial-recurrence} in $R[t]$ for
$n\ge1$ over any commutative ring $R$ (the case $n=1$ reads
$\TypeAEulerianPolynomial{1}=\TypeAEulerianPolynomial{0}$), transported from
the power-series form \lean{Fabius.eulerian_binomial_recurrence_series}.  The
formal proof uses the rational generating function
\cref{eq:eulerian-power-series}: writing
$\TypeAEulerianPolynomial{k}(t)=(1-t)^{k+1}\sum_m(m+1)^kt^m$, the right side
becomes $(1-t)^n\sum_mt^m\sum_{k<n}\binom nk(-1)^{n-1-k}(m+1)^k
=(1-t)^n\sum_m\bigl((m+1)^n-m^n\bigr)t^m$ by the binomial theorem
(\lean{Fabius.sum_choose_neg_one_pow_succPowSeries}), and
$\sum_mm^nt^m=t\sum_m(m+1)^nt^m$ (\lean{Fabius.X_mul_succPowSeries}) finishes.""")),
]

PENDING += [
 # --- thm:ordinary-composition ---
 (r"""coefficient, proving the second.  The third is the definition of the ordinary
Bell polynomial.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
Module \lean{OrdinaryBellComposition} defines the ordinary partial Bell
polynomials \lean{Fabius.ordPartialBell} over any commutative semiring by the
composition recurrence
$\OrdinaryPartialBellPolynomial n{k+1}(b)=\sum_{i=1}^{n}b_i
\OrdinaryPartialBellPolynomial{n-i}{k}(b)$, $\OrdinaryPartialBellPolynomial
n0=\delta_{n0}$, which is \cref{eq:ordinary-composition-compositions} unrolled
one part at a time; \lean{Fabius.coeff_pow_eq_ordPartialBell} is
$[x^n]G(x)^k=\OrdinaryPartialBellPolynomial nk(b_1,b_2,\ldots)$ for $G$ with
zero constant term, and \cref{eq:ordinary-composition-bell} is
\lean{Fabius.coeff_subst_eq_sum_ordPartialBell}, with the sum starting at
$k=0$ (the term $k=0$ is $a_0\delta_{n0}$, which also covers $c_0=a_0$).  The
reciprocal formula \cref{eq:reciprocal-ordinary-bell} is
\lean{Fabius.coeff_reciprocalSeries}, where \lean{Fabius.reciprocalSeries} is
$1/(1-u)$ at $u=-(A-1)$ and \lean{Fabius.mul_reciprocalSeries} shows it
inverts $A$.  The multinomial form \cref{eq:ordinary-composition-multiplicities}
is not formalized.""")),
]

PENDING += [
 # --- thm:merged-appell ---
 (r"""Setting $x=0$ in the Bernoulli translation formula gives the explicit
polynomial expansion.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
For the Bernoulli polynomials, the derivative identity in
\cref{eq:merged-appell-derivative} is Mathlib's
\lean{Polynomial.derivative_bernoulli}, and the translation formula
\cref{eq:merged-appell-translation} is \lean{Fabius.bernoulli_eval_add}
(module \lean{BernoulliAppell}).  The formal proof is the Taylor expansion
rather than the generating function: iterating the derivative identity gives
$\beta_n^{(k)}=n^{\underline k}\beta_{n-k}$
(\lean{Fabius.iterate_derivative_bernoulli}), so the Hasse derivatives are
$\binom nk\beta_{n-k}$ (\lean{Fabius.hasseDeriv_bernoulli}), and Mathlib's
\lean{Polynomial.taylor} expands $\beta_n(x+y)=\sum_k\beta_n^{[k]}(x)y^k$.
The explicit formula \cref{eq:merged-bernoulli-explicit} is Mathlib's
definition \lean{Polynomial.bernoulli_def}.  For the Euler polynomials,
\lean{Fabius.derivative_eulerPolynomial} and \lean{Fabius.eulerPolynomial_eval_add}
(module \lean{EulerPolynomials}) are the derivative and translation identities,
the latter an instance of the general Appell lemma \lean{Fabius.appell_eval_add}
(an Appell sequence with $\deg p_n\le n$ satisfies the translation formula, by
the Taylor expansion).""")),
]

PENDING += [
 # --- cor:shifted-stirling-evaluations ---
 (r"""\eqref{eq:stirling-n-to-n} is \eqref{eq:power-to-fall} evaluated at $x=n$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\cref{eq:shifted-power-to-fall} is
\lean{Fabius.X_pow_eq_sum_stirlingSecond_succ_mul_descPochhammer_comp} (module
\lean{StirlingShiftedEvaluations}), in $R[x]$ over any commutative ring $R$,
with $\FallingFactorial{x-1}{k}$ as the composition of Mathlib's
\lean{descPochhammer} with $x-1$; the proof is the cancellation above, using
that $x$ is a non-zero-divisor in $R[x]$ (\lean{Fabius.X_mul_cancel}).
\cref{eq:stirling-n-to-n} is
\lean{Fabius.pow_self_eq_sum_stirlingSecond_mul_descFactorial}.""")),
]

PENDING += [
 # --- thm:paired-sums ---
 (r"""which of the total $\ell+m$ components were marked.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the first-kind hockey stick is stated with
% lower index $k$, correcting the misprint $n$ (see the editorial note in the
% statement).
All six identities are over the natural numbers, and lie in module
\lean{StirlingSummations} except where noted.  The first equality of
\cref{eq:first-two-sums} is
\lean{Fabius.stirlingFirst_succ_succ_eq_sum_choose} (module
\lean{StirlingBasisChange}, which holds it because the reverse row recurrence
of \cref{eq:first-reverse-row} needs the same identity and neither module
imports the other), proved as the coefficient
of $x^{k+1}$ in $\RisingFactorial{x}{n+1}=x\,(x+1)\cdots(x+n)$, and the second
is \lean{Fabius.stirlingFirst_succ_succ_eq_sum_descFactorial} (with
$n!/j!=\FallingFactorial{n}{n-j}$); the first equality of
\cref{eq:second-two-sums} is \lean{Fabius.stirlingSecond_succ_succ_eq_sum}
(module \lean{BellStirling}) and the second
\lean{Fabius.stirlingSecond_succ_succ_eq_sum_pow}, both iterated recurrences.
The hockey sticks \cref{eq:first-hockey,eq:second-hockey} are
\lean{Fabius.stirlingFirst_add_succ_eq_sum} and
\lean{Fabius.stirlingSecond_add_succ_eq_sum}, telescoping the recurrences by
induction on $k$.  The convolutions
\cref{eq:first-convolution,eq:second-convolution} are
\lean{Fabius.choose_mul_stirlingFirst_add} and
\lean{Fabius.choose_mul_stirlingSecond_add}, specializations of the
block-colour convolution of partial Bell polynomials
(\cref{thm:bell-partial-convolution}, \lean{Fabius.factorial_mul_partialBell_add})
to the weights $(j-1)!$ and $1$.""")),
]

PENDING += [
 # --- thm:normal-order ---
 (r"""operators are equal.  The inverse relation is proved identically using
$\FallingFactorial mn=\sum_k\SignedStirlingFirstKind{n}{k}m^k$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof of \cref{eq:normal1} is by
% induction on $n$, not by evaluation on monomials.
Module \lean{StirlingNormalOrder} proves both identities applied to an
arbitrary polynomial $p$ over any commutative ring: \cref{eq:normal1} is
\lean{Fabius.iterate_X_mul_derivative}, $(xD)^np=\sum_k\StirlingSecondKind nk
x^kD^kp$, by induction on $n$ from
$xD(x^kD^kp)=k\,x^kD^kp+x^{k+1}D^{k+1}p$ (\lean{Fabius.X_mul_derivative_xkDk})
and the recurrence $\StirlingSecondKind{n+1}{k}=k\StirlingSecondKind nk
+\StirlingSecondKind n{k-1}$; \cref{eq:normal2} is
\lean{Fabius.xkDk_eq_sum_signedStirlingFirst}, obtained from it by Stirling
inversion (\lean{Fabius.stirling_inversion}).  The falling-factorial form
$\FallingFactorial{xD}{n}$ and the operator series
\cref{eq:der-from-diff,eq:diff-from-der} are not formalized.""")),
]

PENDING += [
 # --- thm:binomial-type-bell ---
 (r"""$h^{-1}(D_x)\EulerE^{xh(t)}=h^{-1}(h(t))\EulerE^{xh(t)}=t \EulerE^{xh(t)}$; coefficient comparison
gives \eqref{eq:delta-operator}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
Module \lean{BinomialType} defines \lean{Fabius.binomialTypePoly} by
\cref{eq:binomial-type-bell} as the complete Bell polynomial at the weights
$a_jx$ (\lean{Fabius.binomialTypePoly_eq_sum} is the expansion in partial Bell
polynomials).  \cref{eq:binomial-type-egf} is
\lean{Fabius.exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly}, the
bivariate exponential formula of \cref{thm:exponential-formula}, and
\cref{eq:binomial-type-identity} is \lean{Fabius.binomialTypePoly_add}, which
is the addition law $\ExponentialCompleteBellPolynomial n(\kappa+\eta)
=\sum_k\binom nk\ExponentialCompleteBellPolynomial k(\kappa)
\ExponentialCompleteBellPolynomial{n-k}(\eta)$ (\lean{Bell.complete_add}) at
$\kappa=xa$, $\eta=ya$, valid over any commutative ring and without the
hypothesis $a_1\ne0$.  The delta operator \cref{eq:delta-operator} is not
formalized.""")),
]

PENDING += [
 # --- thm:merged-sheffer ---
 (r"""eigenvalue $t$; multiplication of the EGF by $t$ and coefficient comparison
gives the lowering law.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
In module \lean{BinomialType} the Sheffer sequence is
\lean{Fabius.shefferPoly}, the binomial convolution
$s_n=\sum_k\binom nkc_kp_{n-k}$ of the coefficients $c_k$ of $g$ with the
binomial-type sequence $p_n$ of \cref{thm:binomial-type-bell}, so that
\lean{Fabius.egfA_mul_exp_subst_smul_bellWeightSeries} is the generating
function $g(t)\EulerE^{xB(t)}$.  \cref{eq:merged-sheffer-addition} is
\lean{Fabius.shefferPoly_add}: the binomial identity of $p_n$ in convolution
form (\lean{Fabius.binomialTypePoly_add'}) and the associativity of the
binomial convolution (\lean{Bell.binomialConv_assoc}), over any commutative
ring.  The lowering law \cref{eq:merged-sheffer-lowering} is not
formalized.""")),
]

PENDING += [
 # --- thm:bell-leading-zeros ---
 (r"""$t^n$ in \eqref{eq:partial-bell-egf} gives the factorial factor displayed.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof is this proof made formal.
\lean{Fabius.partialBell_leadingZeros} (module \lean{BellLeadingZeros}) is
\cref{eq:bell-leading-zeros} over any $\RationalNumbers$-algebra, for the
zero-padded weights \lean{Fabius.leadingZeros} ($x_j$ replaced by $0$ for
$j\le q$) and the rescaled weights \lean{Fabius.qScaled}
($i\mapsto x_{q+i}/\binom{q+i}{q}$): the weight series of the former is
$t^q/q!$ times that of the latter (\lean{Fabius.bellWeightSeries_leadingZeros}),
and comparing the coefficients of $t^{n+qk}$ in the $k$th powers through
\cref{eq:partial-bell-egf} (\lean{Fabius.bellWeightSeries_pow}) gives the
factorial factor.""")),
]

PENDING += [
 # --- thm:merged-genocchi ---
 (r"""$t$ gives the second equality.  Parity and initial values follow immediately.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
Module \lean{GenocchiNumbers} takes the first equality of
\cref{eq:merged-genocchi} as the definition, \lean{Fabius.genocchi}
$=2(1-2^n)\beta_n$, and proves the defining generating function
\cref{eq:merged-genocchi-egf} as \lean{Fabius.egf_genocchi_mul_exp_add_one},
$\bigl(\sum_n\GenocchiNumber{n}t^n/n!\bigr)(\EulerE^t+1)=2t$ over any
$\RationalNumbers$-algebra, by exactly the displayed partial-fraction
identity: the series is $2\mathscr B(t)-2\mathscr B(2t)$
(\lean{Fabius.egf_genocchi_eq}), and Mathlib's
\lean{bernoulliPowerSeries_mul_exp_sub_one} rescaled to $2t$ gives
$(\sum_n\GenocchiNumber{n}t^n/n!)(\EulerE^t+1)(\EulerE^t-1)=2t(\EulerE^t-1)$,
after which $\EulerE^t-1=t\cdot(\text{unit})$ is cancelled.  The parity
statement is \lean{Fabius.genocchi_odd} and the initial values are
\lean{Fabius.genocchi_one} and \lean{Fabius.genocchi_two}; the Euler-polynomial
equality $\GenocchiNumber{n+1}=(n+1)\mathsf E_n(0)$ is \lean{Fabius.genocchi_succ_eq}
(module \lean{EulerPolynomials}), from the two generating functions.""")),
]

PENDING += [
 # --- thm:eulerian-alternating ---
 (r"""sides vanish, and for even $n$ the signs coincide.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the formal proof avoids $\tanh$ as a
% function and works with the Bernoulli generating function.
\cref{eq:eulerian-alternating} is \lean{Fabius.sum_neg_one_pow_mul_eulerianNumber}
(module \lean{EulerianAlternating}), for $n\ge1$.  Evaluating the Eulerian
generating function \cref{thm:eulerian-egf} at $t=-1$ gives
$E(x)(1+\EulerE^{-2x})=2$ for $E(x)=\sum_n\TypeAEulerianPolynomial{n}(-1)x^n/n!$
(\lean{Fabius.egfA_eulerianPolynomial_eval_neg_one_mul}); with
$\mathscr B(t)=t/(\EulerE^t-1)$ one has
$\mathscr B(4x)(\EulerE^{2x}+1)=2\mathscr B(2x)$
(\lean{Fabius.rescale_four_bernoulli_mul}), hence
$xE(x)=2x-\mathscr B(2x)+\mathscr B(4x)$
(\lean{Fabius.X_mul_egfA_eulerianPolynomial_eval_neg_one}), which is the
displayed expansion of $\tanh x$; comparing the coefficients of $x^{n+1}$
gives the formula.  The two reciprocal-binomial identities are not
formalized.""")),
]

PENDING += [
 # --- thm:merged-bernoulli-euler-basic ---
 (r"""forces every odd $\beta_n$ beyond $\beta_1$ to vanish.  Euler reflection at
$x=1/2$ proves the last assertion.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
For the Bernoulli polynomials the difference identity
\cref{eq:merged-bernoulli-difference} is Mathlib's
\lean{Polynomial.bernoulli_eval_one_add}, the reflection
\cref{eq:merged-bernoulli-reflection} is \lean{Polynomial.bernoulli_eval_one_sub},
and $\beta_{2m+1}=0$ is \lean{bernoulli_eq_zero_of_odd}.  For the Euler
polynomials of module \lean{EulerPolynomials} (defined by
\lean{Fabius.eulerPolynomial}, $\mathsf E_n(x)=\sum_k\binom nk\mathsf E_k(0)x^{n-k}$
with $\mathsf E_k(0)$ the coefficients of $2/(\EulerE^t+1)$), the difference
identity \cref{eq:merged-euler-difference} is
\lean{Fabius.eulerPolynomial_eval_add_one_add}, proved as in the text by
comparing the coefficients of $(\EulerE^t+1)\sum_n\mathsf E_n(x)t^n/n!=2\EulerE^{xt}$
(\lean{Fabius.sum_choose_mul_eulerPolynomial_add}) and translating
(\lean{Fabius.eulerPolynomial_eval_add}).  The Euler reflection
\cref{eq:merged-euler-reflection} is \lean{Fabius.eulerPolynomial_eval_one_sub}
(module \lean{EulerReflection}), proved as in the text: the substitutions
$x\mapsto1-x$ and $t\mapsto-t$ turn the generating-function identity into the
same identity $F\,(\EulerE^t+1)=2\EulerE^t\EulerE^{-xt}$, and the unit
$\EulerE^t+1$ is cancelled; $\mathsf E_{2m+1}(1/2)=0$ is
\lean{Fabius.eulerPolynomial_eval_half_odd}.""")),

 # --- thm:merged-alternating-sums ---
 (r"""interior Euler terms cancel in pairs, leaving the two endpoints.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\lean{Fabius.sum_neg_one_pow_mul_pow_eq_eulerPolynomial} (module
\lean{EulerPolynomials}) is \cref{eq:merged-alternating-sums} in the form
$\sum_{j=0}^{N-1}(-1)^j(x+j)^p=\bigl(\mathsf E_p(x)-(-1)^N\mathsf E_p(x+N)\bigr)/2$,
which agrees with the displayed formula for $N\ge1$ and gives $0$ for $N=0$;
the formal proof is the induction on $N$ from the difference identity
\lean{Fabius.eulerPolynomial_eval_add_one_add}.""")),
]

PENDING += [
 # --- thm:merged-faulhaber ---
 (r"""Apply \eqref{eq:merged-bernoulli-difference} to $\beta_{p+1}(x+j)$ and sum;
the left side telescopes.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01.
\lean{Fabius.sum_range_add_pow_eq_bernoulli_sub} (module \lean{FaulhaberOffset})
is \cref{eq:merged-faulhaber} for all $N\ge0$ and rational $x$, proved by
exactly this telescoping, with the difference identity taken from Mathlib
(\lean{Polynomial.bernoulli_eval_one_add}); the case $x=0$ is also Mathlib's
\lean{Polynomial.sum_range_pow_eq_bernoulli_sub}.""")),
]

PENDING += [
 # --- thm:merged-raabe ---
 (r"""Coefficient comparison gives the multiplication formula.  Set $q=2,x=0$ and
solve for the half-value.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof is this proof made formal.
\lean{Fabius.raabe} (module \lean{RaabeMultiplication}) is
\cref{eq:merged-raabe}, written $\sum_{r<q}\beta_n(x+r/q)=q\,(1/q)^n\beta_n(qx)$
for $q\ge1$ and rational $x$.  In $(\RationalNumbers[x])[[t]]$, Mathlib's
\lean{Polynomial.bernoulli_generating_function} gives
$B(a;t)(\EulerE^t-1)=t\EulerE^{at}$ for polynomial arguments $a$
(\lean{Fabius.bernoulliPolySeriesAt_mul_exp_sub_one}); summing over
$a=x+r/q$ and using the finite geometric sum
$\bigl(\sum_{r<q}\EulerE^{rt/q}\bigr)(\EulerE^{t/q}-1)=\EulerE^t-1$
(\lean{Fabius.sum_pow_mul_sub_one}) gives $G(t)(\EulerE^{t/q}-1)=t\EulerE^{xt}$
for the left side; rescaling $B(qx;t)$ by $t\mapsto t/q$
(\lean{Fabius.rescale_expSeries}) gives the same identity for the right side;
and $\EulerE^{t/q}-1$ is $t$ times a unit, which is cancelled.
\cref{eq:merged-bernoulli-half} is \lean{Fabius.bernoulli_eval_half}.""")),
]

PENDING += [
 # --- thm:touchard-poly ---
 (r"""same number of blocks, contributing $\TouchardPolynomial{n+1}(x)$.  This proves the polynomial
congruence; set $x=1$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the formal proof is arithmetic, not the
% group action above.
\cref{eq:touchard-poly} is \lean{Fabius.touchardPolynomial_add_prime} (module
\lean{TouchardPolyCongruence}), an identity
$\TouchardPolynomial{n+p}=\TouchardPolynomial{n+1}+x^p\TouchardPolynomial{n}$
in $(\mathbb Z/p)[x]$ for every prime $p$, and \cref{eq:touchard} is
\lean{Fabius.bell_add_prime_modEq} (module \lean{TouchardCongruence}).  Both
Lean proofs read Spivey's identity (\cref{thm:spivey}; for Touchard
polynomials \lean{Fabius.spivey_touchard}, transported from
$\RationalNumbers[x]$ to every coefficient ring as
\lean{Fabius.touchardPolynomial_add_eq}) with $m=p$ modulo $p$: the Stirling
numbers $\StirlingSecondKind pj$ with $1<j<p$ vanish modulo $p$
(\lean{Fabius.stirlingSecond_prime_eq_zero_zmod}, from the surjection formula
\cref{thm:second-explicit} and Fermat's little theorem), the term $j=1$ is the
Touchard recurrence $x\sum_k\binom nk\TouchardPolynomial{k}=\TouchardPolynomial{n+1}$,
and in the term $j=p$ only $k=n$ survives because $p^{n-k}\equiv0$ for
$k<n$.""")),
]

PENDING += [
 # --- thm:typeB-eulerian ---
 (r"""\eqref{eq:typeB-power-series}.  Multiplication by $(1-t)^{n+1}$ and coefficient
extraction gives \eqref{eq:typeB-explicit}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; Lean takes the recurrence as the definition.
Module \lean{TypeBEulerian} defines \lean{Fabius.typeBEulerian} by the
recurrence \cref{eq:typeB-recurrence}; the signed-permutation count is not
formalized.  The type-$B$ Worpitzky identity
$(2m+1)^n=\sum_k\TypeBEulerianNumber nk\binom{m+n-k}{n}$ is
\lean{Fabius.typeB_worpitzky}, proved by induction on $n$ from the one-step
relation $(2m+1)\binom{m+n-k}{n}=(2k+1)\binom{m+n+1-k}{n+1}
+(2n-2k+1)\binom{m+n-k}{n+1}$ (\lean{Fabius.two_mul_add_one_mul_choose});
\cref{eq:typeB-power-series} is \lean{Fabius.one_sub_X_pow_mul_oddPowSeries},
in $R[[t]]$ over any commutative ring, exactly as in the text; and
\cref{eq:typeB-explicit} is its $k$-th coefficient,
\lean{Fabius.typeBEulerian_eq_sum_int}.""")),
]

PENDING += [
 # --- thm:second-eulerian-recurrence ---
 (r"""against $t^k$ gives the second.  At each stage there are $2n-1$ insertion gaps, so
the total count is $(2n-1)!!$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; Lean takes the recurrence as the definition.
Module \lean{SecondOrderEulerian} defines \lean{Fabius.secondEulerian} by the
recurrence \cref{eq:second-eulerian-recurrence} (in the form
$\SecondOrderEulerianNumber{n+1}{k+1}=(2n-k)\SecondOrderEulerianNumber nk
+(k+2)\SecondOrderEulerianNumber n{k+1}$); the Stirling-permutation count is
not formalized.  The polynomial recurrence
\cref{eq:second-eulerian-poly-recurrence} is
\lean{Fabius.secondEulerianSeries_succ}, an identity of formal power series
in $t$ over any commutative ring, proved by comparing coefficients; the row
sum \cref{eq:second-eulerian-row-sum} is
\lean{Fabius.sum_secondEulerian_eq_doubleFactorial}, by induction from the
recurrence.""")),

 # --- thm:second-eulerian-stirling-gf ---
 (r"""$t\SecondOrderEulerianPolynomial{n}/(1-t)^{2n+1}$ and using
\eqref{eq:second-eulerian-poly-recurrence} gives the formula for $n+1$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof is this proof made formal.
\lean{Fabius.one_sub_X_pow_mul_diagStirlingSeries} (module
\lean{SecondOrderEulerian}) is \cref{eq:second-eulerian-stirling-gf} in the
form $(1-t)^{2n+1}\sum_m\StirlingSecondKind{n+m}{m}t^m=t\SecondOrderEulerianPolynomial{n}(t)$
in $R[[t]]$ over any commutative ring, for $n\ge1$: the base case is
$F_1=t/(1-t)^3$ (\lean{Fabius.diagStirlingSeries_one}), the recurrence
$(1-t)F_{n+1}=tF_n'$ is \lean{Fabius.one_sub_X_mul_diagStirlingSeries_succ},
and the induction step differentiates the hypothesis and uses
\cref{eq:second-eulerian-poly-recurrence}.""")),
]

PENDING += [
 # --- thm:bell-prime-power-shift ---
 (r"""$x^{p^r}\equiv x$ modulo $p$ at $x=1$ gives
\eqref{eq:bell-prime-power-shift}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof runs through the shift operator rather than the group action.
\lean{Fabius.bell_add_prime_pow_modEq} (module \lean{ShiftOperatorCharP}) is
\cref{eq:bell-prime-power-shift} as a congruence of natural numbers, and
\lean{Fabius.touchardPolynomial_add_prime_pow} is
\cref{eq:touchard-prime-power-poly} as an identity in $\FiniteField_p[x]$.
The formal proof does not use the group action above.  It takes Touchard's
congruence in the operator form $E^p=E+c$, with $c=1$ for the Bell numbers
and $c=x^p$ for the Touchard polynomials (the latter from
\lean{Fabius.touchardPolynomial_add_prime}), and shows by induction on $m$,
using the Frobenius identity $(u+v)^p=u^p+v^p$ in characteristic $p$, that
$Y^{p^m}\equiv Y+\sum_{r<m}c^{p^r}$ modulo the polynomial $Y^p-Y-c$
(\lean{Fabius.mk_X_pow_prime_pow}).  Since the shift $E$ acts linearly on
sequences, every polynomial multiple of the characteristic polynomial
annihilates every solution of the recurrence
(\lean{Fabius.aeval_shiftEnd_eq_zero_of_dvd}), which gives the general
statement \lean{Fabius.shift_pow_char_pow}: if $b_{n+p}=b_{n+1}+cb_n$ in a
commutative ring of characteristic $p$, then
$b_{n+p^m}=b_{n+1}+\bigl(\sum_{r=0}^{m-1}c^{p^r}\bigr)b_n$.""")),

 # --- thm:bell-period-bound ---
 (r"""recurrence, in particular on the Bell sequence.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof avoids the splitting field.
\lean{Fabius.bell_add_sum_prime_pow_modEq} (module \lean{ShiftOperatorCharP})
states that $N_p=\sum_{j<p}p^j$ is a period,
$\BellNumber{n+N_p}\equiv\BellNumber n\pmod p$ for every $n\ge0$, and
\lean{Fabius.bell_period_dvd_sum_prime_pow} that the least positive period
divides $N_p$ (by the general division argument
\lean{Fabius.period_dvd_of_minimal}).  The formal proof stays in
$\FiniteField_p[Y]$: from $Y^{p^j}\equiv Y+j$ modulo $q(Y)=Y^p-Y-1$
(\lean{Fabius.mk_X_pow_prime_pow}) and the Fermat product
$\prod_{j=0}^{p-1}(Y+j)=Y^p-Y$ (\lean{Fabius.prod_range_X_add_C_natCast}, from
the factorization of $Y^p-Y$ over $\FiniteField_p$,
\lean{Fabius.prod_univ_X_sub_C}) one gets $Y^{N_p}\equiv Y^p-Y=q(Y)+1\equiv1$,
so $q(Y)$ divides $Y^{N_p}-1$, and the shift-operator transfer
\lean{Fabius.aeval_shiftEnd_eq_zero_of_dvd} yields $E^{N_p}=1$ on every
solution of the recurrence over $\FiniteField_p$
(\lean{Fabius.shift_pow_period}); no diagonalization is needed.""")),
]

PENDING += [
 # --- thm:weighted-bell-shift ---
 (r"""after $m=r+k$.  The special cases follow by setting $k=1$, and then $a=1,b=k$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-01; the Lean proof is algebraic, without Dobiński's series.
\lean{Fabius.weighted_bell_shift} (module \lean{BellUmbra}) is
\cref{eq:weighted-bell-shift}, \lean{Fabius.weighted_bell_shift_one} is
\cref{eq:weighted-bell-k1} and \lean{Fabius.sum_signedStirlingFirst_mul_bell_eq}
is \cref{eq:weighted-bell-special}, with $a,b$ in an arbitrary commutative
ring and $(-1)^{k-i}\UnsignedStirlingFirstKind ki$ as the signed number
\lean{Fabius.signedStirlingFirst}.  The formal proof replaces the Poisson sum
by the Bell umbra, the linear functional $L$ on $R[x]$ with $L(x^n)=\BellNumber n$
(\lean{Fabius.bellUmbra}): the binomial recurrence
\cref{eq:bell-binomial-recurrence} says $L(xf(x))=L(f(x+1))$
(\lean{Fabius.bellUmbra_X_mul}), induction on $k$ with
$\FallingFactorial{x}{k+1}=x\,\FallingFactorial{x-1}{k}$ gives the umbral
shift $L(\FallingFactorial xk f(x))=L(f(x+k))$
(\lean{Fabius.bellUmbra_descPochhammer_mul}), and applying it to
$f(x)=(ax+b-ak)^n$ gives $L((ax+b)^n)$ on the left, which is the binomial
expansion of \cref{eq:weighted-bell-shift}.  In particular all factorial
moments of the Bell umbra are $1$ (\lean{Fabius.bellUmbra_descPochhammer}).""")),
]

PENDING += [
 # --- thm:second-parity ---
 (r"""condition is the same.  Powers of two are the $n$ with a single $1$-bit, a strictly
smaller class.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the Lean proof is the reduction of the column series modulo 2.
\lean{Fabius.stirlingSecond_modEq_choose_two} (module \lean{StirlingParity})
is \cref{eq:second-parity-binomial} for $1\le k\le n$, as the congruence
$\StirlingSecondKind nk\equiv\binom{n-\lfloor(k+2)/2\rfloor}{\lfloor(k-1)/2\rfloor}\pmod2$
of natural numbers (note $\Ceiling{(k+1)/2}=\lfloor(k+2)/2\rfloor$).  The
formal proof is the one above: over $\FiniteField_2$ the product
$\prod_{j=1}^{k}(1-jt)$ equals $(1-t)^{\lceil k/2\rceil}$
(\lean{Fabius.prod_one_sub_mul_X_zmod_two}, by induction on $k$ with the
parity of the new factor), so the column series of \cref{eq:second-ogf}
becomes $(1-t)^{-\lceil k/2\rceil}$ (\lean{Fabius.stirlingColumnOGF_zmod_two})
and its coefficients are the binomial coefficients
(\lean{Fabius.stirlingSecond_add_zmod_two}).  The bitwise form
\cref{eq:second-parity-bit} is \lean{Fabius.stirlingSecond_odd_iff} and the central case
is \lean{Fabius.stirlingSecond_two_mul_odd_iff} (module \lean{StirlingParityBitwise}).
Both rest on Kummer's theorem at the prime two, \lean{Fabius.odd_choose_add_iff}: the
coefficient $\binom{w+d}{w}$ is odd exactly when $w\BitwiseAnd d=0$.  Mathlib has
Lucas's theorem but not this consequence, so it is proved in that module by induction on
the binary digits, the digit factor of Lucas being $1$ in the three cases where the
lowest digits of $w$ and $d$ do not collide and $0$ in the one case where they do.  The
central case is where the corrected form of the statement matters: the $n$ for which
$\StirlingSecondKind{2n}{n}$ is odd are those with no two adjacent $1$-bits, and
\lean{Fabius.land_pred_div_two_iff} is the step that turns the criterion
$n\BitwiseAnd\Floor{(n-1)/2}=0$ into that condition.""")),
]

PENDING += [
 # --- thm:merged-catalan-reflection ---
 (r"""Subtraction and simplification prove the formula.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02.
Mathlib defines the Catalan numbers by the first-return recurrence
$\CatalanNumber{n+1}=\sum_{i+j=n}\CatalanNumber i\CatalanNumber j$ and proves
that they count Dyck words of semilength $n$
(\lean{DyckWord.card_dyckWord_semilength_eq_catalan}, through the bijection
with binary trees) and that $\CatalanNumber n=\binom{2n}{n}/(n+1)$
(\lean{catalan_eq_centralBinom_div}, \lean{succ_mul_catalan_eq_centralBinom}).
The difference form of \cref{eq:merged-catalan-reflection} is
\lean{Fabius.catalan_succ_eq_choose_sub_choose} (module
\lean{CatalanGeneratingFunction}), for $n+1$ so that no negative lower index
occurs, derived algebraically from $(n+2)\CatalanNumber{n+1}=\binom{2n+2}{n+1}$
and $\binom{2n+2}{n+1}(n+1)=\binom{2n+2}{n}(n+2)$; the reflection bijection
itself is not formalized.""")),

 # --- thm:merged-catalan-first-return ---
 (r"""equation.  Of the two quadratic roots, only the displayed branch has constant
term $1$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02.
\lean{Fabius.catalanSeries_eq} (module \lean{CatalanGeneratingFunction}) is
$C(z)=1+zC(z)^2$ in $R[[z]]$ over any commutative ring, read off from
Mathlib's recurrence \lean{catalan_succ'} by coefficient comparison, and
\lean{Fabius.eq_catalanSeries_of_eq_one_add_X_mul_sq} is the uniqueness
statement behind the choice of branch: every power series $F$ with
$F=1+zF^2$ equals $C(z)$, since the equation determines each coefficient from
the earlier ones.  The closed form with $\sqrt{1-4z}$ is not formalized.""")),
]

PENDING += [
 # --- thm:first-reverse-recurrences ---
 (r"""which follows immediately from the displayed formula for $C_k$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; both formal proofs follow the text.
\cref{eq:first-reverse-row} is \lean{Fabius.first_reverse_row} (module
\lean{StirlingFirstReverse}), with the summation index written as $j=i+2$,
$0\le i<n-k$, and $(-1)^j\binom{-k}{j}$ replaced by $\binom{k+j-1}{j}$: the
coefficient identity
$\UnsignedStirlingFirstKind{n+1}{k+1}=\sum_r\binom rk\UnsignedStirlingFirstKind nr$
is \lean{Fabius.stirlingFirst_succ_succ_eq_sum_choose} (module
\lean{StirlingBasisChange}), from
$\RisingFactorial{x}{n+1}=x\,\RisingFactorial{x+1}{n}$
(Mathlib's \lean{ascPochhammer_succ_left}), and removing the terms $r=k-1,k$
gives the recurrence.  \cref{eq:first-reverse-column} is
\lean{Fabius.first_reverse_column}, stated as
$(n-k)\UnsignedStirlingFirstKind nk=\sum_{j=2}^{n}\binom nj(j-2)!\,\UnsignedStirlingFirstKind{n-j+1}{k}$
(the extra terms vanish); the formal proof compares exponential generating
functions over a $\mathbb Q$-algebra exactly as in the text:
\lean{Fabius.egfA_kernel} is $\sum_{j\ge2}x^j/(j(j-1))=x+(1-x)\log(1-x)$,
\lean{Fabius.one_sub_X_mul_negLog_mul_derivative_egfA_stirlingFirst} is
$-(1-x)\log(1-x)\,C_k'=kC_k$, and \lean{Fabius.egfA_first_reverse_column}
is the resulting identity $xC_k'-kC_k=\bigl(x+(1-x)\log(1-x)\bigr)C_k'$,
from which \lean{Fabius.seq_eq_of_egfA_eq} extracts the coefficients.""")),
]

PENDING += [
 # --- thm:merged-bernoulli-difference ---
 (r"""yields \eqref{eq:merged-bernoulli-newton-basis}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the Lean proof follows the text, with the composition truncated.
\lean{Fabius.bernoulli_eq_sum_fwdDiff} (module \lean{BernoulliNewtonBasis}) is
\cref{eq:merged-bernoulli-newton-basis} as an identity in $\mathbb Q[x]$,
with $\Delta^kx^n$ written out as $\sum_{j=0}^k(-1)^{k-j}\binom kj(x+j)^n$.
The formal proof works in $\mathbb Q[x][[t]]$: Mathlib's
\lean{Polynomial.bernoulli_generating_function} and
\lean{bernoulliPowerSeries_mul_exp_sub_one} give
$\sum_n\beta_n(x)t^n/n!=\EulerE^{xt}\cdot t/(\EulerE^t-1)$
(\lean{Fabius.bernoulliPolySeries_eq}), the composition
\cref{eq:merged-gregory-composition} is used only through its truncation
$t/(\EulerE^t-1)\equiv\sum_{k\le n}\frac{(-1)^k}{k+1}(\EulerE^t-1)^k$ modulo
$t^{n+1}$ (\lean{Fabius.X_pow_dvd_bernoulliPowerSeries_sub_gregory}, whose
coefficients are compared through the Bernoulli--Stirling formula
\lean{Fabius.bernoulli_eq_sum_stirlingSecond} and
$(\EulerE^t-1)^k=k!\sum_nS(n,k)t^n/n!$), and
$\EulerE^{xt}(\EulerE^t-1)^k=\sum_j(-1)^{k-j}\binom kj\EulerE^{(x+j)t}$ is the
binomial theorem for Mathlib's \lean{PowerSeries.exp_mul_exp_eq_exp_add}.""")),

 # --- cor:merged-bernoulli-stirling-second-proof ---
 (r"""which is \eqref{eq:merged-bernoulli-stirling}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02.
\lean{Fabius.bernoulli_eq_sum_fwdDiff_zero} (module \lean{BernoulliNewtonBasis})
is the evaluation at $x=0$,
$\beta_n=\sum_{k\le n}\frac{(-1)^k}{k+1}\sum_{j\le k}(-1)^{k-j}\binom kjj^n$,
and the surjection formula $\Delta^k0^n=k!\StirlingSecondKind nk$ is
\lean{Fabius.factorial_mul_stirlingSecond_eq_sum}, so that the two together
are \lean{Fabius.bernoulli_eq_sum_stirlingSecond}.  (In the formal development
the Newton-basis identity itself is derived through the Bernoulli--Stirling
formula, so it is not an independent second proof there.)""")),
]

PENDING += [
 # --- thm:merged-norlund-calculus ---
 (r"""functions of orders $\alpha$ and $\gamma$ proves the convolution identity.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; natural orders only.
Module \lean{NorlundPolynomials} defines $\beta_n^{(a)}(x)$ for natural
orders $a\in\mathbb N$ by \cref{eq:merged-norlund-egf} with the $a$-th power
of Mathlib's \lean{bernoulliPowerSeries} (\lean{Fabius.norlund}), so that
$\beta_n^{(0)}=x^n$ and $\beta_n^{(1)}=\beta_n$ (\lean{Fabius.norlund_zero},
\lean{Fabius.norlund_one}).  For $a,c\in\mathbb N$ and rational $x,y$:
\cref{eq:merged-norlund-appell} is \lean{Fabius.derivative_norlund_succ},
proved by differentiating the coefficients of $G(t)\EulerE^{xt}$ in $x$
(\lean{Fabius.derivative_coeff_succ_map_C_mul_rescale_exp});
\cref{eq:merged-norlund-convolution} is \lean{Fabius.norlund_add_eval_add},
from the product of the two exponential generating functions
(\lean{Fabius.egfA_norlund_eval}, \lean{Fabius.egfA_mul});
\cref{eq:merged-norlund-translation} is its case $\gamma=0$
(\lean{Fabius.norlund_eval_add}); and \cref{eq:merged-norlund-difference} is
\lean{Fabius.norlund_succ_eval_add_one_sub}, from
$(\EulerE^{(x+1)t}-\EulerE^{xt})\,t/(\EulerE^t-1)=t\EulerE^{xt}$.  Complex
orders, which need $\exp(\alpha\log(t/(\EulerE^t-1)))$, are not formalized.""")),
]

PENDING += [
 # --- thm:bell-poly-derivatives ---
 (r"""gives \eqref{eq:complete-bell-derivative}.  The ordinary chain rule then gives
\eqref{eq:bell-poly-chain}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the Lean proof differentiates the column theorem coefficientwise.
\lean{Fabius.pderiv_partialBell_succ} (module \lean{BellDerivative}) is
\cref{eq:partial-bell-derivative} and \lean{Fabius.pderiv_bellComplete} is
\cref{eq:complete-bell-derivative}, both as identities in the polynomial ring
$\mathbb Q[x_1,x_2,\dots]$ with Mathlib's partial derivative
\lean{MvPolynomial.pderiv}, for $i\ge1$ and $k\ge1$ (for $k=0$ the derivative
vanishes, \lean{Fabius.pderiv_partialBell_zero}).  The formal proof is the one
above: a derivation of the coefficient ring acts coefficientwise on power
series and is again a derivation (\lean{Fabius.coeffDerivation}), so applying
$\partial/\partial x_i$ to the column theorem
\lean{Fabius.bellWeightSeries_pow} and using
$\partial X(t)/\partial x_i=t^i/i!$
(\lean{Fabius.coeffDerivation_pderiv_bellWeightSeries}) gives the identity by
coefficient comparison; the complete-polynomial form follows by summing over
$k$.  The chain rule \cref{eq:bell-poly-chain} is analytic and is not
formalized.""")),
]

PENDING += [
 # --- thm:merged-moment-cumulant ---
 (r"""partitions by block sizes is exactly the coefficient expansion of $\EulerE^K$ and
$\log M$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the formal statement is the block-size (Bell polynomial) form.
Module \lean{BellPolynomialInversion} defines the complete Bell polynomials
\lean{Bell.complete} by the recurrence $m_{n+1}=\sum_k\binom nk\kappa_{k+1}m_{n-k}$
(the sum over partitions grouped by the block containing $n+1$) and the
cumulant sequence \lean{Bell.cumulant} by the inverse recurrence, and proves
that the two constructions are mutually inverse
(\lean{Bell.complete_cumulant} for $m_0=1$, \lean{Bell.cumulant_complete}
for $\kappa_0=0$), over any commutative ring; the generating-function form
$M=\EulerE^K$ is \lean{Fabius.exp_subst_bellWeightSeries} (module
\lean{BellGeneratingFunctions}), where $K$ is the weight series
\lean{Fabius.bellWeightSeries}.  The sums over the partition lattice
\cref{eq:merged-moment-cumulant-forward,eq:merged-moment-cumulant-backward}
and the identity $K=\log M$ are not formalized.""")),
]

PENDING += [
 # --- thm:associated-stirling-recurrence ---
 (r"""power divided by $k!$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; Lean takes the weighted Bell polynomial as the definition.
Module \lean{AssociatedStirling} defines $\mathsf S_r(n,k)$ as the partial
Bell polynomial $\ExponentialPartialBellPolynomial nk$ with the weights
$x_j=[j\ge r]$ (\lean{Fabius.associatedStirling}); the count of partitions
with all blocks of size at least $r$ is not formalized.  With this definition
\cref{eq:associated-stirling-egf} is \lean{Fabius.egfA_associatedStirling},
immediate from the column theorem \lean{Fabius.bellWeightSeries_pow} once the
weight series is identified with $\EulerE^z-\sum_{j<r}z^j/j!$
(\lean{Fabius.bellWeightSeries_assocWeight}), and
\cref{eq:associated-stirling-recurrence} is
\lean{Fabius.associatedStirling_succ_succ}, obtained by differentiating the
generating function: $W'=W+z^{r-1}/(r-1)!$
(\lean{Fabius.derivative_bellWeightSeries_assocWeight}) gives
$F_k'=kF_k+F_{k-1}z^{r-1}/(r-1)!$ for $F_k=W^k/k!$, and the coefficient of
$z^n/n!$ is the recurrence.""")),
]

PENDING += [
 # --- thm:r-stirling-recurrence ---
 (r"""$1,\ldots,r$ is preserved in both constructions, and deletion of $n$ reverses
them.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; Lean takes the recurrence as the definition.
Module \lean{RStirling} defines $\StirlingSecondKind nk_{\!r}$ by the
recurrence \cref{eq:r-stirling-recurrence} with $\StirlingSecondKind rr_{\!r}=1$
and the zero boundary (\lean{Fabius.rStirling}, in the shifted indices
$T_r(n,k)=\StirlingSecondKind{n+r}{k+r}_{\!r}$ as \lean{Fabius.rStirlingShift});
the count of partitions with $1,\dots,r$ in distinct blocks is not
formalized.  The recurrence is \lean{Fabius.rStirling_succ_succ} (for
$n\ge r$).  Since the recurrence says that $n\mapsto T_r(n,k)$ is the binomial
convolution of $j\mapsto r^j$ with $j\mapsto\StirlingSecondKind jk$
(\lean{Fabius.rStirlingShift_eq_binomialConv}, by induction with the shift
rule \lean{Bell.binomialConv_succ}), one gets the explicit formula
$\StirlingSecondKind{n+r}{k+r}_{\!r}=\sum_j\binom nj\StirlingSecondKind jk r^{n-j}$
(\lean{Fabius.rStirlingShift_eq_sum}, \lean{Fabius.rStirling_eq_sum}), and the
mixed generating function \cref{eq:r-stirling-egf} follows from the product
rule for exponential generating functions:
\lean{Fabius.egfA_rStirlingPoly} is
$\sum_n\bigl(\sum_k\StirlingSecondKind{n+r}{k+r}_{\!r}y^k\bigr)z^n/n!
=\EulerE^{rz}\exp\bigl(y(\EulerE^z-1)\bigr)$ in $\mathbb Q[y][[z]]$, which is
\cref{eq:r-stirling-egf} after multiplication by $y^r$.""")),
]

PENDING += [
 # --- thm:merged-cauchy-polynomials ---
 (r""" &=(-1)^n\int_0^1\FallingFactorial{x+v}{n}\Differential v
 =(-1)^n b_n(x).
\end{align*}
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the algebraic identities are formal, the integral ones are not.
Module \lean{CauchyPolynomials} defines $b_n(x)$ directly by
\cref{eq:merged-bernoulli-second-egf}, as $n!$ times the $n$-th coefficient of
$t(1+t)^x/\log(1+t)$ in $\mathbb Q[x][[t]]$ (\lean{Fabius.cauchyPoly}), the
factor $t/\log(1+t)$ being the power-series inverse of the Gregory series
\lean{Fabius.logDivSeries}.  The supporting object is the falling-factorial
generating function $(1+t)^u=\sum_n\FallingFactorial un t^n/n!$ over any
$\mathbb Q$-algebra (\lean{Fabius.fallingSeries}, module
\lean{FallingFactorialSeries}), characterised by $(1+t)F'=uF$ with $F(0)=1$;
from that characterisation one gets the product law
$(1+t)^u(1+t)^v=(1+t)^{u+v}$ (\lean{Fabius.fallingSeries_mul}), hence the
Vandermonde identity for falling factorials
(\lean{Fabius.descPochhammer_eval_add}), and, in $\mathbb Q[x][[t]]$, the
$x$-derivative $\partial_x(1+t)^x=\log(1+t)\,(1+t)^x$
(\lean{Fabius.Dx_fallingPoly}, with $\partial_x$ the coefficientwise
derivative \lean{Fabius.Dx}).
Consequently \cref{eq:merged-cauchy-derivative} is
\lean{Fabius.derivative_cauchyPoly_succ}, \cref{eq:merged-cauchy-difference}
is \lean{Fabius.cauchyPoly_succ_eval_add_one_sub},
\cref{eq:merged-cauchy-addition} is \lean{Fabius.cauchyPoly_eval_add} and
\cref{eq:merged-cauchy-explicit} is \lean{Fabius.cauchyPoly_succ_eq}.
\cref{eq:merged-cauchy-stirling-numbers} is \lean{Fabius.cauchyPoly_eval_zero},
proved with the formal integral $\int_0^1p(u)\Differential u=\sum_kp_k/(k+1)$
as a linear functional on $\mathbb Q[u]$ (\lean{Fabius.intPoly}), for which
$\int_0^1p'=p(1)-p(0)$ (\lean{Fabius.intPoly_derivative}); applying it
coefficientwise to $\partial_x(1+t)^x$ gives
$\int_0^1(1+t)^u\Differential u=t/\log(1+t)$
(\lean{Fabius.mapIntPoly_fallingPoly}), which is
\cref{eq:merged-cauchy-integral} in formal form, although the analytic
integral representation itself is not formalized.  The reflection
\cref{eq:merged-cauchy-reflection} is not formalized.""")),
]

PENDING += [
 # --- lem:coeff-rules ---
 (r"""bound follows by estimating the contour integral by its length $2\pi r$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the three formal rules are Lean, the analytic one is not.
Module \lean{CoefficientRules} proves the three formal rules over an arbitrary
commutative ring: \cref{eq:cauchy} is
\lean{Fabius.coeff_mul_eq_sum_range}, \cref{eq:der-coeff} is
\lean{Fabius.coeff_derivative_eq}, and \cref{eq:geom-conv} is
\lean{Fabius.coeff_mul_geomSeries}, where $F/(1-az)$ is read as
$F\cdot\sum_na^nz^n$; that the geometric series really is the reciprocal of
$1-az$ is \lean{Fabius.one_sub_C_mul_X_mul_geomSeries}, and
\lean{Fabius.eq_mul_geomSeries_iff} lets the same rule be applied
to a series presented by the equation $(1-az)G=F$, which is how it is used in
the Stirling column arguments.  The analytic Cauchy coefficient formula and
bound \cref{eq:cauchy-coeff} are not formalized.""")),

 # --- thm:merged-multinomial-leibniz ---
 (r"""$\prod_r f_r^{(j_r)}(x)/j_r!$.  Multiplication by $n!$ proves
\eqref{eq:merged-multinomial-leibniz}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; two factors only, in the formal reading.
The proof above offers two readings, analytic near $x$ and formal in a new
variable $h$; the formal one is the one that is formalized, and only for two
factors.  \lean{Fabius.derivative_iterate_mul} (module \lean{IteratedLeibniz})
is $(\Differential/\Differential t)^n(fg)=\sum_{k=0}^n\binom nk
f^{(k)}g^{(n-k)}$ for formal power series over any commutative ring, proved by
induction on $n$ from Pascal's rule in convolution form
(\lean{Fabius.sum_pascal_split}, stated for an arbitrary sequence and reusable
for any binomial-type two-term recurrence).  The general $q$-factor form
\cref{eq:merged-multinomial-leibniz}, whose index set is the compositions of
$n$ into $q$ parts, is not formalized.""")),
]

PENDING += [
 # --- thm:merged-norlund-bell-diagonal ---
 (r"""The middle equality is \cref{thm:res-subst}.  Multiplication by $n!$ proves
the polynomial diagonal.  Replace $n$ by $n-1$ and set $x=0$ to obtain the
number diagonal; division by $(n-1)!$ gives the coefficient identity.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the Lean proof avoids residues entirely.
Module \lean{NorlundDiagonal} formalizes the three diagonal displays for
natural orders: \cref{eq:merged-norlund-polynomial-diagonal} is
\lean{Fabius.norlund_diagonal}, in the form
$\beta_n^{(n+1)}(x)=\FallingFactorial{x-1}{n}$ with Mathlib's
\lean{descPochhammer}; \cref{eq:merged-norlund-number-diagonal} is
\lean{Fabius.norlund_eval_zero_diagonal}; and
\cref{eq:merged-norlund-diagonal} is
\lean{Fabius.coeff_bernoulliPowerSeries_pow_succ}.
The formal proof does not use \cref{thm:res-subst}, and needs no residue
calculus.  It rests instead on the Riccati equation
$t\,\frac{\Differential}{\Differential t}\!\left(\frac{t}{\EulerE^t-1}\right)
=\frac{t}{\EulerE^t-1}-\left(\frac{t}{\EulerE^t-1}\right)^2-\frac{t^2}{\EulerE^t-1}$
(\lean{Fabius.X_mul_derivative_bernoulliPowerSeries}, obtained by
differentiating $B(\EulerE^t-1)=t$), which converts into the order-lowering
relation
$(a+1)\beta_{n+1}^{(a+2)}(x+1)=(a-n)\beta_{n+1}^{(a+1)}(x)+(n+1)x\beta_n^{(a+1)}(x)$
(\lean{Fabius.norlund_series_step} as generating functions,
\lean{Fabius.norlund_step} coefficientwise).  Taking $a=n$ annihilates the
first term and leaves $\beta_{n+1}^{(n+2)}(x+1)=x\beta_n^{(n+1)}(x)$
(\lean{Fabius.norlund_diagonal_step}); induction on $n$ against
$\FallingFactorial{x-1}{n+1}=(x-1)\FallingFactorial{x-2}{n}$ then gives the
closed form, and $x=0$ with
$\FallingFactorial{-1}{n}=(-1)^nn!$ (\lean{Fabius.descPochhammer_eval_neg_one})
gives the other two.  Complex orders are not formalized, nor is the
Bell-polynomial construction
\cref{eq:merged-norlund-bell,eq:merged-norlund-bell-explicit}.""")),
]

PENDING += [
 # --- thm:merged-narayana ---
 (r"""Setting $u=1$ gives the Catalan equation, and the closed formula is symmetric
under $k\leftrightarrow n+1-k$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; Lean takes the determinant form as the definition.
Module \lean{NarayanaNumbers} defines $N(n,k)$ over $\IntegerNumbers$ by the
division-free determinant
$\binom nk\binom{n-1}{k-1}-\binom n{k-1}\binom{n-1}k$
(\lean{Fabius.narayana}).  That shape is chosen so that no side condition is
needed: it vanishes identically outside $1\le k\le n$, whereas the quotient
$\frac1n\binom nk\binom n{k-1}$ read with truncated subtraction would give
$N(1,0)=1$ and poison both the symmetry and the row sum.
\cref{eq:merged-narayana} is then \lean{Fabius.narayana_mul} in the cleared
form $nN(n,k)=\binom nk\binom n{k-1}$, proved from
$k\binom nk=(n-k+1)\binom n{k-1}$ and $n\binom{n-1}k=(n-k)\binom nk$;
the symmetry $N(n,k)=N(n,n+1-k)$ is \lean{Fabius.narayana_symm}, obtained by
cancelling $n$ against that cleared form; and
$\sum_kN(n,k)=\CatalanNumber n$ is \lean{Fabius.sum_narayana}, from
Vandermonde's identity in the form
$\sum_j\binom nj\binom n{j+1}=\binom{2n}{n-1}$
(\lean{Fabius.sum_choose_mul_choose_succ}) together with
$n\CatalanNumber n=\binom{2n}{n-1}$ (\lean{Fabius.succ_mul_catalan_succ}).
The peak-counting interpretation and the bivariate generating function
\cref{eq:merged-narayana-gf}, which the proof above obtains by Lagrange
inversion, are not formalized.""")),

 # --- thm:mod-h-structure ---
 (r"""by the archived formula involving unspecified roots $\omega_{h,i}$ and polynomials
$p_{h,i}^{[m]}$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; part A is Lean, and the vanishing above is now a theorem.
\lean{Fabius.stirlingFirst_cast_eq_coeff_block} (module \lean{StirlingFirstModH})
is \cref{eq:mod-h-block-product}: with $n=qh+s$,
$\UnsignedStirlingFirstKind nm\equiv[x^m]\bigl(\prod_{r<h}(x+r)\bigr)^q\prod_{r<s}(x+r)$
modulo $h$.  It follows from the product form of the rising factorial,
$\RisingFactorial xn=\prod_{j<n}(x+j)$
(\lean{Fabius.ascPochhammer_eq_prod_range}, which the corpus previously had only
in evaluated form), by splitting the product into $q$ blocks of length $h$ and
reducing each index modulo $h$.
The editorial remark below is also a theorem:
\lean{Fabius.stirlingFirst_cast_eq_zero_of_lt} proves that
$\UnsignedStirlingFirstKind{qh+s}{m}\equiv0\pmod h$ whenever $m<q$, because the
block polynomial has constant term $\prod_{r<h}r=0$ in
$\IntegerNumbers/h\IntegerNumbers$, so $x^q$ divides its $q$th power.  The
linear recurrence over $\IntegerNumbers/h\IntegerNumbers$ and the Jordan
decomposition are not formalized.""")),
]

PENDING += [
 # --- thm:lagrange-burmann ---
 (r"""which is \eqref{eq:lagrange-burmann-alt}.  Take $H(w)=w$ for
\eqref{eq:lagrange-basic}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the Lean proof is algebraic, with no residue calculus.
Module \lean{LagrangeInversion} formalizes \cref{eq:lagrange-burmann} as
\lean{Fabius.Lagrange.coeff_subst_derivative}, in the division-free form
$n[z^n]H(g)=[w^{n-1}]H'(w)\phi(w)^n$, and \cref{eq:lagrange-basic} as
\lean{Fabius.Lagrange.coeff_subst_id}, over an arbitrary commutative
$\RationalNumbers$-algebra.  The core lemmas take $g$ in the shape $g=z\,u$ with $u=\phi(g)$ and $u$
invertible, and the solution is then \emph{constructed} rather than assumed:
\lean{Fabius.Lagrange.solution} builds it as the compositional inverse of
$z\psi(z)$, where $\psi$ is the power-series inverse of $\phi$, and
\lean{Fabius.Lagrange.solution_eq} proves it satisfies
\cref{eq:lagrange-functional}.  So
\lean{Fabius.Lagrange.coeff_solution_subst_derivative} and
\lean{Fabius.Lagrange.coeff_solution} are unconditional statements about a
witness, not conditional ones.  Uniqueness of $g$ and
\cref{eq:lagrange-burmann-alt} are not formalized.
The proof above is unavailable in Lean, because it runs through
\cref{thm:res-subst}, which is itself unformalized.  The formal proof is
purely algebraic and rests on one cancellation: writing $v$ for the inverse of
$u$, one has $v^{M+1}g'=v^M-\frac1Mz(v^M)'$, whose $M$th coefficient vanishes
for every $M\ge1$ (\lean{Fabius.Lagrange.coeff_pow_succ_mul_derivative_eq_zero}),
while $vg'$ has constant term $1$
(\lean{Fabius.Lagrange.coeff_inv_mul_derivative}).  Substituting
$A(g)=(A\phi^n)(g)\,v^n$ into the truncated substitution expansion
\lean{Fabius.coeff_mul_subst_eq} therefore collapses the sum to its single
surviving term, which is
$[z^{n-1}]\bigl(A(g)g'\bigr)=[w^{n-1}]\bigl(A\phi^n\bigr)$
(\lean{Fabius.Lagrange.coeff_subst_mul_derivative}); the chain rule
\lean{PowerSeries.derivative_subst} turns that into the displayed form.""")),
]

PENDING += [
 # --- thm:lambert-W-zero ---
 (r"""point at $w=-1$, where $f(-1)=-\EulerE^{-1}$; this square-root branch point determines
the radius.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the series is Lean, the radius is not.
Module \lean{LambertWSeries} constructs $W$ rather than assuming it:
$W=z\EulerE^{-W}$ is the Lagrange functional equation with
$\phi(w)=\EulerE^{-w}$, which is invertible with inverse $\EulerE^{w}$
(\lean{Fabius.expNeg_mul_exp}), so \lean{Fabius.Lagrange.solution} applies and
\lean{Fabius.lambertW} is its value.  The familiar form $W\EulerE^W=z$ is
\lean{Fabius.lambertW_mul_exp_subst}, and \cref{eq:lambert-W-zero} is
\lean{Fabius.coeff_lambertW}, in the equivalent shape
$[z^{n+1}]W=(-(n+1))^n/(n+1)!$ that avoids a truncated subtraction; it follows
from \cref{eq:lagrange-basic} together with
$(\EulerE^{-w})^n=\EulerE^{-nw}$ (\lean{Fabius.expNeg_pow}).  The radius of
convergence $\EulerE^{-1}$, and with it the branch-point argument above, is
analytic and is not formalized.""")),
]

PENDING += [
 # --- thm:fuss-series ---
 (r"""Stirling's formula gives coefficients of order
$Ck^{-3/2}R_p^{-((p-1)k+1)}$, which proves absolute convergence on the boundary.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the series is Lean, the radius is not.
Module \lean{FussCatalanSeries} constructs the distinguished solution rather
than assuming it: with $q=p-1$, the equation $x-x^{q+1}=z$ is the Lagrange
functional equation for $\phi(w)=(1-w^q)^{-1}$, and that weight is invertible
by construction (\lean{Fabius.fussPhi_mul}), so \lean{Fabius.Lagrange.solution}
applies and gives \lean{Fabius.fussSolution}; the polynomial form of the
defining equation is \lean{Fabius.fussSolution_sub_pow}.
\cref{eq:fuss-series} then splits into two statements:
\lean{Fabius.coeff_fussSolution}, which is
$(qk+1)[z^{qk+1}]x=\binom{(q+1)k}{k}$, and
\lean{Fabius.coeff_fussSolution_eq_zero}, which is the vanishing of every
coefficient whose index is not of the form $qk+1$.  Both follow from
\cref{eq:lagrange-basic} once $\phi$ is written as the all-ones series with $w$
replaced by $w^q$ (Mathlib's \lean{PowerSeries.expand}); because that
substitution is an algebra map it commutes with the $n$th power, so the
negative binomial coefficients come straight from
\lean{PowerSeries.mk_one_pow_eq_mk_choose_add} and the index condition from
\lean{PowerSeries.coeff_expand_of_not_dvd}.
The radius \cref{eq:fuss-radius}, the critical-point argument that identifies
it, and the absolute convergence on $|z|=R_p$ are analytic and are not
formalized.""")),
]

PENDING += [
 # --- thm:inverse-bell-coeff ---
 (r"""at $n=1$ it is the whole sum and returns $g_1=f_1^{-1}$.  The one displayed
formula therefore covers both cases if the sum is read as $\sum_{k=0}^{n-1}$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the whole theorem is formal.
Module \lean{InverseBellCoefficients} follows the proof above and constructs
$g$ rather than assuming it: $w/f(w)$ is invertible because $f_1$ is, so
\lean{Fabius.Lagrange.solution} applies, and
\lean{Fabius.subst_egfA_reversion} proves $f(g(z))=z$.  The normalization is
\lean{Fabius.normRev}, and \lean{Fabius.egfA_eq_X_mul_normRev} is the
factorization $f(w)=w\,f_1(1+U(w))$ that makes it the right one; $f_1^{-1}$ is
carried as an explicit inverse rather than a division, so the module needs no
field.  \cref{eq:inverse-bell-coeff} is
\lean{Fabius.factorial_mul_coeff_reversion} with the sum from $k=0$, and
\lean{Fabius.factorial_mul_coeff_reversion_of_two_le} with the sum from $k=1$
for $n\ge2$; $g_1=f_1^{-1}$ is \lean{Fabius.coeff_reversion_one}, obtained from
the same formula at $n=1$.  The negative binomial expansion is separated out as
\lean{Fabius.negBinomSeries} over an arbitrary commutative ring, with
\lean{Fabius.negBinomSeries_mul} for $(1+w)^{-(d+1)}(1+w)^{d+1}=1$ and
\lean{Fabius.negBinomSeries_eq_egfA} for the rising-factorial exponential
coefficients; the passage to Bell polynomials is the corpus's exponential
composition theorem \lean{Fabius.egfA_subst_bellWeightSeries}.""")),
]

PENDING += [
 # --- thm:second-eulerian-first-diagonal ---
 (r"""which is \eqref{eq:second-eulerian-first-diagonal}.  Both sides are polynomials in
$m$ of degree at most $2p$, so the same identity gives the stated polynomial
continuation.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; formal proof by induction, not by generating function.
\lean{Fabius.stirlingFirst_diagonal} in module \lean{StirlingFirstDiagonal}
states the identity with the upper index written as $m+p$:
$\UnsignedStirlingFirstKind{m+p}{m}=\sum_{j\le p}\SecondOrderEulerianNumber
pj\binom{m+p+j}{2p}$.  The reindexing is not cosmetic.  The convention that an
out-of-range first-kind number vanishes cannot be read off truncated
subtraction in $\mathbb N$, where $m-p$ is $0$ rather than negative: at $m=0$,
$p\ge1$ the truncated reading would assert $1=0$.  Writing $m+p$ states the
intended range and needs no convention.
The formal proof does not follow the generating function above.  It is a double
induction, on $p$ and then on $m$, resting on the single termwise identity
\lean{Fabius.choose_termwise},
$(j+1)\binom{N+j}{r+1}+(r-j)\binom{N+j+1}{r+1}=N\binom{N+j}{r}$ for $j\le r$,
which is Pascal's rule followed by Mathlib's
\lean{Nat.choose_succ_right_eq}; the second-order Eulerian recurrence enters
through \lean{Fabius.sum_secondEulerian_choose_succ}.  Everything stays in
$\mathbb N$: no formal power series, no derivative, and no division.
The polynomial continuation is not stated separately in Lean: both sides are
polynomials in $m$ agreeing at every natural number, so it carries no
information beyond what is proved, and the corpus has no definition of the
continuation of $c$ in its upper index to state it against.""")),
]

PENDING += [
 # --- thm:diamond-bell ---
 (r"""The EGF of $x^{k\diamondsuit}$ is $X(t)^k$.  Compare with
\eqref{eq:partial-bell-egf}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the formal proof is the one given here.
Module \lean{DiamondPower} takes the diamond product to be
\lean{Bell.binomialConv}, the full binomial convolution, and
\lean{Fabius.binomialConv_eq_sum_Ico} shows that this agrees with
\eqref{eq:diamond} for sequences vanishing at $0$: the terms $j=0$ and
$j=n$, which the source's index range omits, are $x_0y_n$ and $x_ny_0$ and
vanish for that reason rather than by convention.
\lean{Fabius.diamondPow} takes the unit sequence $\delta_{n,0}$ as the empty
product, so that $k=0$ gives $\ExponentialPartialBellPolynomial n0=\delta_{n,0}$
and $x^{1\diamondsuit}=x$ (\lean{Fabius.diamondPow_one}); for $k\ge1$ this is
the $k$-fold product of the source.
The proof is the one above.  \lean{Bell.egfA_mul} turns a binomial convolution
into a product of exponential generating functions, so
\lean{Fabius.egfA_diamondPow} gives $X(t)^k$ by induction, and
\lean{Fabius.bellWeightSeries_pow} already reads the coefficients of $X(t)^k$
off the partial Bell polynomials.  \eqref{eq:diamond-bell} is then
\lean{Fabius.diamondPow_apply} in the product form $(x^{k\diamondsuit})_n=k!\,
\ExponentialPartialBellPolynomial nk$, and
\lean{Fabius.partialBell_eq_diamondPow_div} in the divided form displayed
above.""")),
]

PENDING += [
 # --- thm:bell-poly-egf ---
 (r"""identities.  The ordinary identities follow by the same multinomial argument or
by \eqref{eq:ordinary-exponential-scaling}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; all five identities are formal.
Everything here holds as an identity of formal power series over an arbitrary
commutative $\mathbb Q$-algebra.  The first identity is
\lean{Fabius.bellWeightSeries_pow} and the third
\lean{Fabius.exp_subst_bellWeightSeries}, both in module
\lean{BellGeneratingFunctions}; the second is
\lean{Fabius.exp_subst_smul_bellWeightSeries} in \lean{ExponentialFormula}.
On the ordinary side \lean{Fabius.ordPartialBell} is the ordinary partial Bell
polynomial, \cref{eq:ordinary-bell-ogf} is
\lean{Fabius.coeff_pow_eq_ordPartialBell} in \lean{OrdinaryBellComposition},
and \cref{eq:ordinary-bell-bivariate} is \lean{Fabius.coeff_exp_subst_smul} in
\lean{OrdinaryBellBivariate}, proved from the ordinary composition theorem
\lean{Fabius.coeff_subst_eq_sum_ordPartialBell} together with the homogeneity
\lean{Fabius.ordPartialBell_mul_left}, which is what converts the scaled weights
$ux_i$ into the factor $u^k$.
In both bivariate statements $u$ is a scalar in the algebra rather than a second
formal variable, and the identity is read on the coefficient of $t^n$; the
formal statements are also slightly more general than the displays, since they
ask only that the substituted series have no constant term rather than that it
be presented as $\sum_{j\ge1}x_jt^j$.""")),
]

PENDING += [
 # --- thm:merged-binomial-inversion ---
 (r"""\sum_{k=j}^{n}(-1)^{n-k}\binom nk\binom kj
 =\binom nj\sum_{r=0}^{n-j}(-1)^{n-j-r}\binom{n-j}{r}
 =\delta_{nj},
\]
which independently verifies the inverse matrices.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; both the sequence form and the EGF form are formal.
The equivalence of \cref{eq:merged-binomial-forward} and
\cref{eq:merged-binomial-backward} is \lean{Fabius.binomial_inversion_iff} for
additive commutative groups and \lean{Fabius.binomial_inversion_ring_iff} for
commutative rings, in module \lean{BinomialInversion}; the orthogonality
displayed at the end of the proof is
\lean{Fabius.sum_Icc_neg_one_pow_choose_mul_choose}.
\cref{eq:merged-binomial-egf} is module \lean{BinomialInversionEGF}, where
$\EulerE^{-z}$ is \lean{Fabius.altSeries}, the exponential generating function of
$(-1)^n$, and \lean{Fabius.exp_mul_altSeries} proves it inverts $\EulerE^{z}$.
Each half is stated as an equivalence with its sequence form rather than as an
implication: \lean{Fabius.egfA_eq_exp_mul_iff} and
\lean{Fabius.egfA_eq_altSeries_mul_iff}, with
\lean{Fabius.egfA_eq_exp_mul_iff_egfA_eq_altSeries_mul} relating the two
generating-function equations directly.
Two remarks on the formal proofs.  Multiplying exponential generating functions
is binomial convolution (\lean{Bell.egfA_mul}), so the only content is that
convolving against the constant sequence $1$, or against $(-1)^n$, gives the
displayed sums after reflecting the summation index
(\lean{Fabius.binomialConv_one_left},
\lean{Fabius.binomialConv_altSeries_left}).  And
\lean{Fabius.exp_mul_altSeries} is the binomial theorem at $-1+1=0$ rather than
a separate alternating-sum computation, which keeps it valid over an arbitrary
commutative ring instead of only over $\IntegerNumbers$.""")),
]

PENDING += [
 # --- thm:eulerian-recurrence ---
 (r"""\eqref{eq:eulerian-recurrence}.  Multiply by $t^k$, sum over $k$, and collect the
terms containing $k$ to obtain \eqref{eq:eulerian-poly-recurrence}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; both recurrences formal, the descent count is not.
\cref{eq:eulerian-recurrence} is the definition of \lean{Fabius.eulerianNumber}
in module \lean{EulerianNumbers} (\lean{Fabius.eulerianNumber_succ_succ}, with
the textbook indexing $\TypeAEulerianNumber nk=(k+1)\TypeAEulerianNumber{n-1}k
+(n-k)\TypeAEulerianNumber{n-1}{k-1}$ as
\lean{Fabius.eulerianNumber_succ_left}).  \cref{eq:eulerian-poly-recurrence} is
\lean{Fabius.eulerianPolynomial_succ} in module
\lean{EulerianPolynomialRecurrence}, over an arbitrary commutative ring.
Two points make the formal proof shorter than the coefficient bookkeeping the
text describes.  Every coefficient of $\TypeAEulerianPolynomial n$ is the
corresponding Eulerian number with no range condition
(\lean{Fabius.coeff_eulerianPolynomial}), since the entries above the diagonal
already vanish; and $t\bigl(\TypeAEulerianPolynomial n\bigr)'$ has the uniform coefficient
$k\TypeAEulerianNumber nk$ (\lean{Fabius.coeff_X_mul_derivative}), so the
derivative term needs no separate treatment at $k=0$.
One point does need care, and is recorded as
\lean{Fabius.natCast_sub_mul_eulerianNumber}: the numerical recurrence carries
$n-k$ as a truncated subtraction of natural numbers while the polynomial
identity carries the ring difference, and the two disagree exactly where the
Eulerian number they multiply is zero.
The combinatorial reading of $\TypeAEulerianNumber nk$ as a descent count, and
with it the insertion argument given above, is not formalized; the Lean
development takes the recurrence as the definition.""")),
]

PENDING += [
 # --- thm:bell-inversions ---
 (r"""iterated $k$ times in the equivalent form
$\Expectation[X^{n+1}(X-1)^k]=\Expectation[(X+1)^nX^k]$, turns it into the right side after expanding
$(X-1)^k$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; the second identity is formal by a different route.
\cref{eq:bell-inversion-one} is
\lean{Fabius.bell_eq_sum_neg_one_pow_choose_bell_succ} in module
\lean{BellShiftEGF}, exactly as the text says: ordinary binomial inversion
(\lean{Fabius.binomial_inversion_ring}) applied to the Bell recurrence
\lean{Fabius.bell_succ_eq_sum_choose}.
\cref{eq:bell-inversion-two} is
\lean{Fabius.sum_choose_bell_add_eq_sum_neg_one_pow} in module
\lean{BellInversionTwo}, but not by the argument above.  The Poisson route needs
the moments of a Poisson variable and the summation-by-parts identity
\cref{eq:poisson-sbp}; neither is available in the corpus, and formalizing them
would be a considerably larger undertaking than the identity itself.  Instead
both sides are given names, \lean{Fabius.bellForward} and
\lean{Fabius.bellBackward}, and are shown to satisfy the same recurrence in $k$,
\[
 H(n,k+1)=H(n+1,k)-H(n,k),
\]
(\lean{Fabius.bellForward_succ}, \lean{Fabius.bellBackward_succ}) and to agree at
$k=0$, where both equal $\BellNumber{n+1}$ by the Bell recurrence
(\lean{Fabius.bellForward_zero}, \lean{Fabius.bellBackward_zero}).  Each
recurrence is Pascal's rule together with a shift of the summation index, so the
formal proof is a double induction over $\IntegerNumbers$ with no probability
and no generating function in it.
The probabilistic proof in the text is not thereby superseded; it explains where
the identity comes from, which the induction does not.""")),
]

PENDING += [
 # --- thm:second-reverse-recurrences ---
 (r"""They are equal because direct differentiation gives
$(1-\EulerE^{-x})F_k'(x)=kF_k(x)$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; two of the three identities are formal.
\cref{eq:second-triangular-explicit} is
\lean{Fabius.stirlingSecond_eq_pow_div_factorial_sub_sum} in module
\lean{StirlingTriangularExplicit}, for all $n,k$ with the $r=0$ term left in the
sum.
\cref{eq:second-reverse-column} is \lean{Fabius.second_reverse_column} in module
\lean{StirlingSecondReverseColumn}, and the formal proof is the one given here.
The right-hand side is read as a binomial convolution of the kernel
$j\mapsto(-1)^j$, restricted to $j\ge2$, against the shifted column
$m\mapsto\StirlingSecondKind{m+1}k$, so its exponential generating function is
$(\EulerE^{-x}-1+x)F_k'$ (\lean{Fabius.egfA_altKernel},
\lean{Fabius.egfA_second_reverse_column_rhs}); the displayed differential
equation is
\lean{Fabius.one_sub_altSeries_mul_derivative_egfA_stirlingSecond}, where
$\EulerE^{-x}$ is \lean{Fabius.altSeries}, the exponential generating function of
$(-1)^n$, and $\EulerE^{-x}\EulerE^{x}=1$ is \lean{Fabius.exp_mul_altSeries}.
Worth noting beside the first-kind case: the first-kind column satisfies
$(1-x)\log(1-x)F'=-kF$, whose kernel needs a logarithm and a dedicated series,
while the kernel here is elementary.
\cref{eq:second-reverse-row} is not formalized.""")),
]

PENDING += [
 # --- thm:bell-symmetric-functions ---
 (r"""the logarithm through ordinary Bell polynomials yields the second pair of forms.
The exponential form follows from \eqref{eq:ordinary-exponential-scaling}.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; three of the four displayed forms are formal.
Everything here is proved for a finite family $u:\iota\to A$ indexed by a
finite set, over any commutative $\mathbb Q$-algebra, with
$e_n=\sum_{|t|=n}\prod_{i\in t}u_i$ and $p_r=\sum_i u_i^r$.
\cref{eq:elementary-via-bell} is \lean{Fabius.esymm_eq_bell_complete} in module
\lean{ElementarySymmetricBell}, and its sign variant is
\lean{Fabius.esymm_eq_neg_bell_complete}, which follows from the weighted
homogeneity \lean{Fabius.partialBell_pow_mul}.
\cref{eq:powersum-via-bell} is \lean{Fabius.newton_power_sum} in
\lean{NewtonPowerSumBell}, stated multiplied through by $(-1)^{n-1}(n-1)!$ so
that it is division-free, with the displayed divided form as
\lean{Fabius.power_sum_eq}.
The formal proof of the first identity is not the one given here.  Taking
logarithms needs $\exp\circ\log=\mathrm{id}$ for formal power series, which
Mathlib does not have; that gap is now filled by
\lean{Fabius.exp_subst_logOf} in module \lean{ExpLog}, proved through the
differential equation $F'=FW$ rather than by a coefficient computation, with
$f'/f$ written as a substituted geometric series so that no inverse is ever
formed.  The symmetric-function identity itself is then obtained the same way:
$\prod_i(1+u_it)$ and $\sum_n\ExponentialCompleteBellPolynomial n t^n/n!$ satisfy
the same equation and agree at $t=0$.
The second identity is a corollary rather than a separate argument.  The Newton
weights have the scaled elementary symmetric functions $n!e_n$ as their complete
Bell family, so they are that sequence's cumulants, and the cumulants have the
closed form \lean{Fabius.cumulant_eq_cumulantSum} in
\lean{CumulantBellFormula} — the moment-to-cumulant formula, which the corpus
also lacked and which is proved here from the same $\exp\circ\log$ inverse.
The second form of \cref{eq:powersum-via-bell}, through the ordinary partial
Bell polynomials, is not formalized.""")),
]

PENDING += [
 # --- thm:merged-catalan-first-return ---
 (r"""equation.  Of the two quadratic roots, only the displayed branch has constant
term $1$.
\end{proof}
""",
  remark(r"""% ed.: crosswalk added 2026-09-02; both displays are now formal.
$C=1+zC^2$ is \lean{Fabius.catalanSeries_eq}, and the uniqueness the proof
appeals to — that only one power series satisfies it — is
\lean{Fabius.eq_catalanSeries_of_eq_one_add_X_mul_sq}, both in module
\lean{CatalanGeneratingFunction}.
The closed form is \lean{Fabius.sqrtOf_one_sub_four_X} in module
\lean{SquareRootSeries}, stated as $\sqrt{1-4z}=1-2zC(z)$ rather than as
$C=(1-\sqrt{1-4z})/(2z)$ so that nothing is divided by $z$.  The square root is
\lean{Fabius.sqrtOf}, defined as $\exp(\tfrac12\log)$ on series with constant
term $1$ and unique among such series by \lean{Fabius.sqrt_unique}; the
existence rests on the formal exponential law \lean{Fabius.exp_subst_add} and on
\lean{Fabius.exp_subst_logOf}, in modules \lean{ExpAddLog} and \lean{ExpLog}.
The formal proof uses no binomial series and no analysis: squaring $1-2zC$ and
substituting $zC^2=C-1$ gives $1-4z$ outright.
Two things this does not say.  The $\sqrt{\cdot}$ is the formal square root just
described, not a real or complex one, so the identity is between power series
over a commutative $\mathbb Q$-algebra.  And the radius of convergence, together
with the branch of the square root that the analytic statement selects, is not
formalized.""")),
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
