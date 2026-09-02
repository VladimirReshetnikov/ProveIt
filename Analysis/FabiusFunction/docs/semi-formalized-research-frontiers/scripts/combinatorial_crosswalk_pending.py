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
All six identities are in module \lean{StirlingSummations}, over the natural
numbers.  The first equality of \cref{eq:first-two-sums} is
\lean{Fabius.stirlingFirst_succ_succ_eq_sum_choose}, proved as the coefficient
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
(\lean{Fabius.bernoulliPolySeries_mul_exp_sub_one}); summing over
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
