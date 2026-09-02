# -*- coding: utf-8 -*-
r"""(Re)generate the Lean formalization register of
Combinatorial_Coefficient_Calculus.tex.

Run:  python add_register.py <path-to-tex>

* First run: adds the \lean macro to the preamble and appends the register
  section before \backmatter.
* Later runs: replaces the existing register section (everything from
  '\section{Lean formalization register}' to '\backmatter') with a fresh one.

One row per theorem-like environment (theorem/proposition/lemma/corollary/
identity/algorithm), in document order, with a status column:

  Lean      -- an exact (or more general) Lean counterpart exists
  partial   -- a named part of the statement is proved; the rest is named
  none      -- no Lean counterpart yet (the default)

Statuses come from the STATUS dictionary, keyed by label.  Unlabelled
results are keyed by environment name and running number.
"""
import io, re, sys

path = sys.argv[1]
s = io.open(path, encoding='utf-8').read()

# ---------------------------------------------------------------- macro
if '\\newcommand{\\lean}' not in s:
    anchor = '\\newtheorem{historical}[theorem]{Historical note}\n'
    assert s.count(anchor) == 1
    macro = anchor + (
        '\n% Crosswalk to the Lean development (Analysis/FabiusFunction/Lean/FabiusFunction):\n'
        '% typeset a declaration name verbatim, in text or in math mode.\n'
        '\\newcommand{\\lean}[1]{\\ifmmode\\text{\\texttt{\\detokenize{#1}}}'
        '\\else\\nolinkurl{#1}\\fi}\n')
    s = s.replace(anchor, macro)

# ---------------------------------------------------------------- statuses
# label -> (status, "declarations (module)")
STATUS = {
 'thm:first-cycle': ('partial',
   r"recurrence and boundary values are Mathlib's \lean{Nat.stirlingFirst_succ_succ}, "
   r"\lean{Nat.stirlingFirst_succ_zero}, \lean{Nat.stirlingFirst_eq_zero_of_lt}; the "
   r"defining expansions are \lean{Fabius.ascPochhammer_eq_sum_monomial_stirlingFirst} and "
   r"\lean{Fabius.descPochhammer_eq_sum_monomial_signedStirlingFirst} "
   r"(\lean{StirlingBasisChange}); the permutation count itself is not formalized"),
 'thm:second-recurrence': ('Lean',
   r"\lean{Nat.stirlingSecond_succ_succ}, \lean{Nat.stirlingSecond_succ_zero}, "
   r"\lean{Nat.stirlingSecond_eq_zero_of_lt} (Mathlib); the set-partition count is "
   r"Mathlib's definition by this recurrence"),
 'thm:second-explicit': ('Lean',
   r"\lean{Fabius.factorial_mul_stirlingSecond_eq_sum} (over $\mathbb Z$) and "
   r"\lean{Fabius.stirlingSecond_eq_sum_div_factorial} (over $\mathbb Q$) "
   r"(\lean{StirlingBasisChange}); proved by binomial inversion of "
   r"\lean{Fabius.pow_eq_sum_stirlingSecond_mul_factorial_mul_choose}"),
 'thm:stirling-basis': ('Lean',
   r"\lean{Fabius.ascPochhammer_eq_sum_monomial_stirlingFirst}, "
   r"\lean{Fabius.descPochhammer_eq_sum_monomial_signedStirlingFirst}, "
   r"\lean{Fabius.X_pow_eq_sum_stirlingSecond_mul_descPochhammer}, "
   r"\lean{Fabius.X_pow_eq_sum_stirlingSecond_mul_ascPochhammer}, "
   r"\lean{Fabius.pow_eq_sum_stirlingSecond_mul_factorial_mul_choose} "
   r"(\lean{StirlingBasisChange}); polynomial identities over every commutative ring"),
 'cor:stirling-inverse': ('Lean',
   r"\lean{Fabius.sum_range_stirlingSecond_mul_signedStirlingFirst}, "
   r"\lean{Fabius.sum_range_signedStirlingFirst_mul_stirlingSecond} and their "
   r"\lean{Finset.Icc} forms (\lean{StirlingBasisChange})"),
 'thm:lah-conv': ('Lean',
   r"\lean{Fabius.ascPochhammer_eq_sum_lahNumber_mul_descPochhammer}, "
   r"\lean{Fabius.descPochhammer_eq_sum_lahNumber_mul_ascPochhammer}, "
   r"\lean{Fabius.sum_range_lahNumber_mul_lahNumber}, "
   r"\lean{Fabius.lahNumber_eq_sum_stirlingFirst_mul_stirlingSecond} (\lean{LahNumbers}); "
   r"the closed form of the definition is \lean{Fabius.lahNumber_succ_succ_mul_factorial}"),
 'thm:stirling-egfs': ('partial',
   r"\lean{Fabius.exp_sub_one_pow}, \lean{Fabius.egf_stirlingSecond}, "
   r"\lean{Fabius.negLogOneSub_pow}, \lean{Fabius.egf_stirlingFirst}, "
   r"\lean{Fabius.log_pow} (\lean{StirlingGeneratingFunctions}), as formal power series "
   r"over any commutative $\mathbb Q$-algebra; the bivariate generating function "
   r"\cref{eq:second-double-egf} is not formalized"),
 'thm:stirling-transform': ('partial',
   r"the inversion formula is \lean{Fabius.stirling_inversion}, "
   r"\lean{Fabius.stirling_inversion_symm}, \lean{Fabius.stirling_inversion_iff} "
   r"(\lean{StirlingBasisChange}), for sequences in any additive commutative group; "
   r"the generating-function form is \lean{Fabius.egfA_subst_exp_sub_one} and "
   r"\lean{Fabius.egfA_subst_log} (\lean{StirlingTransformEGF}): substituting $\EulerE^t-1$, "
   r"respectively $\log(1+t)$, into an exponential generating function applies the second-kind, "
   r"respectively signed first-kind, Stirling transform"),
 'thm:bell-binomial-recurrence': ('Lean', r"\lean{Nat.bell_succ} (Mathlib, the definition)"),
 'thm:bell-stirling-sum': ('Lean',
   r"\lean{Fabius.bell_eq_sum_stirlingSecond}, \lean{Fabius.bell_eq_sum_sum_div_factorial} "
   r"(\lean{BellStirling})"),
 'thm:dobinski': ('Lean',
   r"\lean{Fabius.dobinski} (\lean{BellStirling}), from the general Poisson moment identity "
   r"\lean{Fabius.tsum_pow_mul_pow_div_factorial}"),
 'thm:poisson-stirling-moments': ('partial',
   r"the moment series $\sum_m m^n\lambda^m/m! = e^{\lambda}\sum_k S(n,k)\lambda^k$ is "
   r"\lean{Fabius.tsum_pow_mul_pow_div_factorial} (\lean{BellStirling}) for every real "
   r"$\lambda$; the probabilistic phrasing is not formalized"),
 'thm:merged-binomial-inversion': ('Lean',
   r"\lean{Fabius.binomial_inversion_iff} (additive commutative groups) and "
   r"\lean{Fabius.binomial_inversion_ring_iff} (commutative rings) "
   r"(\lean{BinomialInversion}); the kernel orthogonality is "
   r"\lean{Fabius.sum_Icc_neg_one_pow_choose_mul_choose}; the EGF form is not formalized"),
 'thm:bell-poly-recurrences': ('Lean',
   r"\lean{Fabius.partialBell} is defined by \cref{eq:partial-bell-recurrence} "
   r"(\lean{Fabius.partialBell_succ_succ}, \lean{Fabius.partialBell_succ_succ_eq_binomialConv}); "
   r"\cref{eq:complete-bell-recurrence} is Mathlib-free \lean{Bell.complete_succ} together with "
   r"\lean{Fabius.bell_complete_eq_sum_partialBell} (\lean{PartialBellPolynomials}, "
   r"\lean{BellPolynomialInversion}); the boundary values are \lean{Fabius.partialBell_zero_succ}, "
   r"\lean{Fabius.partialBell_succ_zero}, \lean{Fabius.partialBell_eq_zero_of_lt}"),
 'thm:bell-poly-egf': ('partial',
   r"the first identity is \lean{Fabius.bellWeightSeries_pow} and the third "
   r"\lean{Fabius.exp_subst_bellWeightSeries} (\lean{BellGeneratingFunctions}), as formal power "
   r"series over any commutative $\mathbb Q$-algebra; the bivariate form is "
   r"\lean{Fabius.exp_subst_smul_bellWeightSeries} (\lean{ExponentialFormula}) and the ordinary "
   r"Bell polynomials are \lean{Fabius.ordPartialBell} with "
   r"\lean{Fabius.coeff_pow_eq_ordPartialBell} (\lean{OrdinaryBellComposition})"),
 'thm:bell-poly-specializations': ('partial',
   r"\cref{eq:bell-first-specialization} is \lean{Fabius.partialBell_factorial_pred}, "
   r"\cref{eq:bell-second-specialization} is \lean{Fabius.partialBell_one}, "
   r"\cref{eq:bell-number-specialization} is \lean{Fabius.bell_complete_one}, "
   r"\cref{eq:bell-lah-specialization} is \lean{Fabius.partialBell_factorial} "
   r"(\lean{PartialBellPolynomials}, \lean{BellGeneratingFunctions}), and the Touchard form "
   r"\cref{eq:touchard-bell-specialization} is \lean{Fabius.bell_complete_const_eq_touchard_eval} "
   r"(\lean{BellHomogeneity}); the factorial row sum \cref{eq:bell-factorial-complete} is not "
   r"formalized"),
 'thm:bell-partial-convolution': ('Lean',
   r"\lean{Fabius.factorial_mul_partialBell_add} (\lean{BellComposition}), in the division-free "
   r"form $(k_1+k_2)!\,B_{n,k_1+k_2}=k_1!k_2!\sum_i\binom ni B_{i,k_1}B_{n-i,k_2}$"),
 'thm:exponential-composition': ('Lean',
   r"\lean{Fabius.egfA_subst_bellWeightSeries} (\lean{BellComposition}): substitution of "
   r"exponential generating functions over any commutative $\mathbb Q$-algebra"),
 'thm:complete-bell-addition': ('Lean',
   r"\lean{Bell.complete_add} (\lean{BellPolynomialInversion}), over every commutative semiring"),
 'thm:bell-transform-inverse': ('Lean',
   r"\cref{eq:bell-transform-x} is \lean{Fabius.bell_transform_inverse} (\lean{BellComposition}), "
   r"from $X=\log(1+Y)$ formalized as \lean{Fabius.log_subst_exp_sub_one} and the composition "
   r"theorem; the recursive inversion over every commutative ring is \lean{Bell.complete_cumulant} "
   r"and \lean{Bell.cumulant_complete} (\lean{BellPolynomialInversion}); the general form "
   r"\cref{eq:general-bell-inverse} is not formalized"),
 'thm:moment-cumulant': ('Lean',
   r"\cref{eq:moments-from-cumulants} is \lean{Fabius.bell_complete_eq_sum_partialBell} with "
   r"\lean{Fabius.exp_subst_bellWeightSeries}, and \cref{eq:cumulants-from-moments} is "
   r"\lean{Fabius.bell_transform_inverse} (\lean{BellComposition}); the recursive forms are "
   r"\lean{Fabius.completeBellPolynomial_momentCumulant}, "
   r"\lean{Fabius.momentCumulant_completeBellPolynomial} (\lean{MomentCumulantAlgebra}) and "
   r"\lean{Bell.complete_cumulant}"),
 'thm:bell-egf': ('Lean',
   r"\lean{Fabius.exp_subst_exp_sub_one} (\lean{BellGeneratingFunctions}): "
   r"$\exp\circ(e^z-1)=\sum_n B(n)z^n/n!$ as formal power series over any commutative "
   r"$\mathbb Q$-algebra; the differential equation is the derivative of this substitution"),
 'thm:merged-bernoulli-stirling-touchard': ('partial',
   r"\cref{eq:merged-bernoulli-stirling} is \lean{Fabius.bernoulli_eq_sum_stirlingSecond} "
   r"(\lean{BernoulliStirling}) for Mathlib's \lean{bernoulli} (with $B_1=-1/2$), from "
   r"\lean{Fabius.bernoulliPowerSeries_eq_logDivSeries_subst}: the Bernoulli generating "
   r"function is $\log(1+u)/u$ at $u=\EulerE^t-1$; the two integral representations are not "
   r"formalized"),
 'thm:bell-bihomogeneous': ('Lean',
   r"\lean{Fabius.partialBell_mul_left}, \lean{Fabius.partialBell_pow_mul}, "
   r"\lean{Fabius.partialBell_bihomogeneous} (\lean{BellHomogeneity}), over every commutative "
   r"semiring"),
 'thm:eulerian-alternating': ('partial',
   r"\cref{eq:eulerian-alternating} is \lean{Fabius.sum_neg_one_pow_mul_eulerianNumber} "
   r"(\lean{EulerianAlternating}), from the Eulerian EGF at $t=-1$ "
   r"(\lean{Fabius.egfA_eulerianPolynomial_eval_neg_one_mul}) and "
   r"$x\tanh x=x-\mathscr B(2x)+\mathscr B(4x)$ "
   r"(\lean{Fabius.X_mul_egfA_eulerianPolynomial_eval_neg_one}); the two reciprocal-binomial "
   r"identities are not formalized"),
 'thm:merged-genocchi': ('Lean',
   r"with \lean{Fabius.genocchi} defined by $2(1-2^n)\beta_n$, the generating function "
   r"\cref{eq:merged-genocchi-egf} is \lean{Fabius.egf_genocchi_mul_exp_add_one} "
   r"(\lean{GenocchiNumbers}), i.e. the first equality of \cref{eq:merged-genocchi}, and the "
   r"second equality is \lean{Fabius.genocchi_succ_eq} (\lean{EulerPolynomials}); "
   r"\lean{Fabius.genocchi_one}, \lean{Fabius.genocchi_two}, \lean{Fabius.genocchi_odd} give the "
   r"initial values and the parity"),
 'thm:merged-alternating-sums': ('Lean',
   r"\lean{Fabius.sum_neg_one_pow_mul_pow_eq_eulerPolynomial} (\lean{EulerPolynomials}), in the "
   r"form $\sum_{j<N}(-1)^j(x+j)^p=\bigl(\mathsf E_p(x)-(-1)^N\mathsf E_p(x+N)\bigr)/2$, valid "
   r"for all $N\ge0$, by induction from the difference identity"),
 'thm:bell-leading-zeros': ('Lean',
   r"\lean{Fabius.partialBell_leadingZeros} (\lean{BellLeadingZeros}), over any "
   r"$\RationalNumbers$-algebra, with the zero-padded weights \lean{Fabius.leadingZeros} and the "
   r"rescaled weights \lean{Fabius.qScaled}; the proof compares the weight series "
   r"(\lean{Fabius.bellWeightSeries_leadingZeros}) exactly as in the text"),
 'thm:merged-sheffer': ('partial',
   r"\cref{eq:merged-sheffer-addition} is \lean{Fabius.shefferPoly_add} (\lean{BinomialType}), "
   r"for \lean{Fabius.shefferPoly} $=c\star p$ (binomial convolution of the coefficients of $g$ "
   r"with the binomial-type sequence), with generating function "
   r"\lean{Fabius.egfA_mul_exp_subst_smul_bellWeightSeries}; the lowering law "
   r"\cref{eq:merged-sheffer-lowering} is not formalized"),
 'thm:binomial-type-bell': ('partial',
   r"with \lean{Fabius.binomialTypePoly} defined by \cref{eq:binomial-type-bell} "
   r"(\lean{BinomialType}): \cref{eq:binomial-type-egf} is "
   r"\lean{Fabius.exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly} and "
   r"\cref{eq:binomial-type-identity} is \lean{Fabius.binomialTypePoly_add} (from the addition "
   r"law \lean{Bell.complete_add}), over any commutative ring; the delta operator "
   r"\cref{eq:delta-operator} is not formalized"),
 'thm:normal-order': ('Lean',
   r"\lean{Fabius.iterate_X_mul_derivative} (\cref{eq:normal1}) and "
   r"\lean{Fabius.xkDk_eq_sum_signedStirlingFirst} (\cref{eq:normal2}, by Stirling inversion) in "
   r"\lean{StirlingNormalOrder}, as identities of operators applied to an arbitrary polynomial "
   r"over any commutative ring; the falling-factorial form $\FallingFactorial{xD}{n}$ and the "
   r"operator series \cref{eq:der-from-diff,eq:diff-from-der} are not formalized"),
 'thm:paired-sums': ('Lean',
   r"\lean{StirlingSummations}: \cref{eq:first-two-sums} is "
   r"\lean{Fabius.stirlingFirst_succ_succ_eq_sum_choose} and "
   r"\lean{Fabius.stirlingFirst_succ_succ_eq_sum_descFactorial}, \cref{eq:second-two-sums} is "
   r"\lean{Fabius.stirlingSecond_succ_succ_eq_sum} (\lean{BellStirling}) and "
   r"\lean{Fabius.stirlingSecond_succ_succ_eq_sum_pow}, the hockey sticks "
   r"\cref{eq:first-hockey,eq:second-hockey} are \lean{Fabius.stirlingFirst_add_succ_eq_sum} and "
   r"\lean{Fabius.stirlingSecond_add_succ_eq_sum} (with lower index $k$ in the first-kind case, "
   r"correcting a misprint), and the convolutions "
   r"\cref{eq:first-convolution,eq:second-convolution} are "
   r"\lean{Fabius.choose_mul_stirlingFirst_add} and \lean{Fabius.choose_mul_stirlingSecond_add}"),
 'cor:shifted-stirling-evaluations': ('Lean',
   r"\cref{eq:shifted-power-to-fall} is "
   r"\lean{Fabius.X_pow_eq_sum_stirlingSecond_succ_mul_descPochhammer_comp} in $R[x]$ over any "
   r"commutative ring (cancelling $x$ via \lean{Fabius.X_mul_cancel}) and "
   r"\cref{eq:stirling-n-to-n} is \lean{Fabius.pow_self_eq_sum_stirlingSecond_mul_descFactorial} "
   r"(\lean{StirlingShiftedEvaluations})"),
 'thm:ordinary-composition': ('partial',
   r"\cref{eq:ordinary-composition-bell} is \lean{Fabius.coeff_subst_eq_sum_ordPartialBell} "
   r"(\lean{OrdinaryBellComposition}) over any commutative ring, with the ordinary Bell "
   r"polynomials \lean{Fabius.ordPartialBell} defined by the composition recurrence "
   r"$\OrdinaryPartialBellPolynomial n{k+1}=\sum_{i\ge1}b_i\OrdinaryPartialBellPolynomial{n-i}{k}$ "
   r"(so \cref{eq:ordinary-composition-compositions} is the definition unrolled) and "
   r"$[x^n]G^k=\OrdinaryPartialBellPolynomial nk(b)$ as \lean{Fabius.coeff_pow_eq_ordPartialBell}; "
   r"the reciprocal formula \cref{eq:reciprocal-ordinary-bell} is "
   r"\lean{Fabius.coeff_reciprocalSeries}; the multinomial form "
   r"\cref{eq:ordinary-composition-multiplicities} is not formalized"),
 'thm:eulerian-binomial-recurrence': ('Lean',
   r"\lean{Fabius.eulerianPolynomial_binomial_recurrence} in $R[t]$ and "
   r"\lean{Fabius.eulerian_binomial_recurrence_series} in $R[[t]]$ (\lean{EulerianEGF}), for "
   r"$n\ge1$ over any commutative ring $R$, proved from the rational generating function "
   r"\cref{eq:eulerian-power-series} and the binomial theorem rather than from the EGF"),
 'thm:eulerian-egf': ('Lean',
   r"\lean{Fabius.egfA_eulerianPolynomial_mul} (\lean{EulerianEGF}): in $(\RationalNumbers[t])[[x]]$, "
   r"$\bigl(\sum_n\TypeAEulerianPolynomial{n}(t)x^n/n!\bigr)\,(t-\EulerE^{(t-1)x})=t-1$, i.e. "
   r"\cref{eq:eulerian-egf} in multiplicative form; it is the binomial recurrence "
   r"\cref{thm:eulerian-binomial-recurrence} read coefficientwise"),
 'thm:spivey': ('Lean',
   r"\lean{Fabius.spivey} (\lean{BellShiftEGF}), read off from the shifted generating function "
   r"\lean{Fabius.egfA_bell_add}: $\sum_n\BellNumber{n+m}t^n/n!=\TouchardPolynomial{m}(\EulerE^t)"
   r"\,\EulerE^{\EulerE^t-1}$, proved by induction on $m$ from the Touchard recurrence "
   r"\lean{Fabius.derivative_touchardExp}; the Touchard-polynomial version "
   r"$\TouchardPolynomial{m+n}(x)=\sum_{j,k}\StirlingSecondKind mj x^j\binom nk\TouchardPolynomial{k}(x)j^{n-k}$ "
   r"is \lean{Fabius.spivey_touchard} (\lean{TouchardShiftEGF})"),
 'thm:bell-inversions': ('partial',
   r"\cref{eq:bell-inversion-one} is \lean{Fabius.bell_eq_sum_neg_one_pow_choose_bell_succ} "
   r"(\lean{BellShiftEGF}), by \lean{Fabius.binomial_inversion_ring} applied to "
   r"\lean{Fabius.bell_succ_eq_sum_choose}; \cref{eq:bell-inversion-two} is not formalized"),
 'thm:second-reverse-recurrences': ('partial',
   r"\cref{eq:second-triangular-explicit} is "
   r"\lean{Fabius.stirlingSecond_eq_pow_div_factorial_sub_sum} (\lean{StirlingTriangularExplicit}), "
   r"for all $n,k$ with the $r=0$ term included; the two reverse recurrences "
   r"\cref{eq:second-reverse-row,eq:second-reverse-column} are not formalized"),
 'thm:eulerian-stirling': ('Lean',
   r"\lean{Fabius.sum_eulerianNumber_mul_X_pow_eq_sum_stirlingSecond} (\lean{EulerianStirling}), "
   r"as an identity in $R[[t]]$ over any commutative ring $R$, from the rising-factorial "
   r"expansion of $(m+1)^n$ and $\sum_m\binom{m+k}{k}t^m=(1-t)^{-k-1}$"),
 'thm:merged-complementary-bell': ('Lean',
   r"\lean{Fabius.complementaryBell} (\lean{ComplementaryBell}); "
   r"\cref{eq:merged-complementary-egf} is \lean{Fabius.exp_subst_neg_exp_sub_one}, "
   r"\cref{eq:merged-complementary-recurrence} is \lean{Fabius.complementaryBell_succ}, and "
   r"\cref{eq:merged-complementary-dobinski} is \lean{Fabius.complementaryBell_eq_exp_mul_tsum} "
   r"(the series converges absolutely as the Poisson moment series of "
   r"\lean{Fabius.tsum_pow_mul_pow_div_factorial})"),
 'cor:merged-bell-convolution-inverse': ('Lean',
   r"\lean{Fabius.sum_choose_bell_mul_complementaryBell} (\lean{ComplementaryBell}), from the "
   r"addition law \lean{Bell.complete_add} of complete Bell polynomials at weights $\pm1$"),
 'thm:newton-expansion': ('Lean',
   r"\lean{Fabius.newton_expansion} (\lean{NewtonExpansion}): $p=\sum_{k\le d}"
   r"\frac{\Delta^kp(0)}{k!}\FallingFactorial{x}{k}$ in $K[x]$ for every field $K$ of "
   r"characteristic zero, from the evaluation form "
   r"\lean{Fabius.eval_natCast_eq_sum_choose_fwdDiff} ($p(m)=\sum_k\binom mk\Delta^kp(0)$ over "
   r"any commutative ring), which packages Mathlib's Gregory--Newton formula "
   r"\lean{shift_eq_sum_fwdDiff_iter} with \lean{Polynomial.fwdDiff_iter_eq_zero_of_degree_lt}"),
 'thm:exponential-formula': ('Lean',
   r"\cref{eq:partial-bell-egf} is \lean{Fabius.bellWeightSeries_pow}, "
   r"\cref{eq:bivariate-bell-egf} is \lean{Fabius.exp_subst_smul_bellWeightSeries} "
   r"(\lean{ExponentialFormula}), \cref{eq:complete-bell-egf} is "
   r"\lean{Fabius.exp_subst_bellWeightSeries}, all as substitutions of formal power series "
   r"over any $\RationalNumbers$-algebra"),
 'thm:ordered-bell': ('Lean',
   r"\lean{Fabius.fubini} is defined by \cref{eq:ordered-bell-stirling}; "
   r"\cref{eq:ordered-bell-egf} is \lean{Fabius.two_sub_exp_mul_egfA_fubini} (via "
   r"\lean{Fabius.egfA_fubini}: the generating function is $1/(1-u)$ at $u=\EulerE^t-1$) and "
   r"\cref{eq:ordered-bell-recurrence} is \lean{Fabius.fubini_succ} (\lean{OrderedBell}); the "
   r"ordered-partition count itself is not formalized"),
 'thm:second-ogf': ('Lean',
   r"\lean{Fabius.prod_one_sub_mul_X_mul_stirlingColumnOGF} and "
   r"\lean{Fabius.stirlingColumnOGF_eq_prod_mk_pow} (\lean{StirlingOrdinaryGF}): the column "
   r"series $\sum_r\StirlingSecondKind{k+r}{k}x^r$ times $\prod_{j\le k}(1-jx)$ is $1$, and "
   r"equals the product of the geometric series $\sum_r j^rx^r$, in $R[[x]]$ for every "
   r"commutative ring $R$; the complete-homogeneous coefficient formula is the coefficient "
   r"extraction of the latter and is not stated separately"),
 'thm:eulerian-power-series': ('Lean',
   r"\lean{Fabius.one_sub_X_pow_mul_succPowSeries} (the identity "
   r"$(1-t)^{n+1}\sum_m(m+1)^nt^m=\TypeAEulerianPolynomial{n}(t)$ in $R[[t]]$) and "
   r"\lean{Fabius.eulerianNumber_eq_sum_int} (\lean{EulerianGeneratingFunctions}); the "
   r"symmetry \cref{eq:eulerian-symmetry} is \lean{Fabius.eulerianNumber_symm} and "
   r"\cref{eq:eulerian-k1} is \lean{Fabius.eulerianNumber_one_right}"),
 'thm:merged-riordan': ('Lean',
   r"\lean{Fabius.expRiordan_action}, \lean{Fabius.expRiordan_mul}, "
   r"\lean{Fabius.expRiordan_mul_inverse} (\lean{ExponentialRiordan}), for exponential Riordan "
   r"arrays $[g,f]$ over any $\RationalNumbers$-algebra, with the inverse law in the form "
   r"$[g,f]\,[h,\overline f]=[1,t]$ whenever $g\,(h\circ f)=1$; the Stirling examples are "
   r"\lean{Fabius.expRiordan_one_exp_sub_one} and \lean{Fabius.expRiordan_one_log}"),
 'cor:merged-bernoulli-stirling-second-proof': ('partial',
   r"the conclusion is \lean{Fabius.bernoulli_eq_sum_stirlingSecond} and the evaluation "
   r"$\Delta^k0^n=k!\StirlingSecondKind nk$ is \lean{Fabius.factorial_mul_stirlingSecond_eq_sum} "
   r"(\lean{StirlingBasisChange}); the finite-difference route through "
   r"\cref{thm:merged-bernoulli-difference} is not formalized"),
 'thm:merged-appell': ('Lean',
   r"Bernoulli: the derivative identity is Mathlib's \lean{Polynomial.derivative_bernoulli}, "
   r"the translation formula is \lean{Fabius.bernoulli_eval_add} (\lean{BernoulliAppell}) and "
   r"the explicit formula \cref{eq:merged-bernoulli-explicit} is the definition "
   r"\lean{Polynomial.bernoulli_def}; Euler: \lean{Fabius.eulerPolynomial} "
   r"(\lean{EulerPolynomials}, defined from $2/(\EulerE^t+1)$ as an Appell sequence), "
   r"\lean{Fabius.derivative_eulerPolynomial} and \lean{Fabius.eulerPolynomial_eval_add}, both "
   r"translation formulas being instances of the general Appell lemma "
   r"\lean{Fabius.appell_eval_add}"),
 'thm:merged-bernoulli-euler-basic': ('Lean',
   r"Mathlib: the difference identity \cref{eq:merged-bernoulli-difference} is "
   r"\lean{Polynomial.bernoulli_eval_one_add}, the reflection "
   r"\cref{eq:merged-bernoulli-reflection} is \lean{Polynomial.bernoulli_eval_one_sub}, and "
   r"$\beta_{2m+1}=0$ is \lean{bernoulli_eq_zero_of_odd}; the Euler difference identity "
   r"\cref{eq:merged-euler-difference} is \lean{Fabius.eulerPolynomial_eval_add_one_add} "
   r"(\lean{EulerPolynomials}), the Euler reflection \cref{eq:merged-euler-reflection} is "
   r"\lean{Fabius.eulerPolynomial_eval_one_sub} and $\mathsf E_{2m+1}(1/2)=0$ is "
   r"\lean{Fabius.eulerPolynomial_eval_half_odd} (\lean{EulerReflection})"),
 'thm:second-eulerian-recurrence': ('partial',
   r"\lean{Fabius.secondEulerian} (\lean{SecondOrderEulerian}) is defined by the recurrence "
   r"\cref{eq:second-eulerian-recurrence} (\lean{Fabius.secondEulerian_succ_succ}); the polynomial "
   r"recurrence \cref{eq:second-eulerian-poly-recurrence} is \lean{Fabius.secondEulerianSeries_succ} "
   r"(as power series) and the row sum \cref{eq:second-eulerian-row-sum} is "
   r"\lean{Fabius.sum_secondEulerian_eq_doubleFactorial}; the Stirling-permutation count is not "
   r"formalized"),
 'thm:second-eulerian-stirling-gf': ('Lean',
   r"\lean{Fabius.one_sub_X_pow_mul_diagStirlingSeries} (\lean{SecondOrderEulerian}), in $R[[t]]$ "
   r"over any commutative ring, by the induction of the text: $(1-t)F_{n+1}=tF_n'$ "
   r"(\lean{Fabius.one_sub_X_mul_diagStirlingSeries_succ}) and the polynomial recurrence"),
 'thm:typeB-eulerian': ('partial',
   r"\lean{Fabius.typeBEulerian} (\lean{TypeBEulerian}) is defined by the recurrence "
   r"\cref{eq:typeB-recurrence} (\lean{Fabius.typeBEulerian_succ_succ}); "
   r"\cref{eq:typeB-power-series} is \lean{Fabius.one_sub_X_pow_mul_oddPowSeries} in $R[[t]]$ "
   r"(from the type-$B$ Worpitzky identity \lean{Fabius.typeB_worpitzky}) and "
   r"\cref{eq:typeB-explicit} is \lean{Fabius.typeBEulerian_eq_sum_int}; the signed-permutation "
   r"count is not formalized"),
 'thm:bell-prime-power-shift': ('Lean',
   r"\lean{Fabius.bell_add_prime_pow_modEq} is \cref{eq:bell-prime-power-shift}; "
   r"\lean{Fabius.touchardPolynomial_add_prime_pow} is \cref{eq:touchard-prime-power-poly} "
   r"over $\FiniteField_p$; both from the operator identity \lean{Fabius.shift_pow_char_pow} "
   r"(module \lean{ShiftOperatorCharP})."),
 'thm:bell-period-bound': ('Lean',
   r"\lean{Fabius.bell_add_sum_prime_pow_modEq}: $N_p$ is a period modulo $p$ "
   r"(\lean{Fabius.shift_pow_period}, via the Fermat product "
   r"\lean{Fabius.prod_range_X_add_C_natCast}); \lean{Fabius.bell_period_dvd_sum_prime_pow}: "
   r"the least period divides $N_p$."),
 'thm:touchard-poly': ('Lean',
   r"\cref{eq:touchard-poly} is \lean{Fabius.touchardPolynomial_add_prime} "
   r"(\lean{TouchardPolyCongruence}), an identity in $(\mathbb Z/p)[x]$, read off from Spivey's "
   r"identity for Touchard polynomials (\lean{Fabius.touchardPolynomial_add_eq}) modulo $p$ with "
   r"\lean{Fabius.stirlingSecond_prime_eq_zero_zmod} ($p\mid\StirlingSecondKind pk$ for $1<k<p$); "
   r"\cref{eq:touchard} is \lean{Fabius.bell_add_prime_modEq} (\lean{TouchardCongruence})"),
 'thm:faa-partition': ('partial',
   r"the analytic statement is not formalized; its formal power-series analogue, the "
   r"coefficients of $F(G(t))$ through partial Bell polynomials, is "
   r"\lean{Fabius.egfA_subst_bellWeightSeries} (\lean{BellComposition})"),
 'thm:faa-multiplicity': ('partial',
   r"the analytic statement is not formalized; the formal power-series analogue "
   r"\lean{Fabius.egfA_subst_bellWeightSeries} carries the Bell-polynomial form, with the "
   r"partial Bell polynomials defined by the pointing recurrence rather than by the multiplicity "
   r"sum"),
 'thm:merged-raabe': ('Lean',
   r"\lean{Fabius.raabe} (\lean{RaabeMultiplication}), in the form "
   r"$\sum_{r<q}\beta_n(x+r/q)=q\,(1/q)^n\beta_n(qx)$, proved from the generating functions in "
   r"$(\RationalNumbers[x])[[t]]$ exactly as in the text; \cref{eq:merged-bernoulli-half} is "
   r"\lean{Fabius.bernoulli_eval_half}"),
 'lem:coeff-rules': ('partial',
   r"the formal rules are Mathlib's: \cref{eq:cauchy} is \lean{PowerSeries.coeff_mul} and "
   r"\cref{eq:der-coeff} is \lean{PowerSeries.coeff_derivative}; \cref{eq:geom-conv} is the "
   r"product with the geometric series (\lean{PowerSeries.coeff_mul} with "
   r"\lean{PowerSeries.coeff_mk}); Cauchy's coefficient formula and bound "
   r"\cref{eq:cauchy-coeff} are not formalized in this form"),
 'thm:merged-higher-quotient': ('partial',
   r"the analytic statement is not formalized; its formal power-series analogue, the "
   r"coefficients of $1/A$ through ordinary Bell polynomials, is "
   r"\lean{Fabius.coeff_reciprocalSeries} (\lean{OrdinaryBellComposition})"),
 'thm:merged-faulhaber': ('Lean',
   r"\lean{Fabius.sum_range_add_pow_eq_bernoulli_sub} (\lean{FaulhaberOffset}), telescoping "
   r"Mathlib's \lean{Polynomial.bernoulli_eval_one_add}; the case $x=0$ is also Mathlib's "
   r"\lean{Polynomial.sum_range_pow_eq_bernoulli_sub} (and \lean{sum_range_pow}, "
   r"\lean{sum_Ico_pow} in the Bernoulli-number form)"),
 'thm:eulerian-recurrence': ('partial',
   r"\lean{Fabius.eulerianNumber} is defined by this recurrence "
   r"(\lean{Fabius.eulerianNumber_succ_left}, \lean{Fabius.eulerianNumber_succ_succ}, "
   r"module \lean{EulerianNumbers}); the descent count and the polynomial form "
   r"\cref{eq:eulerian-poly-recurrence} are not formalized"),
 'thm:worpitzky': ('Lean',
   r"\lean{Fabius.worpitzky_nat} (natural numbers, all $n$) and "
   r"\lean{Fabius.worpitzky_polynomial} (in $\mathbb Q[x]$, with "
   r"\lean{Fabius.binomialPoly} for $\binom{x+k}{n}$) (\lean{EulerianNumbers})"),
 'cor:eulerian-power-sum': ('Lean',
   r"\lean{Fabius.sum_range_pow_succ_eq_sum_eulerianNumber} (\lean{EulerianNumbers}), "
   r"in the form $\sum_{r=0}^{m} r^{n+1}=\sum_k A(n+1,k)\binom{m+k+1}{n+2}$"),
}

ENV = re.compile(
    r'\\begin\{(theorem|proposition|lemma|corollary|identity|algorithm)\}'
    r'(?:\[([^\]]*)\])?\s*(?:\\label\{([^}]*)\})?')
CHAPTER = re.compile(r'\\chapter\*?\{([^}]*)\}')
SECTION_START = '\\section{Lean formalization register}'
BACK = '\\backmatter\n'


def tex_escape(t):
    return t.replace('&', '\\&').replace('%', '\\%').replace('_', '\\_').replace('#', '\\#')


# remove an existing register before scanning
if SECTION_START in s:
    i = s.index(SECTION_START)
    j = s.index(BACK)
    assert i < j
    s = s[:i] + s[j:]

rows = []
counters = {}
chapter = ''
events = [(m.start(), 'ch', m) for m in CHAPTER.finditer(s)] + \
         [(m.start(), 'env', m) for m in ENV.finditer(s)]
events.sort(key=lambda e: e[0])
for _, kind, m in events:
    if kind == 'ch':
        chapter = m.group(1)
        continue
    env, title, label = m.group(1), m.group(2), m.group(3)
    counters[env] = counters.get(env, 0) + 1
    key = label if label else '%s-%d' % (env, counters[env])
    status, decl = STATUS.get(key, ('none', ''))
    name = ('\\Cref{%s}' % label) if label else ('%s (unlabelled, no.~%d)' % (env, counters[env]))
    ttl = tex_escape(title) if title else ''
    rows.append((name, ttl, status, decl))

unknown = set(STATUS) - {r[0][6:-1] for r in rows if r[0].startswith('\\Cref{')}
assert not unknown, 'STATUS keys without a matching label: %s' % sorted(unknown)

n_lean = sum(1 for r in rows if r[2] == 'Lean')
n_part = sum(1 for r in rows if r[2] == 'partial')
n_none = sum(1 for r in rows if r[2] == 'none')

table = []
table.append(SECTION_START)
table.append('\\label{sec:lean-register}')
table.append(
 'Every theorem-like environment of this monograph is listed here with the status of its '
 'formalization in the Lean development \\path{Analysis/FabiusFunction/Lean/FabiusFunction} '
 '(Mathlib \\texttt{v4.32.0}).  \\emph{Lean} means that a public, compiled declaration proves '
 'the exact statement or a more general one (the generalization is then noted next to the '
 'result); \\emph{partial} means that a named part of the statement is proved and the rest is '
 'named; \\emph{none} means that no Lean counterpart exists yet.  A citation, a numerical '
 'check, or a plausible derivation does not count.  The register is generated from the '
 'source and must be regenerated when results are added.  Current totals: '
 '%d Lean, %d partial, %d none, of %d results.' % (n_lean, n_part, n_none, len(rows)))
table.append('')
table.append('\\begin{footnotesize}')
table.append('\\begin{longtable}{@{}p{0.16\\textwidth}p{0.22\\textwidth}p{0.08\\textwidth}p{0.40\\textwidth}@{}}')
table.append('\\toprule')
table.append('Result & Title & Status & Lean declarations (module) \\\\')
table.append('\\midrule')
table.append('\\endfirsthead')
table.append('\\toprule')
table.append('Result & Title & Status & Lean declarations (module) \\\\')
table.append('\\midrule')
table.append('\\endhead')
table.append('\\bottomrule')
table.append('\\endfoot')
for name, ttl, status, decl in rows:
    table.append('%s & %s & %s & %s \\\\' % (name, ttl, status, decl))
table.append('\\end{longtable}')
table.append('\\end{footnotesize}')
table.append('')

assert s.count(BACK) == 1
s = s.replace(BACK, '\n'.join(table) + '\n' + BACK)

io.open(path, 'w', encoding='utf-8', newline='\n').write(s)
print('rows', len(rows), 'Lean', n_lean, 'partial', n_part, 'none', n_none)
