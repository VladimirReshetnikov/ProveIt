# -*- coding: utf-8 -*-
r"""(Re)generate the Lean formalization register of
Combinatorial_Coefficient_Calculus.tex.

Run:  python combinatorial_lean_register.py <path-to-tex>

* First run: adds the \lean macro to the preamble and appends the register
  section before \backmatter.
* Later runs: replaces the existing register section (everything from
  '\section{Lean formalization register}' to '\backmatter') with a fresh one.

One row per theorem-like environment (theorem/proposition/lemma/corollary/
identity/algorithm), in document order, with a status column:

  Lean      -- an exact (or more general) Lean counterpart exists
  partial   -- a named part of the statement is proved; the rest is named
  none      -- no compiler-verified counterpart recorded yet (the default)

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
 'thm:merged-grid-certificate': ('Lean',
   r"\lean{Fabius.mvPolynomial_eq_of_eval_eq_on_grid} proves the difference-degree "
   r"criterion over any integral domain and finite variable type; "
   r"\lean{Fabius.mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_sub_le} and "
   r"\lean{Fabius.mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_le} give the two "
   r"natural-degree-bound forms, and \lean{Fabius.mvPolynomial_grid_eval_injective} "
   r"gives injectivity on the bounded-degree class (\lean{GridEvaluationCertificate})."),
 'thm:merged-crt-certificate': ('Lean',
   r"\lean{Fabius.int_prod_dvd_of_pairwise_coprime} and "
   r"\lean{Fabius.int_eq_zero_of_modEq_zero_of_natAbs_lt_prod} prove product "
   r"divisibility and the stronger full-product zero bound; "
   r"\lean{Fabius.int_eq_of_modEq_of_natAbs_sub_lt_prod}, "
   r"\lean{Fabius.int_eq_of_modEq_of_natAbs_add_lt_prod}, and "
   r"\lean{Fabius.int_eq_of_modEq_of_two_mul_natAbs_lt_prod} give the difference, "
   r"sum, and symmetric half-product equality certificates for finite families "
   r"of signed, pairwise coprime integer moduli (\lean{IntegerCRTCertificate})."),
 'lem:merged-formal-rescaling': ('Lean',
   r"\cref{eq:merged-formal-rescaling-derivative} is "
   r"\lean{Fabius.derivative_rescale} over every commutative semiring; "
   r"\lean{Fabius.derivative_rescale_exp}, \lean{Fabius.rescale_zero_exp}, and "
   r"\lean{Fabius.rescale_exp_add_one} give the exponential specializations "
   r"over every commutative $\RationalNumbers$-algebra "
   r"(\lean{ExponentialRescaling}). The general product law is Mathlib's "
   r"\lean{PowerSeries.exp_mul_exp_eq_exp_add}."),
 'thm:first-cycle': ('partial',
   r"recurrence and boundary values are Mathlib's \lean{Nat.stirlingFirst_succ_succ}, "
   r"\lean{Nat.stirlingFirst_succ_zero}, \lean{Nat.stirlingFirst_eq_zero_of_lt}; the "
   r"defining expansions are \lean{Fabius.ascPochhammer_eq_sum_monomial_stirlingFirst} and "
   r"\lean{Fabius.descPochhammer_eq_sum_monomial_signedStirlingFirst} "
   r"(\lean{StirlingBasisChange}); the permutation count itself is not formalized"),
 'thm:second-recurrence': ('partial',
   r"\lean{Nat.stirlingSecond_succ_succ}, \lean{Nat.stirlingSecond_succ_zero}, "
   r"\lean{Nat.stirlingSecond_eq_zero_of_lt} (Mathlib); the set-partition count, "
   r"which Mathlib leaves as a docstring claim, is \lean{Fabius.card_setPartitions} "
   r"(\lean{BellSetPartitions})"),
 'prop:merged-abel': ('none',
   r"\lean{Fabius.abelPolynomial}, \lean{Fabius.abelPolynomial_eval_add}, "
   r"\lean{Fabius.abelSeries_eq}, \lean{Fabius.exp_subst_eq_egfA_abelPolynomial} "
   r"(\lean{AbelPolynomialSeries}) state the EGF for every solution "
   r"of $T=te^{-aT}$ over a commutative rational algebra, not only the constructed one. "
   r"The polynomial definition needs only a commutative ring, but the current "
   r"binomial-identity proof also assumes a rational algebra. Compiler validation is pending."),
 'thm:merged-frechet-faa': ('Lean',
   r"Mathlib's \lean{iteratedFDeriv_comp} (ContDiff/Comp.lean), unfolded with "
   r"\lean{FormalMultilinearSeries.taylorComp} and "
   r"\lean{FormalMultilinearSeries.compAlongOrderedFinpartition_apply}. "
   r"The statement includes local $C^n$ hypotheses and explicitly uses "
   r"\lean{OrderedFinpartition}'s increasing-maximum block order. "
   r"No symmetry conversion is required; the separate partial-Bell regrouping remains open."),
 'thm:bell-poly-partitions': ('Lean',
   r"\lean{Fabius.partialBell_eq_sum_setPartitions} and "
   r"\lean{Fabius.bell_complete_eq_sum_allSetPartitions} (\lean{BellSetPartitions}), "
   r"over any commutative semiring of weights; the per-type count "
   r"\cref{cor:partition-type} is not covered"),
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
 'thm:stirling-egfs': ('Lean',
   r"\lean{Fabius.exp_sub_one_pow}, \lean{Fabius.egf_stirlingSecond}, "
   r"\lean{Fabius.negLogOneSub_pow}, \lean{Fabius.egf_stirlingFirst}, "
   r"\lean{Fabius.log_pow} (\lean{StirlingGeneratingFunctions}), as formal power series "
   r"over any commutative $\mathbb Q$-algebra.  \cref{eq:second-double-egf} is "
   r"\lean{Fabius.exp_subst_smul_exp_sub_one} (\lean{BellHomogeneity}), which proves "
   r"$\exp(y(\EulerE^z-1))=\sum_n\bigl(\sum_k\StirlingSecondKind nk y^k\bigr)z^n/n!$ "
   r"for every scalar $y$ of the coefficient algebra; taking that algebra to be "
   r"$\mathbb Q[y]$ and the scalar to be $y$ recovers the display, so the content is "
   r"formalized even though no Lean statement writes $y$ as a formal variable"),
 'thm:stirling-transform': ('Lean',
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
 'thm:merged-weighted-binomial-translation': ('Lean',
   r"\lean{Appell.translate_eq_sum}, \lean{Appell.translate_translate}, "
   r"\lean{Appell.binomialConv_translate}, and \lean{Appell.translate_injective} "
   r"(\lean{AppellSequence}); semiring identities, with additive cancellation "
   r"only for injectivity"),
 'cor:merged-weighted-binomial-inversion': ('Lean',
   r"\lean{Appell.weighted_binomial_inversion_iff}, \lean{Appell.translate_neg_translate}, "
   r"\lean{Appell.translate_translate_neg}, and "
   r"\lean{Appell.binomialConv_translate_neg_translate} (\lean{AppellSequence}), "
   r"over arbitrary commutative rings"),
 'thm:merged-binomial-inversion': ('Lean',
   r"the equivalence of \cref{eq:merged-binomial-forward,eq:merged-binomial-backward} is "
   r"\lean{Fabius.binomial_inversion_iff} (additive commutative groups) and "
   r"\lean{Fabius.binomial_inversion_ring_iff} (commutative rings) "
   r"(\lean{BinomialInversion}), with the kernel orthogonality "
   r"\lean{Fabius.sum_Icc_neg_one_pow_choose_mul_choose}; \cref{eq:merged-binomial-egf} is "
   r"\lean{Fabius.egfA_eq_exp_mul_iff} and \lean{Fabius.egfA_eq_altSeries_mul_iff} "
   r"(\lean{BinomialInversionEGF}), each an iff with its sequence form, together with "
   r"\lean{Fabius.egfA_eq_exp_mul_iff_egfA_eq_altSeries_mul} for the equivalence of the two "
   r"generating-function equations"),
 'thm:bell-poly-recurrences': ('Lean',
   r"\lean{Fabius.partialBell} is defined by \cref{eq:partial-bell-recurrence} "
   r"(\lean{Fabius.partialBell_succ_succ}, \lean{Fabius.partialBell_succ_succ_eq_binomialConv}); "
   r"\cref{eq:complete-bell-recurrence} is Mathlib-free \lean{Bell.complete_succ} together with "
   r"\lean{Fabius.bell_complete_eq_sum_partialBell} (\lean{PartialBellPolynomials}, "
   r"\lean{BellPolynomialInversion}); the boundary values are \lean{Fabius.partialBell_zero_succ}, "
   r"\lean{Fabius.partialBell_succ_zero}, \lean{Fabius.partialBell_eq_zero_of_lt}"),
 'thm:bell-poly-egf': ('Lean',
   r"all five identities, as formal power series over any commutative $\mathbb Q$-algebra.  "
   r"The first is \lean{Fabius.bellWeightSeries_pow} and the third "
   r"\lean{Fabius.exp_subst_bellWeightSeries} (\lean{BellGeneratingFunctions}); the exponential "
   r"bivariate form is \lean{Fabius.exp_subst_smul_bellWeightSeries} "
   r"(\lean{ExponentialFormula}); the ordinary Bell polynomials are "
   r"\lean{Fabius.ordPartialBell} with \cref{eq:ordinary-bell-ogf} as "
   r"\lean{Fabius.coeff_pow_eq_ordPartialBell} (\lean{OrdinaryBellComposition}); and "
   r"\cref{eq:ordinary-bell-bivariate} is \lean{Fabius.coeff_exp_subst_smul} "
   r"(\lean{OrdinaryBellBivariate}).  In both bivariate statements $u$ is a scalar parameter "
   r"rather than a second formal variable"),
 'thm:bell-poly-specializations': ('Lean',
   r"\cref{eq:bell-first-specialization} is \lean{Fabius.partialBell_factorial_pred}, "
   r"\cref{eq:bell-factorial-complete} is \lean{Fabius.bell_complete_factorial_pred} "
   r"(\lean{BellFactorialRowSum}), "
   r"\cref{eq:bell-second-specialization} is \lean{Fabius.partialBell_one}, "
   r"\cref{eq:bell-number-specialization} is \lean{Fabius.bell_complete_one}, "
   r"\cref{eq:bell-lah-specialization} is \lean{Fabius.partialBell_factorial} "
   r"(\lean{PartialBellPolynomials}, \lean{BellGeneratingFunctions}), and the Touchard form "
   r"\cref{eq:touchard-bell-specialization} is \lean{Fabius.bell_complete_const_eq_touchard_eval} "
   r"(\lean{BellHomogeneity})"),
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
   r"and \lean{Bell.cumulant_complete} (\lean{BellPolynomialInversion}).  The more general "
   r"locally-inverse transform \cref{eq:general-bell-inverse}, which the text states after "
   r"this theorem rather than inside it, is not formalized"),
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
 'thm:normal-order': ('partial',
   r"\lean{Fabius.iterate_X_mul_derivative} (\cref{eq:normal1}) and "
   r"\lean{Fabius.xkDk_eq_sum_signedStirlingFirst} (\cref{eq:normal2}, by Stirling inversion) in "
   r"\lean{StirlingNormalOrder}, as identities of operators applied to an arbitrary polynomial "
   r"over any commutative ring; the falling-factorial form $\FallingFactorial{xD}{n}$ and the "
   r"operator series \cref{eq:der-from-diff,eq:diff-from-der} are not formalized"),
 'thm:paired-sums': ('Lean',
   r"\lean{StirlingSummations}: \cref{eq:first-two-sums} is "
   r"\lean{Fabius.stirlingFirst_succ_succ_eq_sum_choose} (module "
   r"\lean{StirlingBasisChange}) and "
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
 'thm:bell-inversions': ('Lean',
   r"\cref{eq:bell-inversion-one} is \lean{Fabius.bell_eq_sum_neg_one_pow_choose_bell_succ} "
   r"(\lean{BellShiftEGF}), by \lean{Fabius.binomial_inversion_ring} applied to "
   r"\lean{Fabius.bell_succ_eq_sum_choose}; \cref{eq:bell-inversion-two} is "
   r"\lean{Fabius.sum_choose_bell_add_eq_sum_neg_one_pow} (\lean{BellInversionTwo}), proved "
   r"not by the Poisson argument but by showing both sides satisfy "
   r"$H(n,k+1)=H(n+1,k)-H(n,k)$ and agree at $k=0$"),
 'thm:second-reverse-recurrences': ('partial',
   r"\cref{eq:second-triangular-explicit} is "
   r"\lean{Fabius.stirlingSecond_eq_pow_div_factorial_sub_sum} (\lean{StirlingTriangularExplicit}), "
   r"for all $n,k$ with the $r=0$ term included; \cref{eq:second-reverse-column} is "
   r"\lean{Fabius.second_reverse_column} (\lean{StirlingSecondReverseColumn}), by the "
   r"column differential equation $(1-\EulerE^{-x})F_k'=kF_k$ "
   r"(\lean{Fabius.one_sub_altSeries_mul_derivative_egfA_stirlingSecond}); "
   r"new source \lean{Fabius.second_reverse_row} (\lean{StirlingSecondReverseRowIdentity}) "
   r"supplies \cref{eq:second-reverse-row} over every commutative ring by extracting "
   r"coefficients from \lean{Fabius.subst_logTail}; \lean{Fabius.second_reverse_row_sum} "
   r"gives the unrestricted rational-index version.  Compiler validation of the new "
   r"row identities is pending."),
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
 'thm:ordered-bell': ('partial',
   r"\lean{Fabius.fubini} is defined by \cref{eq:ordered-bell-stirling}; "
   r"\cref{eq:ordered-bell-egf} is \lean{Fabius.two_sub_exp_mul_egfA_fubini} (via "
   r"\lean{Fabius.egfA_fubini}: the generating function is $1/(1-u)$ at $u=\EulerE^t-1$) and "
   r"\cref{eq:ordered-bell-recurrence} is \lean{Fabius.fubini_succ} (\lean{OrderedBell}); the "
   r"ordered-partition count itself is not formalized"),
 'thm:second-ogf': ('Lean',
   r"\lean{Fabius.prod_one_sub_mul_X_mul_stirlingColumnOGF} and "
   r"\lean{Fabius.stirlingColumnOGF_eq_prod_mk_pow} (\lean{StirlingOrdinaryGF}) prove the "
   r"formal inverse and finite geometric-product identities.  The compiled "
   r"\lean{StirlingCompleteHomogeneous} declarations "
   r"\lean{Fabius.stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn}, "
   r"\lean{Fabius.stirlingSecond_add_eq_completeHomogeneousEvalOn}, "
   r"\lean{Fabius.stirlingSecond_eq_completeHomogeneousEvalOn_of_le}, "
   r"\lean{Fabius.stirlingSecond_add_eq_completeHomogeneousEval}, "
   r"\lean{Fabius.stirlingSecond_add_eq_eval_hsymm}, and "
   r"\lean{Fabius.stirlingSecond_add_eq_sum_finsuppAntidiag} cover inverse uniqueness, the "
   r"$n=k+r$ and $n\ge k$ complete-homogeneous identities over every commutative semiring, universal "
   r"\lean{MvPolynomial.hsymm} evaluation, and the explicit multiplicity sum.  Its "
   r"\lean{Fabius.pow_mul_descPochhammer_eval_inv_eq_prod_one_sub_natCast_mul} and "
   r"\lean{Fabius.prod_inv_one_sub_natCast_mul_eq_inv_pow_mul_descPochhammer_eval_inv} cover "
   r"the scalar falling-factorial factorization under $x\ne0$ and its reciprocal under "
   r"nonvanishing of every $1-jx$."),
 'thm:stirling-symmetric-semirings': ('partial',
   r"The second-kind identities are compiled as "
   r"\lean{Fabius.stirlingSecond_add_eq_completeHomogeneousEvalOn} and "
   r"\lean{Fabius.stirlingSecond_eq_completeHomogeneousEvalOn_of_le} in "
   r"\lean{StirlingCompleteHomogeneous}, over every commutative semiring.  New source "
   r"\lean{Fabius.stirlingFirst_eq_sum_powersetCard} and "
   r"\lean{Fabius.stirlingFirst_eq_esymm} in \lean{StirlingSymmetricFunctions} supplies "
   r"the first-kind identities; compiler validation of those additions is pending."),
 'cor:stirling-symmetric-scaling': ('none',
   r"New source: \lean{Fabius.completeHomogeneousEvalOn_scaled_range} and "
   r"\lean{Fabius.esymm_scaled_range} in \lean{StirlingSymmetricFunctions}; "
   r"compiler validation pending."),
 'thm:eulerian-power-series': ('Lean',
   r"\lean{Fabius.one_sub_X_pow_mul_succPowSeries} (the identity "
   r"$(1-t)^{n+1}\sum_m(m+1)^nt^m=\TypeAEulerianPolynomial{n}(t)$ in $R[[t]]$) and "
   r"\lean{Fabius.eulerianNumber_eq_sum_int} (\lean{EulerianGeneratingFunctions}); the "
   r"symmetry \cref{eq:eulerian-symmetry} is \lean{Fabius.eulerianNumber_symm} and "
   r"\cref{eq:eulerian-k1} is \lean{Fabius.eulerianNumber_one_right}"),
 'thm:merged-riordan': ('partial',
   r"\lean{Fabius.expRiordan_action}, \lean{Fabius.expRiordan_mul}, "
   r"\lean{Fabius.expRiordan_mul_inverse} (\lean{ExponentialRiordan}) prove the action, "
   r"product, and a conditional one-sided inverse law, assuming the inverse series and "
   r"$g\,(h\circ f)=1$.  Construction of these inverse series from the theorem's unit "
   r"hypotheses and the full two-sided inverse statement remain to be formalized.  "
   r"The Stirling examples are \lean{Fabius.expRiordan_one_exp_sub_one} and "
   r"\lean{Fabius.expRiordan_one_log}."),
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
 'thm:weighted-bell-shift': ('Lean',
   r"\lean{Fabius.weighted_bell_shift} is \cref{eq:weighted-bell-shift}, "
   r"\lean{Fabius.weighted_bell_shift_one} is \cref{eq:weighted-bell-k1} and "
   r"\lean{Fabius.sum_signedStirlingFirst_mul_bell_eq} is \cref{eq:weighted-bell-special}, "
   r"over any commutative ring, from the umbral shift \lean{Fabius.bellUmbra_descPochhammer_mul} "
   r"(module \lean{BellUmbra})."),
 'thm:second-parity': ('Lean',
   r"\cref{eq:second-parity-binomial} is \lean{Fabius.stirlingSecond_modEq_choose_two} "
   r"(module \lean{StirlingParity}), for $1\le k\le n$, from the column series modulo $2$, "
   r"\lean{Fabius.stirlingColumnOGF_zmod_two}.  The bitwise form "
   r"\cref{eq:second-parity-bit} is \lean{Fabius.stirlingSecond_odd_iff} and the central "
   r"case is \lean{Fabius.stirlingSecond_two_mul_odd_iff} (module "
   r"\lean{StirlingParityBitwise}), both resting on Kummer's theorem at the prime two, "
   r"\lean{Fabius.odd_choose_add_iff}, which is proved there from Mathlib's Lucas "
   r"theorem by induction on the binary digits."),
 'thm:merged-catalan-reflection': ('Lean',
   r"The Dyck-word count is Mathlib's \lean{DyckWord.card_dyckWord_semilength_eq_catalan}; "
   r"$\CatalanNumber n=\binom{2n}{n}/(n+1)$ is \lean{catalan_eq_centralBinom_div} and the "
   r"difference form is \lean{Fabius.catalan_succ_eq_choose_sub_choose} "
   r"(module \lean{CatalanGeneratingFunction})."),
 'thm:merged-catalan-first-return': ('partial',
   r"$C=1+zC^2$ is \lean{Fabius.catalanSeries_eq} and its uniqueness among power series "
   r"\lean{Fabius.eq_catalanSeries_of_eq_one_add_X_mul_sq} (module "
   r"\lean{CatalanGeneratingFunction}); the square-root closed form is "
   r"\lean{Fabius.sqrtOf_one_sub_four_X} (\lean{SquareRootSeries}), where $\sqrt{\cdot}$ is "
   r"the formal square root \lean{Fabius.sqrtOf} of a series with constant term $1$, defined "
   r"as $\exp(\tfrac12\log)$ and unique by \lean{Fabius.sqrt_unique}; the radius of "
   r"convergence and the branch cut are analytic and are not formalized."),
 'thm:first-reverse-recurrences': ('Lean',
   r"\cref{eq:first-reverse-row} is \lean{Fabius.first_reverse_row} and "
   r"\cref{eq:first-reverse-column} is \lean{Fabius.first_reverse_column} (module "
   r"\lean{StirlingFirstReverse}), the first from the rising factorial, the second by "
   r"comparing exponential generating functions (\lean{Fabius.egfA_first_reverse_column})."),
 'thm:merged-bernoulli-difference': ('Lean',
   r"\cref{eq:merged-bernoulli-newton-basis} is \lean{Fabius.bernoulli_eq_sum_fwdDiff} (module "
   r"\lean{BernoulliNewtonBasis}), an identity in $\mathbb Q[x]$ with $\Delta^kx^n$ written out as "
   r"$\sum_j(-1)^{k-j}\binom kj(x+j)^n$; the truncated Gregory composition is "
   r"\lean{Fabius.X_pow_dvd_bernoulliPowerSeries_sub_gregory}."),
 'cor:merged-bernoulli-stirling-second-proof': ('Lean',
   r"\lean{Fabius.bernoulli_eq_sum_fwdDiff_zero} (module \lean{BernoulliNewtonBasis}): "
   r"$\beta_n=\sum_k\frac{(-1)^k}{k+1}\Delta^k0^n$, and with the surjection formula "
   r"\lean{Fabius.factorial_mul_stirlingSecond_eq_sum} this is "
   r"\lean{Fabius.bernoulli_eq_sum_stirlingSecond}."),
 'thm:merged-norlund-calculus': ('partial',
   r"For natural orders $\alpha,\gamma\in\mathbb N$ (module \lean{NorlundPolynomials}, "
   r"$\beta_n^{(a)}$ defined by \lean{Fabius.norlund}): \cref{eq:merged-norlund-appell} is "
   r"\lean{Fabius.derivative_norlund_succ}, \cref{eq:merged-norlund-translation} is "
   r"\lean{Fabius.norlund_eval_add}, \cref{eq:merged-norlund-difference} is "
   r"\lean{Fabius.norlund_succ_eval_add_one_sub} and \cref{eq:merged-norlund-convolution} is "
   r"\lean{Fabius.norlund_add_eval_add}. The arbitrary-order source in "
   r"\lean{NorlundGeneralized}, including "
   r"\lean{Fabius.generalizedNorlund_succ_eval_add_one_sub} and "
   r"\lean{Fabius.generalizedNorlund_eval_add_one_sub}, awaits compilation; "
   r"the row is not promoted on source review alone."),
 'lem:merged-complete-bell-multiplicities': ('none',
   r"The new \lean{BellCompletePartitions} source states "
   r"\lean{Fabius.bell_complete_eq_sum_weightedPartitions}, "
   r"\lean{Fabius.inv_factorial_smul_complete_eq_sum_weightedPartitions}, and "
   r"\lean{Fabius.bell_complete_eq_sum_div_weightedPartitions}, including degree zero "
   r"and unrestricted zeroth input. It shares the existing complete-Bell and "
   r"weighted-partition bridges, but still awaits compilation. "
   r"This is an integer-multiplicity sum, not a labelled-set partition theorem."),
 'thm:bell-poly-derivatives': ('partial',
   r"\cref{eq:partial-bell-derivative} is \lean{Fabius.pderiv_partialBell_succ} and "
   r"\cref{eq:complete-bell-derivative} is \lean{Fabius.pderiv_bellComplete} (module "
   r"\lean{BellDerivative}), in $\mathbb Q[x_1,x_2,\dots]$ via the coefficientwise derivation "
   r"\lean{Fabius.coeffDerivation}; the chain rule \cref{eq:bell-poly-chain} is not formalized."),
 'thm:merged-moment-cumulant': ('partial',
   r"In the block-size form: \lean{Bell.complete} and \lean{Bell.cumulant} are mutually inverse "
   r"(\lean{Bell.complete_cumulant}, \lean{Bell.cumulant_complete}, module "
   r"\lean{BellPolynomialInversion}) and $M=\EulerE^K$ is \lean{Fabius.exp_subst_bellWeightSeries}; "
   r"$K=\log M$ is now \lean{Fabius.logOf_egfA} together with "
   r"\lean{Fabius.cumulant_eq_cumulantSum} (\lean{CumulantBellFormula}), which also "
   r"gives the closed form $\kappa_n=\sum_k(-1)^{k-1}(k-1)!\,\ExponentialPartialBellPolynomial nk(m)$, resting on the formal $\exp\circ\log$ "
   r"inverse \lean{Fabius.exp_subst_logOf} (\lean{ExpLog}); the sums over set "
   r"partitions are not formalized."),
 'thm:associated-stirling-recurrence': ('partial',
   r"With $\mathsf S_r$ defined as the partial Bell polynomial with weights $[j\ge r]$ "
   r"(\lean{Fabius.associatedStirling}, module \lean{AssociatedStirling}): "
   r"\cref{eq:associated-stirling-recurrence} is \lean{Fabius.associatedStirling_succ_succ} and "
   r"\cref{eq:associated-stirling-egf} is \lean{Fabius.egfA_associatedStirling}; the block-size "
   r"count is not formalized."),
 'thm:r-stirling-recurrence': ('partial',
   r"With $\StirlingSecondKind nk_{\!r}$ defined by the recurrence (\lean{Fabius.rStirling}, "
   r"module \lean{RStirling}): \cref{eq:r-stirling-recurrence} is "
   r"\lean{Fabius.rStirling_succ_succ}, the explicit formula "
   r"$\StirlingSecondKind{n+r}{k+r}_{\!r}=\sum_j\binom nj\StirlingSecondKind jk r^{n-j}$ is "
   r"\lean{Fabius.rStirlingShift_eq_sum} and \cref{eq:r-stirling-egf} is "
   r"\lean{Fabius.egfA_rStirlingPoly}; the distinct-blocks count is not formalized."),
 'thm:merged-cauchy-polynomials': ('partial',
   r"Module \lean{CauchyPolynomials} defines $b_n$ by \cref{eq:merged-bernoulli-second-egf} "
   r"(\lean{Fabius.cauchyPoly}): \cref{eq:merged-cauchy-derivative} is "
   r"\lean{Fabius.derivative_cauchyPoly_succ}, \cref{eq:merged-cauchy-difference} is "
   r"\lean{Fabius.cauchyPoly_succ_eval_add_one_sub}, \cref{eq:merged-cauchy-addition} is "
   r"\lean{Fabius.cauchyPoly_eval_add}, \cref{eq:merged-cauchy-explicit} is "
   r"\lean{Fabius.cauchyPoly_succ_eq} and \cref{eq:merged-cauchy-stirling-numbers} is "
   r"\lean{Fabius.cauchyPoly_eval_zero}; the integral representation "
   r"\cref{eq:merged-cauchy-integral} and the reflection \cref{eq:merged-cauchy-reflection} "
   r"are not formalized."),
 'lem:coeff-rules': ('partial',
   r"The three formal rules are \lean{Fabius.coeff_mul_eq_sum_range} "
   r"(\cref{eq:cauchy}), \lean{Fabius.coeff_derivative_eq} (\cref{eq:der-coeff}) and "
   r"\lean{Fabius.coeff_mul_geomSeries} (\cref{eq:geom-conv}), over any commutative "
   r"ring (module \lean{CoefficientRules}); the analytic Cauchy coefficient formula "
   r"\cref{eq:cauchy-coeff} is not formalized."),
 'thm:merged-multinomial-leibniz': ('partial',
   r"The two-factor case, in the formal reading the proof itself sanctions, is "
   r"\lean{Fabius.derivative_iterate_mul} (module \lean{IteratedLeibniz}): "
   r"$(\Differential/\Differential t)^n(fg)=\sum_k\binom nk f^{(k)}g^{(n-k)}$ in $R[[t]]$ over any "
   r"commutative ring; the general $q$-factor multinomial form is not formalized."),
 'thm:merged-norlund-bell-diagonal': ('partial',
   r"The three diagonal displays are formalized for natural orders and rational evaluation points (module "
   r"\lean{NorlundDiagonal}): \cref{eq:merged-norlund-polynomial-diagonal} is "
   r"\lean{Fabius.norlund_diagonal}, \cref{eq:merged-norlund-number-diagonal} is "
   r"\lean{Fabius.norlund_eval_zero_diagonal} and \cref{eq:merged-norlund-diagonal} is "
   r"\lean{Fabius.coeff_bernoulliPowerSeries_pow_succ}. "
   r"The arbitrary-order Bell and multiplicity constructions in "
   r"\lean{NorlundGeneralized} and \lean{BellCompletePartitions} await compilation. "
   r"Transport of the polynomial diagonal to an arbitrary coefficient algebra remains open."),
 'thm:merged-narayana': ('partial',
   r"Module \lean{NarayanaNumbers} defines $N(n,k)$ by the division-free determinant "
   r"$\binom nk\binom{n-1}{k-1}-\binom n{k-1}\binom{n-1}k$ over $\IntegerNumbers$ "
   r"(\lean{Fabius.narayana}), which vanishes outside $1\le k\le n$ without a side condition: "
   r"\cref{eq:merged-narayana} is \lean{Fabius.narayana_mul} in the cleared form "
   r"$nN(n,k)=\binom nk\binom n{k-1}$, the symmetry is \lean{Fabius.narayana_symm} and the row "
   r"sum $\sum_kN(n,k)=\CatalanNumber n$ is \lean{Fabius.sum_narayana}; the peak-counting "
   r"interpretation and the bivariate generating function \cref{eq:merged-narayana-gf} are not "
   r"formalized."),
 'thm:mod-h-structure': ('partial',
   r"\cref{eq:mod-h-block-product} is \lean{Fabius.stirlingFirst_cast_eq_coeff_block} (module "
   r"\lean{StirlingFirstModH}), together with the rising-factorial product form "
   r"\lean{Fabius.ascPochhammer_eq_prod_range}; the eventual vanishing that makes the spectral "
   r"reading vacuous is \lean{Fabius.stirlingFirst_cast_eq_zero_of_lt}.  The linear recurrence "
   r"over $\IntegerNumbers/h\IntegerNumbers$ and the Jordan decomposition are not formalized."),
 'thm:lagrange-burmann': ('partial',
   r"\cref{eq:lagrange-burmann} is \lean{Fabius.Lagrange.coeff_subst_derivative} and "
   r"\cref{eq:lagrange-basic} is \lean{Fabius.Lagrange.coeff_subst_id} (module "
   r"\lean{LagrangeInversion}), over any commutative $\RationalNumbers$-algebra and in the "
   r"division-free form $n[z^n]H(g)=[w^{n-1}]H'\phi^n$, from the division-free core "
   r"\lean{Fabius.Lagrange.coeff_subst_mul_derivative}.  The solution $g$ of "
   r"\cref{eq:lagrange-functional} is constructed, not assumed "
   r"(\lean{Fabius.Lagrange.solution}, \lean{Fabius.Lagrange.solution_eq}), so "
   r"\lean{Fabius.Lagrange.coeff_solution_subst_derivative} and "
   r"\lean{Fabius.Lagrange.coeff_solution} concern the constructed solution under the "
   r"inverse-series hypothesis.  New source in "
   r"\lean{LagrangeInversionUniqueness} supplies uniqueness over any commutative ring and "
   r"\cref{eq:lagrange-burmann-alt} via \lean{Fabius.Lagrange.coeff_solution_subst_alt}; "
   r"compiler validation pending."),
 'thm:lambert-W-zero': ('partial',
   r"The series \cref{eq:lambert-W-zero} is \lean{Fabius.coeff_lambertW} (module "
   r"\lean{LambertWSeries}), for \lean{Fabius.lambertW} constructed as the Lagrange solution of "
   r"$W=z\EulerE^{-W}$; the defining equation in the form $W\EulerE^W=z$ is "
   r"\lean{Fabius.lambertW_mul_exp_subst}.  The radius of convergence $\EulerE^{-1}$ is analytic "
   r"and is not formalized."),
 'thm:fuss-series': ('partial',
   r"\cref{eq:fuss-series} is \lean{Fabius.coeff_fussSolution} together with "
   r"\lean{Fabius.coeff_fussSolution_eq_zero} (module \lean{FussCatalanSeries}), for "
   r"\lean{Fabius.fussSolution} constructed as the Lagrange solution; the polynomial form of the "
   r"defining equation is \lean{Fabius.fussSolution_sub_pow}.  The radius "
   r"\cref{eq:fuss-radius} and the boundary convergence are analytic and are not formalized."),
 'thm:inverse-bell-coeff': ('Lean',
   r"\lean{InverseBellCoefficients}: \cref{eq:inverse-bell-coeff} is "
   r"\lean{Fabius.factorial_mul_coeff_reversion} (sum from $k=0$) and "
   r"\lean{Fabius.factorial_mul_coeff_reversion_of_two_le} (sum from $k=1$, for $n\ge2$), "
   r"with $g_1=f_1^{-1}$ as \lean{Fabius.coeff_reversion_one}; the reversion itself is "
   r"constructed, not assumed, and \lean{Fabius.subst_egfA_reversion} proves it inverts $f$"),
 'thm:second-eulerian-first-diagonal': ('partial',
   r"\lean{Fabius.stirlingFirst_diagonal} (\lean{StirlingFirstDiagonal}), with the upper "
   r"index written as $m+p$ so that the range is explicit and the out-of-range convention "
   r"is not needed; proved by double induction on the termwise binomial identity "
   r"\lean{Fabius.choose_termwise} rather than through the generating function, so the "
   r"formal proof stays in $\mathbb N$.  The polynomial continuation displayed in the "
   r"theorem is not formalized: it follows from the integer identity, but stating it needs a "
   r"definition of the continuation of $c$ in its upper index, which the corpus does not have"),
 'thm:diamond-bell': ('Lean',
   r"\lean{Fabius.diamondPow_apply} and \lean{Fabius.partialBell_eq_diamondPow_div} "
   r"(\lean{DiamondPower}); the diamond product is \lean{Bell.binomialConv}, and "
   r"\lean{Fabius.binomialConv_eq_sum_Ico} checks that the two extreme terms the source "
   r"omits do vanish, so the two definitions agree.  Raw diamond powers and their "
   r"zero/successor/one laws hold over every "
   r"commutative semiring; the EGF and partial-Bell bridge retain commutative "
   r"$\RationalNumbers$-algebra hypotheses.  The proof is the source's: "
   r"\lean{Fabius.egfA_mul} makes the generating function of the power a power "
   r"(\lean{Fabius.egfA_diamondPow}), and \lean{Fabius.bellWeightSeries_pow} reads off its "
   r"coefficients."),
 'thm:bell-symmetric-functions': ('Lean',
   r"\cref{eq:elementary-via-bell} is \lean{Fabius.esymm_eq_bell_complete} and its sign "
   r"variant \lean{Fabius.esymm_eq_neg_bell_complete} (\lean{ElementarySymmetricBell}), for a "
   r"finite family in any commutative $\mathbb Q$-algebra; \cref{eq:powersum-via-bell} is "
   r"\lean{Fabius.newton_power_sum} in cleared form and \lean{Fabius.power_sum_eq} in the "
   r"divided form (\lean{NewtonPowerSumBell}), with its second form, through the ordinary "
   r"partial Bell polynomials, as \lean{Fabius.power_sum_eq_ord_bell} "
   r"(\lean{PowerSumOrdinaryBell}).  All of it rests on \lean{Fabius.exp_subst_logOf} "
   r"(\lean{ExpLog}), which supplies the $\exp\circ\log$ inverse Mathlib lacks, and on "
   r"\lean{Fabius.cumulant_eq_cumulantSum} (\lean{CumulantBellFormula}); the two forms of "
   r"\cref{eq:powersum-via-bell} are the exponential and the ordinary reading of the same "
   r"$\log E$, equated"),
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
   r"\cref{eq:eulerian-recurrence} defines \lean{Fabius.eulerianNumber} (\lean{EulerianNumbers}, "
   r"\lean{Fabius.eulerianNumber_succ_succ}), with the textbook indexing as "
   r"\lean{Fabius.eulerianNumber_succ_left}; \cref{eq:eulerian-poly-recurrence} is "
   r"\lean{Fabius.eulerianPolynomial_succ} (\lean{EulerianPolynomialRecurrence}) over any "
   r"commutative ring; the descent count itself is not formalized"),
 'thm:worpitzky': ('Lean',
   r"\lean{Fabius.worpitzky_nat} (natural numbers, all $n$) and "
   r"\lean{Fabius.worpitzky_polynomial} (in $\mathbb Q[x]$, with "
   r"\lean{Fabius.binomialPoly} for $\binom{x+k}{n}$) (\lean{EulerianNumbers})"),
 'cor:eulerian-power-sum': ('Lean',
   r"\lean{Fabius.sum_range_pow_succ_eq_sum_eulerianNumber} (\lean{EulerianNumbers}), "
   r"in the form $\sum_{r=0}^{m} r^{n+1}=\sum_k A(n+1,k)\binom{m+k+1}{n+2}$"),
 'alg:merged-exp-log-power': ('Lean',
   r"\cref{eq:merged-alg-log} is the reflected-index form of "
   r"\lean{Fabius.SaddleExpansion.logCoeff_succ}, with "
   r"\lean{Fabius.SaddleExpansion.logSeries_eq_logOf} identifying that recurrence with the "
   r"formal logarithm (\lean{SaddleLogExpansionAlgebra}, "
   r"\lean{SaddleLogExpansionPowerSeries}); \cref{eq:merged-alg-exp} is "
   r"\lean{Fabius.coeff_exp_subst_recurrence} (\lean{UnitSeriesBellCoefficients}) in the "
   r"denominator-cleared form $na_n=\sum_{j=1}^n j\ell_j a_{n-j}$. "
   r"\cref{eq:merged-alg-power} is "
   r"\lean{Fabius.coeff_fallingSeries_subst_sub_one_recurrence} "
   r"(\lean{UnitSeriesPowerRecurrence}), from "
   r"\lean{Fabius.mul_derivative_fallingSeries_subst_sub_one} and the "
   r"commutative-ring identity \lean{Fabius.coeff_recurrence_of_mul_derivative_eq}. "
   r"The power is formal binomial substitution with constant coefficient one; "
   r"all three divided recurrences hold over a commutative $\mathbb Q$-algebra"),
 'alg:merged-newton-reciprocal': ('Lean',
   r"\lean{NewtonReciprocal}: initialization \lean{Fabius.X_dvd_one_sub_mul_C}, exact "
   r"residual squaring \lean{Fabius.one_sub_mul_newtonReciprocalStep}, precision doubling "
   r"\lean{Fabius.X_pow_dvd_one_sub_mul_newtonReciprocalStep}, coefficient agreement "
   r"\lean{Fabius.coeff_mul_newtonReciprocalStep}, and actual truncation "
   r"\lean{Fabius.X_pow_dvd_one_sub_mul_trunc_newtonReciprocalStep}; all over an arbitrary "
   r"commutative ring and checked by focused compilation."),
}

# A dict literal keeps the LAST of two equal keys and reports nothing, so a
# duplicated label silently replaces one crosswalk by another.  That happened
# once, to lem:coeff-rules, and the row that shipped was the weaker of the two.
# Re-read this file and refuse to run if any label is written twice.
_rows = re.findall(r"^ '([^']+)': \('", io.open(__file__, encoding='utf-8').read(), re.M)
_dups = sorted({r for r in _rows if _rows.count(r) > 1})
assert not _dups, 'duplicate register labels (a dict literal would hide one): %s' % _dups
assert len(_rows) == len(STATUS), (
    'register rows %d but STATUS has %d entries' % (len(_rows), len(STATUS)))

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
 'named; \\emph{none} means that no compiler-verified counterpart is recorded yet, even if '
 'source under validation is identified.  A citation, a numerical '
 'check, or a plausible derivation does not count.  The register is generated from the '
 'source; its mappings must be updated when results are added or validated.  Current totals: '
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
