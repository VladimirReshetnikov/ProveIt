# Fabius paper coverage

This file maps the named mathematical results in the two source papers to
their proved Lean declarations.  It also audits the numbered equations and
substantive prose claims in the two local TeX drafts.  All cited Lean names
are available from the public import `FabiusFunction`.

For a human-readable synthesis rather than a declaration-by-declaration map,
see its
[LaTeX source](Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
or [rendered PDF](Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.pdf).

## arXiv:1702.05442

The exact version used by this audit is vendored as
[TeX source](papers/arXiv-1702.05442v1/09-Function.tex) and as the
[published PDF](papers/arXiv-1702.05442v1/1702.05442v1.pdf).

| Source result | Lean declaration(s) |
| --- | --- |
| Theorem 1 | `Fabius.IsOriginalFabius`, `Fabius.IsOriginalFabius.mk_of_derivative_law`, `Fabius.IsFabius.isOriginalFabius_rvachevUp`, `Fabius.isOriginalFabius_iff_eq_canonical`, `Fabius.rvachevUp_eq_iff_eqOn_Iic_one`, `Fabius.isFabius_iff_isOriginalFabius_rvachevUp_and_rightTail`, `Fabius.isOriginalFabius_iff_existsUnique_isFabius`, `Fabius.existsUnique_originalFabius`, `Fabius.originalFabius_eq_canonical` |
| Lemma 1 | `Fabius.finiteConvolutionProbability_tendsto`, `Fabius.finiteConvolutionProbability_tendsto_fabius`, `Fabius.integral_finiteConvolutionMeasure_tendsto`, `Fabius.integral_finiteConvolutionMeasure_complex_tendsto` |
| Theorem 2 | `Fabius.stepApproximant_tendsto_rvachevUp`, `Fabius.stepApproximant_tendsto_fabius` |
| Theorem 3 | `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSum_probability`, `Fabius.ProbabilityRepresentation.ofReal_rvachevUp_eq_weightedSum_probability` |
| Probability proposition after Theorem 3 | `Fabius.ProbabilityRepresentation.independent_uniform_coordinates`, `Fabius.ProbabilityRepresentation.coordinate_has_uniform_law` |
| Theorem 4(a–c) | `Fabius.original_theorem_four_a`, `Fabius.original_theorem_four_b`, `Fabius.original_theorem_four_c` |
| Unnumbered corollary | `Fabius.rvachev_not_analyticAt` |
| Theorem 5, its Schwartz-decay strengthening, and its upper-bound-free support specializations | `Fabius.rvachev_poisson_summation`, `Fabius.rvachevFourier_real_iteratedDeriv_rapidDecay`, `Fabius.rvachevFourier_real_rapidDecay`, `Fabius.rvachev_poisson_support_specialization_unscaled_of_one_half_le`, `Fabius.rvachev_poisson_support_specialization_of_one_half_le` |
| Theorem 6 | `Fabius.original_theorem_six` |
| Theorem 7 | `Fabius.original_theorem_seven_global` |

The Theorem 3 row intentionally records the paper's source-facing statement,
whose input lies in `[-1,0]`.  The library also proves strictly stronger
all-real forms:

- `Fabius.ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal` and
  `Fabius.ProbabilityRepresentation.fabiusReal_eq_weightedSum_probability`,
  together with
  `Fabius.ProbabilityRepresentation.ofReal_fabiusReal_eq_weightedSum_probability`,
  identify the bounded Fabius function with the random-series CDF for every
  real threshold in both measure codomains;
- `Fabius.ProbabilityRepresentation.weightedSumCDF_eq_intervalIntegral_of_le_half`
  proves the collapsed smoothing equation
  `H(x) = ∫ t in 0..2*x, H(t)` for every `x ≤ 1/2`, including negative
  thresholds where the oriented integral and CDF both vanish;
- `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSumCDF`,
  `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSum_probability_global`,
  and
  `Fabius.ProbabilityRepresentation.ofReal_rvachevUp_eq_weightedSum_probability_global`
  give the real-valued and `ℝ≥0∞` identities
  `up(x) = P[X ≤ 1 - |x|]` for every real `x`.

In these names, “global” means that the real input is unrestricted.  These are
identities for the bounded CDF and `rvachevUp`, not for the signed extension
`extendedFabius` or its canonical specialization `globalFabius`.

The construction and proof infrastructure also formalizes the key supporting
Fourier, recurrence, convolution, polynomial, Taylor, Poisson, moment, and
generating-function identities in proof-oriented forms.  In particular:

- `Fabius.polynomialMeasure_eq_finiteConvolutionMeasure` is the exact bridge
  between equations (12) and (14);
- `Fabius.intervalIntegral_stepApproximant_tendsto` is the weak-limit bridge
  used in Theorem 2;
- `Fabius.rvachev_partition_one_over_nat`,
  `Fabius.rvachev_partition_unity`, `Fabius.rvachev_cosine_series`, and the
  source-compatible `rvachev_poisson_support_specialization` theorems cover
  equations (26)–(32), while their `_of_one_half_le` companions show that
  the upper bound on the lattice spacing is unnecessary;
- `Fabius.rvachevDyadic_cast_global` gives the executable equality underlying
  the global form of Theorem 7.

The second Euler/Weierstrass product displayed in equation (9) is a proof-body
identity rather than a theorem or lemma environment.  It is not part of the
named-result coverage claim.

## arXiv:1702.06487v3

Version 3 is vendored as
[TeX source](papers/arXiv-1702.06487v3/157-Arithmetic-v3.tex) and as the
[published PDF](papers/arXiv-1702.06487v3/1702.06487v3.pdf).

| Source result | Lean declaration |
| --- | --- |
| Proposition 1 | `Fabius.proposition_one` |
| Proposition 2 | `Fabius.proposition_two` and `Fabius.proposition_two_real` |
| Proposition 3 | `Fabius.proposition_three` |
| Proposition 4 | `Fabius.proposition_four` |
| Question 5 | `Fabius.reshetnikovQuestion` |
| Proposition 6 | `Fabius.proposition_six` |
| Theorem 7 | `Fabius.theorem_seven` |
| Proposition 8 | `Fabius.proposition_eight` |
| Theorem 9 | `Fabius.theorem_nine` and `Fabius.theorem_nine_all` |
| Lemma 1 | `Fabius.lemma_one` |
| Proposition 10 | `Fabius.proposition_ten` |
| Definition 12 | `Fabius.dyadicDenominator` |
| Theorem 13 | `Fabius.theorem_thirteen` and `Fabius.theorem_thirteen_denominator_bound` |
| Proposition 15 and the resulting least-common-denominator valuation bound (using Theorem 21) | `Fabius.proposition_fifteen` and `Fabius.dyadicDenominator_padicVal_two_lower_bound` |
| Conjecture 16 and its following denominator formulas | The conjecture remains recorded as `Fabius.conjecture_sixteen`.  The displayed odd-index denominator formula is the unconditional identity `Fabius.dyadicDenominator_odd_eq_conjecturalH` (valid even at `n = 0` under natural-number subtraction); `Fabius.conjecture_sixteen_denominator_formulas` packages it with the even-index formula that still assumes the conjecture for `n ≥ 1`. |
| Theorem 17 | `Fabius.theorem_seventeen` |
| Proposition 18 | `Fabius.proposition_eighteen` |
| Proposition 19 | `Fabius.proposition_nineteen` |
| Theorem 20 | `Fabius.theorem_twenty` |
| Theorem 21 and its reduced-denominator form | `Fabius.theorem_twenty_one` and `Fabius.fabiusAtInverseTwoPow_den_padicVal_two` |
| Proposition 22 | `Fabius.proposition_twenty_two_initial`, `Fabius.proposition_twenty_two` |

`FabiusFunction.Paper06487Supplement` additionally exposes the non-environment
claims used in the paper's prose and proofs: positivity, flat derivatives,
the doubled half-moment recurrence, multiplier divisibility and valuations,
the shifted dyadic-grid formula, the reordered sum, and the conditional
post-Conjecture-16 denominator formulas.

## Additional requested identities

| Claim | Status | Lean declaration(s) |
| --- | --- | --- |
| Fourier--Legendre expansion of Rvachev's up function, with the displayed finite formula for the coefficient of `P_(2n)` | Proved exactly on the natural domain `x ∈ [-1,1]`.  All odd coefficients vanish, and the even series converges absolutely and uniformly on the closed interval, hence pointwise at both endpoints. | `Fabius.rvachevFullLegendreCoefficient_odd_eq_zero`, `Fabius.canonical_rvachevLegendreCoefficient_eq_fabius_sum`, `Fabius.hasSum_canonical_rvachevLegendreSeries_formula`, `Fabius.tsum_canonical_rvachevLegendreSeries_formula`, `Fabius.hasSum_canonical_rvachevLegendreSeries_formula_uniform`, `Fabius.tsum_canonical_rvachevLegendreSeries_formula_uniform` |
| Least-squares optimality of every finite `up` Legendre partial sum | Proved with the exact Pythagorean error identity and uniqueness.  The sum through `P_(2N)` has degree at most `2N` and is the unique minimizer even among all real polynomials of degree at most `2N+1`; therefore it is in particular the best approximation of its corresponding visible degree. | `Fabius.rvachevLegendrePartialSumPolynomial_natDegree_le`, `Fabius.integral_rvachevUp_sub_partialSum_mul_polynomial_eq_zero`, `Fabius.rvachevLegendrePartialSum_pythagorean`, `Fabius.rvachevLegendrePartialSum_least_squares`, `Fabius.rvachevLegendrePartialSum_strict_least_squares`, `Fabius.rvachevLegendrePartialSum_error_eq_iff`, `Fabius.canonical_rvachevLegendrePartialSum_mem_and_isMinOn` |
| Translated monomial representation of `FabiusF[x]` on `0 ≤ x ≤ 2` | Proved for the signed global Fabius function.  The exact nested finite sums retain the source order, all four binomial factors, and the literal integer exponent `k-j+2k^2-2n`; the inner dyadic values use the same global function.  The endpoint `x=0` follows the convention `0^0=1`. | `Fabius.legendrePolynomial_comp_one_sub_two_X`, `Fabius.eval_legendrePolynomial_even_sub_one`, `Fabius.hasSum_extendedFabius_translatedLegendreSeries`, `Fabius.hasSum_globalFabius_translatedLegendre_formula`, `Fabius.tsum_globalFabius_translatedLegendre_formula`, `Fabius.globalFabius_eq_tsum_translatedLegendre_formula` |
| Computability of the canonical bounded Fabius function | Proved in the Grzegorczyk sense.  The sequential clause uses uniform fast dyadic names and a certified primitive-recursive centered-spline evaluator with nearest rounding.  Effective uniform continuity uses the primitive-recursive positive modulus `d(n)=2n` for positive precision indices.  The analytic spline approximation is certified uniformly on all of `ℝ`, with signed-global error at most `2^-p`; its bounded/CDF specialization is uniform on `[0,1]`. | `Fabius.ComputableRealSequence`, `Fabius.SequentiallyComputable`, `Fabius.EffectivelyUniformContinuous`, `Fabius.abs_fabiusUniformSpline_sub_extendedFabius_le`, `Fabius.fabiusUniformSpline_tendstoUniformly_extendedFabius`, `Fabius.fabiusUniformSpline_tendstoUniformly_globalFabius`, `Fabius.fabiusUniformSpline_tendstoUniformlyOn_fabiusReal`, `Fabius.tmBitPR_primrec`, `Fabius.fabiusSplineApproxPR_computable`, `Fabius.fabiusSplineApproxPR_error`, `Fabius.fabius_sequentiallyComputable`, `Fabius.fabius_isComputableRealFunction` |
| Exact centered finite-spline geometry | Proved in every degree, including the degree-zero step spline.  On `[0,1]` the centered spline is exactly the midpoint-corrected finite CDF, takes values in `[0,1]`, and is nondecreasing.  It is already equal to one throughout its last half-cell `1 - 1 / 2^(p+1) ≤ x ≤ 1`, and in particular at `x=1`. | `Fabius.ProbabilityRepresentation.fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc`, `Fabius.ProbabilityRepresentation.fabiusUniformSpline_eq_centeredPartialCDF_all`, `Fabius.ProbabilityRepresentation.fabiusUniformSpline_mem_Icc_all`, `Fabius.ProbabilityRepresentation.monotoneOn_fabiusUniformSpline_all`, `Fabius.monotoneOn_fabiusUniformSpline_all`, `Fabius.ProbabilityRepresentation.uniformCenteredPartialCDF_eq_one_of_le`, `Fabius.fabiusUniformSpline_eq_one_of_le`, `Fabius.fabiusUniformSpline_one_eq_one` |
| Rvachev Fourier transform as the sinc product, with total dyadic shells and a strict global peak | The public facade identifies the actual transform of every bounded Fabius solution with the standalone sinc product.  It transfers the canonical product, two-sided decay gauge, extremal ray, lobe signs and maxima, and exact positive-integer zero orders.  The cross-multiplied real shell identity is valid at every seed, including `y = 0` and the empty shell `k = 0`; on the real axis the modulus is one exactly at the origin and is strictly smaller elsewhere. | `Fabius.rvachevFourier_eq_rvachevFourierProduct`, `Fabius.rvachevFourier_eq_canonical`, `Fabius.rvachevFourier_two_pow_mul`, `Fabius.norm_rvachevFourier_two_pow_mul_cross`, `Fabius.norm_rvachevFourier_le_decayGauge_abs`, `Fabius.norm_rvachevFourier_peak_ray_envelope`, `Fabius.norm_rvachevFourier_lt_one_of_ne_zero`, `Fabius.norm_rvachevFourier_eq_one_iff`, `Fabius.existsUnique_isMaxOn_rvachevFourier_lobe`, `Fabius.rvachevFourier_eq_thueMorse_sign_mul_norm`, `Fabius.tendsto_norm_rvachevFourier_div_pow_zero_order` |
| Exact Birkhoff and normalized dyadic sine-product variance | Proved at every natural length.  The zero-length case is the empty Birkhoff sum and the empty sine product `1`, so both the integral and closed form vanish exactly.  The pointwise logarithmic bridge is global off the finite zero set, without a fundamental-domain hypothesis. | `Fabius.variance_closed_form_all`, `Fabius.integral_sq_birkhoff_sum_all`, `Fabius.log_abs_prod_two_sin_global`, `Fabius.integral_sq_log_prod_two_sin_all` |
| Generic exponential-partition coefficient algebra (reusable infrastructure beyond the two source papers) | Proved over every commutative `ℚ`-algebra. Weighted multiplicity vectors give a finite reciprocal-factorial partition sum satisfying both marked-part and normalized successor recurrences, without cancellation in the target. Over a characteristic-zero field this agrees with the usual quotient notation, and extensionally it is the recursive `SaddleExpansion.expCoeff` family. | `Fabius.weightedPartitions`, `Fabius.mem_weightedPartitions`, `Fabius.mem_weightedPartitions_of`, `Fabius.weightedPartitions_zero`, `Fabius.partitionExpSum`, `Fabius.partitionExpSum_zero`, `Fabius.partitionExpSum_recurrence`, `Fabius.partitionExpSum_succ`, `Fabius.partitionExpSum_eq_sum_div`, `Fabius.partitionExpSum_eq_expCoeff` |
| Generic complete-Bell and moment--cumulant algebra (reusable infrastructure beyond the two source papers) | Proved over every commutative `ℚ`-algebra. Factorial normalization conjugates the ordinary `expCoeff` and `logCoeff` recurrences into named complete-Bell and moment--cumulant transforms, with the classical Bell recurrence, normalized all-index inverse laws, and functoriality under algebra morphisms. This is formal coefficient algebra; no probabilistic interpretation or hierarchy-specific cumulant formula is claimed. | `Fabius.factorialNormalize`, `Fabius.factorialDenormalize`, `Fabius.completeBellPolynomial`, `Fabius.momentCumulant`, `Fabius.completeBellPolynomial_succ`, `Fabius.completeBellPolynomial_momentCumulant`, `Fabius.momentCumulant_completeBellPolynomial`, `Fabius.map_completeBellPolynomial`, `Fabius.map_momentCumulant` |

## Local draft: *Fabius Asymptotic*

The source draft audited for this section is not currently vendored in the
repository.  It contains **zero** formal theorem, lemma, proposition, or
corollary environments, so the table is a claim matrix rather than a
named-environment inventory.  Its public Lean aggregate is
`FabiusFunction.PaperFabiusAsymptotic`.

| Source claim | Status | Lean declaration(s) |
| --- | --- | --- |
| Definitions of `t`, `phi(t)`, and `g(t)` | Proved definitions | `Fabius.fabiusLogArgument`, `Fabius.fabiusLogPhi`, `Fabius.fabiusLogProfile` |
| Chain rule and equation (1) | Proved with the necessary large-scale hypothesis `1 ≤ t` | `Fabius.fabiusLogPhi_hasDerivAt`, `Fabius.fabiusLogProfile_hasDerivAt`, `Fabius.fabiusLogProfile_difference_eq_log_deriv` |
| Positivity used before equation (1) | Proved | `Fabius.fabiusLogPhi_pos`, `Fabius.fabiusLogSlope_pos` |
| Equation (2), both logarithm expansions | Proved | `Fabius.log_sub_one_sub_log_second_order_isBigO`, `Fabius.log_div_sub_one_second_order_isBigO` |
| Equations (3)–(8), proposed explicit main term | Formalized as a candidate and checked against the exact equation; not assumed to be the true sharp expansion | `Fabius.logMainTerm`, `Fabius.logMainDerivative`, `Fabius.logMainTerm_hasDerivAt`, `Fabius.logMainDefect_eq`, `Fabius.logMainDefect_decomposition` |
| Quadratic leading coefficient | Proved first on dyadic scales and then for all real scales | `Fabius.normalized_log_fabius_inverse_two_pow_tendsto`, `Fabius.fabiusLogProfile_normalized_tendsto` |
| Equation (9), exact remainder-difference identity | Proved with the actual remainder `g - G` and the repaired domain `1 < t` | `Fabius.fabiusLogRemainder_difference_eq` |
| Equation (9), size of the explicit main-term defect | Corrected result proved: the residual is `O((log t / t)^2)` | `Fabius.logMainDefect_isBigO_logScaleSquaredRate` |
| Equation (10)'s replacement of that residual by `O(t^-2)` | **False**; formally refuted, with its nonzero leading coefficient identified | `Fabius.logMainDefect_sub_lead_isLittleO`, `Fabius.logMainDefect_not_isBigO_one_div_sq` |
| Equation (11), bounded one-periodic-in-`t` remainder with `E(t) = O(log t / t)` | **Unsupported and not asserted in Lean.** The printed proof uses the false preceding residual estimate. | No declaration claims this particular phase/refinement. |
| Final sharp formula as derived from equations (8) and (11) | The draft's derivation and phase are invalid.  A separate rigorous saddle analysis proves the corrected Lambert-phase formula below. | `Fabius.log_fabius_sub_correctedWikipediaMain_isBigO`, `Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO` |
| Rigorous coarse small-argument replacement | Proved: explicit dyadic error, eventual full-real bound, and `O(t log t)` error | `Fabius.abs_dyadicLogError_le`, `Fabius.eventually_abs_fabiusLogProfile_sub_quadratic_le`, `Fabius.fabiusLogProfile_sub_quadratic_isBigO`, `Fabius.log_fabiusLogPhi_add_quadratic_isBigO` |
| Rigorous sharp periodic correction | Proved: continuous periodic correction, exact mean, every nonzero-frequency Gamma--zeta Fourier coefficient is nonzero, absolute Fourier reconstruction, and `O(1 / (-log x))` corrected error | `Fabius.negativeLaplacePeriodicMean_eq`, `Fabius.hasSum_negativeLaplacePsi_gammaZeta_fourierSeries`, `Fabius.negativeLaplacePsiFourierCoeff_ne_zero`, `Fabius.negativeLaplacePsi_not_constant`, `Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO` |
| Full sharp expansion to every order | Proved at the exact lower-Lambert phase: after the first `N` periodic saddle coefficients, the remainder is `O(lambda^-N)`; `N = 2` exposes the first explicit correction after the identically zero zeroth coefficient | `Fabius.log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`, `Fabius.log_fabius_sub_sharpLambertExpansion_isBigO`, `Fabius.fabiusSharpLambertExpansion_two` |
| Forward negative-Laplace tail at the exact lower-Lambert scale | Proved smaller than every inverse power of the phase along `x = 2^-t`: for each natural `N`, the tail is `o(lambda(2^-t)^-N)` as `t → +∞`.  The case `N = 0` states convergence to zero; this little-o result applies to the isolated forward tail, not to the complete saddle-expansion remainder. | `Fabius.negativeLaplaceTailError_dyadicLambert_isLittleO_inv_pow`, `Fabius.negativeLaplaceTailError_dyadicLambert_isBigO_inv_pow` |
| Lower-Lambert phase to every order | Proved separately in literal `-log x` and `log (-log x)` variables | `Fabius.fabiusLambertLiteralApproximation`, `Fabius.fabiusLambertPhase_sub_literalApproximation_isBigO` |
| Literal elementary formula with the periodic term omitted | **False at the claimed error scale.** | `Fabius.log_fabius_sub_WikipediaElementaryMain_not_isBigO` |

The source's intermediate coefficient matching is not a proof about an
arbitrary remainder: its equation (4) drops `R(t)-R(t-1)`, and equation (6)
uses a bound on `R'` that was never assumed.  The Lean development therefore
checks the displayed explicit term through its exact residual instead of
formalizing those circular steps as theorems.

## Linked Stack Exchange discussions

| Web claim | Status | Lean declaration(s) |
| --- | --- | --- |
| [Recurrence sequence](https://math.stackexchange.com/questions/4354350/extracting-an-asymptotic-from-a-sequence-defined-by-a-recurrence-relation) and its connection to `F(2^-n)` | Proved with the source normalization `a_n = d_n / n!`; the resulting direct recurrence for `F(2^-n)` is proved exactly for `n ≥ 1` in rational, generic bounded, canonical bounded, generic signed-global, and canonical signed-global forms | `Fabius.fabiusRecurrenceSequence`, `Fabius.fabiusRecurrenceSequence_recurrence`, `Fabius.fabius_inverse_two_pow_eq_recurrenceSequence`, `Fabius.fabiusAtInverseTwoPow_recurrence_zpow`, `Fabius.fabiusFunction_inverse_two_pow_recurrence_zpow`, `Fabius.fabius_inverse_two_pow_recurrence_zpow`, `Fabius.extendedFabius_inverse_two_pow_recurrence`, `Fabius.globalFabius_inverse_two_pow_recurrence` |
| Nonrecursive solution of the inverse-dyadic recurrence | Proved for every natural `n`, including `n = 0`, as a finite weighted-path sum and as the explicit sum over ordered compositions `n = r₁+⋯+rₘ` with partial sums `sⱼ`; a nested version first sums over the number of blocks.  The empty composition gives `F(1)=1`.  Generic bounded, canonical, and signed-global real corollaries are exposed.  The former standalone article is consolidated into Part “Fabius Integration Research Frontiers,” especially sections `integration:sec:path-sums` and `integration:sec:fabius-composition-formula`, in the maintained [source](non-formalized-research-frontiers/non-formalized-research-frontiers.tex) and [PDF](non-formalized-research-frontiers/non-formalized-research-frontiers.pdf). | `Fabius.Composition.pathSum_eq_sum_range`, `Fabius.triangularRecurrence_eq_initial_mul_pathSum`, `Fabius.fabiusCompositionWeight`, `Fabius.fabiusCompositionSum`, `Fabius.fabiusRecurrenceSequence_eq_sum_compositions`, `Fabius.fabiusAtInverseTwoPow_eq_composition_formula`, `Fabius.fabiusAtInverseTwoPow_eq_composition_formula_by_length`, `Fabius.fabiusFunction_inverse_two_pow_eq_sum_compositions`, `Fabius.globalFabius_inverse_two_pow_eq_sum_compositions` |
| Bernoulli recurrence and generating-function equation/product | Proved in source-facing coefficient and analytic forms | `Fabius.fabiusRecurrenceSequence_bernoulli_recurrence`, `Fabius.complexGeneratingFunction_eq_fabiusRecurrenceSequence_series`, `Fabius.fabiusRecurrenceSequence_series_neg_eq_tprod` |
| [Finite q-binomial/half-shifted Thue--Morse formula for `F(m/2^n)`](https://math.stackexchange.com/questions/3283519/conjectured-formula-for-the-fabius-function) | Proved exactly for all natural `m,n`, including zero and unreduced representations.  With no bound on `m`, it computes the signed global extension; under `m ≤ 2^n`, it computes every bounded `IsFabius` function.  `qPochhammer` and `qBinomial` follow the source argument order. | `Fabius.qBinomialThueMorseDyadicHalfShiftFormula`, `Fabius.fabiusDyadic_eq_qBinomialThueMorseDyadic_halfShift_sum`, `Fabius.extendedFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula`, `Fabius.globalFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula`, `Fabius.fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula` |
| Arbitrary-scalar translation and dyadic-representation invariance of the finite formula | The complete normalized finite expression is packaged as a polynomial over `ℚ` and proved equal to the constant centered formula, then evaluated in every field over `ℚ`.  Consequently the fully displayed sum with inner power `(j - m * 2^k + q)^(n+k)` computes the same value for every real or complex `q`, with an explicit Gaussian-rational endpoint.  Equal nonnegative dyadic rationals give equal formula values even when both scalar translations are changed simultaneously; binary refinement is the corresponding special case. | `Fabius.qBinomialThueMorseDyadicTranslatedFormulaPolynomial_eq_const`, `Fabius.qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered`, `Fabius.qBinomialThueMorseDyadicTranslatedFormulaIn_eq_of_rat_eq`, `Fabius.qBinomialThueMorseDyadicTranslatedFormulaIn_refine`, `Fabius.fabiusDyadic_algebraMap_eq_qBinomialThueMorseDyadic_translated_sum`, `Fabius.globalFabius_dyadic_eq_qBinomialThueMorseDyadic_translated_sum_real`, `Fabius.globalFabius_dyadic_eq_qBinomialThueMorseDyadic_translated_sum_complex`, `Fabius.globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_gaussianRat`, `Fabius.qBinomialThueMorseDyadicTranslatedFormula_eq_of_rat_eq`, `Fabius.qBinomialThueMorseDyadicTranslatedFormula_refine`, `Fabius.qBinomialThueMorseDyadicFormula_eq_of_rat_eq`, `Fabius.qBinomialThueMorseDyadicHalfShiftFormula_refine`, `Fabius.qBinomialThueMorseDyadicHalfShiftFormula_eq_of_rat_eq` |
| Gaussian/dyadic Prouhet coefficient extractor | The signed half-q-binomial weights at the nodes `-2^k` annihilate every rational polynomial of degree below `n` and, in degree at most `n`, extract its top coefficient times the exact q-Pochhammer/Mersenne factor.  The `Polynomial.degree` formulation includes `n = 0, p = 0`. | `Fabius.halfQBinomialDyadicWeight`, `Fabius.negativeDyadicNode`, `Fabius.halfQBinomialDyadicWeight_nodes_zero`, `Fabius.halfQBinomialDyadicWeight_nodes_self`, `Fabius.halfQBinomial_negativeDyadic_polynomial_sum_eq_coeff`, `Fabius.halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne`, `Fabius.halfQBinomial_negativeDyadic_polynomial_sum_eq_zero_of_degree_lt` |
| Inverse-power specialization `F(2^-n)` | Recovered for every natural `n`, including `n = 0`; both the centered and `+1/2` literal sums are exposed.  The arbitrary-numerator formula is proved to specialize exactly to the centered inverse-power formula at numerator one. | `Fabius.qBinomialThueMorseDyadicFormula_one`, `Fabius.fabiusAtInverseTwoPow_eq_qBinomialThueMorse_sum`, `Fabius.fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula`, `Fabius.fabiusAtInverseTwoPow_eq_qBinomialThueMorse_halfShift_sum`, `Fabius.fabius_inverse_two_pow_eq_qBinomialThueMorseHalfShiftFormula` |
| Centered and raw-coordinate inverse-power formulas with arbitrary shifts | Proved over every field over `ℚ`, hence for every real or complex `q`; explicit Gaussian-rational and fully literal real/complex endpoints are exposed.  The centered inner power is `(r - 2^k + q)^(n+k)`, while dyadic reflection gives the raw power `(r+q)^(n+k)` with denominator `(-2)^(n^2)`.  The zero-one `thueMorseBit` is used literally, and `n = q = 0` follows Lean's `0^0 = 1` convention. | `Fabius.qBinomialThueMorseTranslatedFormulaIn_eq_centered`, `Fabius.fabiusAtInverseTwoPow_cast_eq_qBinomialThueMorse_translated_sum`, `Fabius.fabius_inverse_two_pow_eq_qBinomialThueMorse_translated_sum_complex`, `Fabius.qBinomialThueMorseRawTranslatedNumeratorPolynomial_eq_const`, `Fabius.qBinomialThueMorseRawTranslatedFormulaIn_eq_fabiusAtInverseTwoPow`, `Fabius.fabiusAtInverseTwoPow_cast_eq_qBinomialThueMorse_rawTranslated_sum`, `Fabius.fabius_inverse_two_pow_eq_qBinomialThueMorse_rawTranslated_sum_real`, `Fabius.fabius_inverse_two_pow_eq_qBinomialThueMorse_rawTranslated_sum_complex`, `Fabius.fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_gaussianRat` |
| Infinite binary-reduction q-binomial/Thue--Morse series | Corrected and proved with outer index `m = 0`: for every real `x` and every real or complex `q`, the literal nested summands are absolutely summable and their series sums to the signed global Fabius extension; on `[0,1]` it equals the bounded Fabius function.  For `N ≥ 1`, the finite analytic telescope through scale `N` has uniform error at most `2 * 2^-N`; with the natural-floor zero extension on `x ≤ 0`, its partial sums converge uniformly on all of `ℝ`.  The finite q-binomial expression is a constant polynomial in `q`.  At `x = 1`, the binary prefix at scale `m` is `2^m`, the scale-zero summand is one, and every positive-scale coefficient and summand vanishes. | `Fabius.qBinomialThueMorseTranslatedNumeratorPolynomial_eq_const`, `Fabius.qBinomialFabiusReductionPolynomial_rclike_eq_fabiusReductionSum`, `Fabius.binaryPreviousPrefix_eq_floor_zpow`, `Fabius.binaryPrefix_one`, `Fabius.globalBinaryReductionSummand_one_zero`, `Fabius.globalBinaryReductionCoefficient_one_eq_zero_of_one_le`, `Fabius.globalBinaryReductionSummand_one_eq_zero_of_one_le`, `Fabius.norm_globalBinaryReductionSum_sub_extendedFabius_le`, `Fabius.globalBinaryReductionSum_tendstoUniformly_extendedFabius`, `Fabius.hasSum_globalBinaryReductionSummand_all`, `Fabius.qBinomialFabiusGlobalSummand`, `Fabius.qBinomialFabiusGlobalSummand_eq`, `Fabius.qBinomialFabiusGlobalSummand_independent`, `Fabius.summable_norm_qBinomialFabiusGlobalSummand_all`, `Fabius.summable_qBinomialFabiusGlobalSummand_all`, `Fabius.hasSum_qBinomialFabiusGlobalSummand_all`, `Fabius.extendedFabius_eq_tsum_qBinomialFabiusGlobalSummand_all`, `Fabius.globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_all`, `Fabius.fabiusReal_eq_tsum_qBinomialFabiusGlobalSummand` |
| Parity-power Fabius series | Corrected and proved with outer index `m = 0` for every real `x`; its summands are absolutely summable and the sum is the signed global Fabius extension.  On `x ≤ 0` every summand vanishes.  The source exponent is interpreted in `ℤ`, so its `n = 0` value is `-1`.  At `x = 1`, the zeroth summand is one and every positive-scale summand vanishes.  On `[0,1]` the sum equals the bounded Fabius function; the original `m = 1` indexing is proved on the half-open domain `0 ≤ x < 1`. | `Fabius.fabiusParityPowerExponent_eq_choose_sub_one`, `Fabius.fabiusParityPowerInner_eq_half_reductionSum`, `Fabius.fabiusParityPowerSummand_eq_globalBinaryReductionSummand`, `Fabius.fabiusParityPowerSummand_eq_zero_of_nonpos`, `Fabius.fabiusParityPowerSummand_one_zero`, `Fabius.fabiusParityPowerSummand_one_eq_zero_of_one_le`, `Fabius.summable_norm_fabiusParityPowerSummand_all`, `Fabius.hasSum_fabiusParityPowerSummand_all`, `Fabius.globalFabius_eq_tsum_fabiusParityPower_literal_all`, `Fabius.fabiusReal_eq_tsum_fabiusParityPowerSummand`, `Fabius.globalFabius_eq_tsum_fabiusParityPowerSummand_succ` |
| Generalized Wolfram `DiscreteLimit` q-binomial/Thue--Morse formula | Proved for every real `x` and every `q : ℂ`, including Gaussian-rational shifts and arbitrary real shifts (hence irrational ones).  The limit is the signed global Fabius extension; on `x ≤ 0` every finite approximant and the target vanish exactly, while on `[0,1]` the target is the bounded Fabius function.  For `x ≥ 0`, the safe natural range length `⌊2^(n+k)x+1/2⌋₊` equals one plus the inclusive upper cutoff `Floor[2^(n+k)x-1/2]`, including the empty case.  Finite rows may depend on `q`; their limit does not.  Exact reindexing makes each row a Toeplitz average of convergent complex-shift finite splines.  The exact finite q-binomial telescope retains its natural `0 ≤ x` hypothesis, but convergence of the binary telescope and both infinite-`tsum` identifications hold for all real `x`; none of these statements asserts termwise equality with a finite `DiscreteLimit` row.  The former nonnegative-domain convergence declarations remain as compatibility forms. | `Fabius.fabiusDiscreteLimitRangeLength_eq_floor_add_one`, `Fabius.fabiusDiscreteLimitApproximationComplex_eq_weighted_shiftSpline`, `Fabius.fabiusDiscreteLimitApproximation_eq_zero_of_nonpos`, `Fabius.extendedFabius_eq_zero_of_nonpos`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all`, `Fabius.fabiusDiscreteLimitApproximationGaussianRat_tendsto_globalFabius_all`, `Fabius.fabiusDiscreteLimitApproximationReal_tendsto_globalFabius_all`, `Fabius.fabiusDiscreteLimitApproximationRat_tendsto_globalFabius_all`, `Fabius.fabiusDiscreteLimit_literal_complex_tendsto_globalFabius_all`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius`, `Fabius.fabiusDiscreteLimitApproximationGaussianRat_tendsto_globalFabius`, `Fabius.fabiusDiscreteLimitApproximationReal_tendsto_globalFabius`, `Fabius.fabiusDiscreteLimitApproximationRat_tendsto_globalFabius`, `Fabius.fabiusDiscreteLimit_literal_complex_tendsto_globalFabius`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_fabiusReal`, `Fabius.extendedFabius_eq_qBinomial_telescope_add_remainder`, `Fabius.globalFabius_eq_qBinomialThueMorse_telescope_add_remainder_complex`, `Fabius.hasSum_globalBinaryReductionSummand_all`, `Fabius.extendedFabius_eq_tsum_globalBinaryReductionSummand_all`, `Fabius.binary_telescope_tendsto_globalFabius_all`, `Fabius.binary_telescope_tendsto_globalFabius`, `Fabius.hasSum_qBinomialFabiusGlobalSummand_all`, `Fabius.extendedFabius_eq_tsum_qBinomialFabiusGlobalSummand_all`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum_all`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum_all`, `Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum` |
| Normalized Toeplitz q-row polynomial | The complete rational generating polynomial is the normalized finite q-Pochhammer product.  Its rational roots are exactly `2, 4, ..., 2^n`, including the empty root set at `n = 0`; mass one is the value at `z = 1`.  The row annihilates each of the first `n` dyadic geometric modes after their rational coefficients act on an arbitrary vector, and exact q-Richardson cancellation holds for sequences in every `ℚ`-module.  No multiplication, topology, order, or norm is required on the target; the existing rational theorem is the `M = ℚ` specialization.  No root classification at arbitrary scalar arguments is claimed. | `Fabius.sum_range_discreteLimitWeight_mul_pow`, `Fabius.sum_range_discreteLimitWeight_mul_pow_eq_zero_iff`, `Fabius.sum_range_discreteLimitWeight`, `Fabius.sum_range_discreteLimitWeight_mul_geometricMode_smul_eq_zero`, `Fabius.discreteLimitWeight_qRichardson_exact_module`, `Fabius.discreteLimitWeight_qRichardson_exact` |
| Fixed-constant asymptotic conjecture for the recurrence sequence | Corrected: the sharp dyadic formula has a genuine nonconstant periodic term and `O(1/n)` error | `Fabius.log_fabius_dyadic_sub_lambertMain_isBigO`, `Fabius.negativeLaplacePsi_not_constant` |
| [Explicit logarithmic small-`x` formula](https://math.stackexchange.com/a/3925650/19661) | Transcribed exactly, but corrected by adding the nonconstant periodic term at the exact lower-Lambert phase | `Fabius.fabiusWikipediaElementaryMain`, `Fabius.fabiusExplicitCorrectedWikipediaMain` |
| Corrected general formula with `O(1 / (-log x))`, and the resulting asymptotic equivalent | Proved unconditionally by the quantitative Bromwich saddle argument | `Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO`, `Fabius.fabius_isEquivalent_exp_explicitCorrectedWikipediaMain` |
| Complete corrected asymptotic expansion | Proved for every order `N`: `log F - main - sum_{j<N} lambda^{-j} c_j(lambda) = O(lambda^{-N})`, where `c_j` is continuous, bounded, and one-periodic | `Fabius.fabiusSaddleLogCoefficient`, `Fabius.log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`, `Fabius.log_fabius_sub_sharpLambertExpansion_isBigO` |
| First term beyond the linked formula | Identified explicitly as `fabiusFirstSaddleCorrection(lambda) / lambda`, with an `O(lambda^-2)` remainder after insertion | `Fabius.fabiusSaddleLogPartialSum_two`, `Fabius.fabiusSharpLambertExpansion_two`, `Fabius.log_fabius_sub_sharpLambertExpansion_isBigO` |
| All-orders elementary expansion of the exact phase | Proved independently; the oscillatory saddle coefficients in the full formula remain evaluated at the exact phase | `Fabius.fabiusLambertLiteralApproximation`, `Fabius.fabiusLambertPhase_sub_literalApproximation_isBigO` |
| Uncorrected formula with the same error | **False** because the omitted periodic correction cannot be absorbed into a vanishing remainder | `Fabius.negativeLaplacePsi_comp_fabiusLambertPhase_not_isBigO`, `Fabius.log_fabius_sub_WikipediaElementaryMain_not_isBigO` |
| [Quotient-of-exponentials approximation](https://mathematica.stackexchange.com/questions/285919/approximation-of-the-fabius-function-with-a-quotient-of-exponentials) | Formally refuted as an endpoint asymptotic: it is little-o of the true displaced bump | `Fabius.mathematicaFabiusQuotientCandidate_isLittleO_fabiusLogPhi`, `Fabius.mathematicaFabiusQuotientCandidate_not_isEquivalent_fabiusLogPhi` |

## Local draft: *K-fold summation over the signed Thue--Morse sequence*

The source draft audited for this section is likewise not currently vendored
in the repository.  It contains **zero** formal theorem, lemma, proposition,
or corollary environments.  Its public Lean aggregate is
`FabiusFunction.PaperKFoldThueMorse`.

| Source claim | Status | Lean declaration(s) |
| --- | --- | --- |
| Thue--Morse sign definition and self-similarity | Proved | `Fabius.binaryWeight`, `Fabius.thueMorseSign`, `Fabius.thueMorseSign_two_mul`, `Fabius.thueMorseSign_two_mul_add_one` |
| Degree-valued Boolean-cube and sparse Prouhet annihilation | Proved over every commutative ring using `Polynomial.degree`.  Unlike the legacy `natDegree` interfaces, the public degree-valued theorems include the genuine boundary where the support is empty: the strict bound then admits exactly the zero polynomial.  Consequently the sparse theorem is valid also at submask parameter `n = 0`; the sharp moment remains valid there under the `0^0 = 1` convention.  Both powerset parametrizations and the literal odd-Pascal-row indices are exposed. | `Fabius.sum_powerset_neg_one_pow_eval_of_degree_lt`, `Fabius.sum_powerset_neg_one_pow_pow_card`, `Fabius.sum_thueMorseSign_mul_affine_eval_of_degree_lt`, `Fabius.sum_submask_neg_one_pow_eval_of_degree_lt`, `Fabius.sum_submask_neg_one_pow_pow`, `Fabius.sum_oddBinomialIndices_thueMorseSign_mul_affine_eval_of_degree_lt`, `Fabius.sum_oddBinomialIndices_thueMorseSign_mul_affine_pow_binaryWeight` |
| Additional requested identity (not in the draft): zero-one `ThueMorse[n]` binomial/`Log2` formula | Proved for every natural `n`, with the integer inside `Log2` first identified exactly as `2^(binaryWeight n + 1)` and the final division interpreted in `ℚ` | `Fabius.thueMorseBit`, `Fabius.signedBinomialParitySum`, `Fabius.thueMorseLogIntegerArgument_eq_two_pow`, `Fabius.log2_thueMorseLog2Argument`, `Fabius.thueMorseBit_eq_log2_binomialParity_formula` |
| Inclusive iterated prefix sums and odd first-prefix zeros | Proved | `Fabius.iteratedPrefix`, `Fabius.iteratedPrefix_succ`, `Fabius.iteratedPrefix_succ_sub`, `Fabius.iteratedPrefix_one_two_mul_add_one` |
| Equation (1), literal normalized grid | Defined exactly | `Fabius.paperPrefixGridValue`, `Fabius.prefixGridPoint` |
| Equation (1), instruction to join consecutive grid points | Defined as the intended real polygon (with a rational companion), distinct from the contradictory floor/step wording | `Fabius.paperPrefixPolygonReal`, `Fabius.paperPrefixPolygonReal_grid`, `Fabius.paperPrefixPolygon`, `Fabius.paperPrefixPolygon_grid` |
| Equation (2), discrete functional equation | Proved with the omitted unit-interval index condition made explicit | `Fabius.paperPrefixGridValue_equation`, `Fabius.paperPrefixGridValue_equation_of_pos`, `Fabius.prefixGridPoint_lower_argument_mem` |
| Additional library generalization: arbitrary-shift prefix-grid recurrence | **Proved and compiler-validated.**  Source checkpoint `00ff41a5e` is validated at immutable coordinator merge `ae16882d5`.  For `V_s(k,j) = S^(k+s)_j / 2^(k.choose 2)`, the unscaled and denominator-cleared recurrences hold for every natural shift `s`.  Shift zero is definitionally the literal equation-(1) grid, and shift one is the inclusive-prefix correction.  The exact equation records `j < 2^q` so that its lower-level abscissa lies in `[0,1]`; the positive-level form assumes `0 < k` and `j < 2^(k-1)`.  Endpoint, polygon, and convergence semantics are deliberately not generalized because they depend on the shift. | `Fabius.shiftedPrefixGridValue`, `Fabius.shiftedPrefixGridValue_zero`, `Fabius.shiftedPrefixGridValue_one`, `Fabius.shiftedPrefixGridValue_succ_sub`, `Fabius.shiftedPrefixGridValue_scaledDifference`, `Fabius.shiftedPrefixGridValue_equation`, `Fabius.shiftedPrefixGridValue_equation_of_pos` |
| Equation (3), Fabius characterization | Repaired: the bounded derivative equation holds only on `[0,1/2]` and symmetry is required | `Fabius.IsFabius`, `Fabius.existsUnique_fabius` |
| Claimed convergence of the literal equation-(1) normalization | **False**, even pointwise at `x = 1`; the intended real polygon has the same obstruction | `Fabius.paperPrefixGridValue_endpoint`, `Fabius.paperPrefixGridValue_endpoint_not_tendsto_one`, `Fabius.paperPrefixPolygonReal_endpoint_not_tendsto_one` |
| Corrected prefix approximation | Proved pointwise, with one prefix-order shift and the centered-cell interpretation; no uniform rate is claimed | `Fabius.correctedPrefixCoefficient_eq_stepApproximant`, `Fabius.correctedPrefixGridSample_tendsto_rvachevUp`, `Fabius.correctedPrefixGridSample_tendsto_fabius` |
| Repeated-derivative scaling | Proved for the signed global extension; the bounded global wording is domain-invalid | `Fabius.iteratedDeriv_extendedFabius` |
| Signed dyadic pre-run reciprocity and reflected zero locus; separate terminal zero run, left boundary, and right boundary | Proved for the literal hypotheses `k ≤ r` and `k + d < 2 ^ r`; the zero equivalence pairs any zeros and does not assert a zero-free pre-run window | Base sign reflection: `Fabius.thueMorseSign_dyadic_complement`; signed prefix reflection: `Fabius.iteratedPrefix_dyadic_reverse_window`; reflected zero iff: `Fabius.iteratedPrefix_dyadic_reverse_window_eq_zero_iff`; value at zero used by the `d = 0` specialization: `Fabius.iteratedPrefix_at_zero`; terminal endpoint/run: `Fabius.iteratedPrefix_dyadic_endpoint`, `Fabius.iteratedPrefix_dyadic_zero_reverse`, `Fabius.iteratedPrefix_dyadic_zero_run`; left boundary: `Fabius.iteratedPrefix_before_dyadic_run`; right boundary: `Fabius.iteratedPrefix_at_dyadic` |
| Equation (4), local `4h` error and global uniform error | **False** for the printed normalization | `Fabius.literalGridSlope_two_one`, `Fabius.literal_local_error_bound_false`, `Fabius.paperPrefixGridValue_endpoint_not_tendsto_one` |
| Equation (5), discrete B-spline kernel and binomial convolution | Proved in exact source-facing form, with a shifted recurrence also available | `Fabius.iteratedPrefixKernel`, `Fabius.iteratedPrefix_eq_sum_kernel`, `Fabius.iteratedPrefix_convolution` |
| Equation (6), both generating-series identities | Proved as formal power-series identities, with finite coefficient stabilization for the infinite product | `Fabius.thueMorseBlockPolynomial_eq_product`, `Fabius.coeff_finite_thueMorse_product`, `Fabius.iteratedPrefixSeries_eq`, `Fabius.one_sub_X_pow_mul_iteratedPrefixSeries`, `Fabius.coeff_eq6_finite` |
| Block-polynomial derivatives at one | Proved through the exact derivative/binomial-moment dictionary, including every lower-order zero and the first nonzero derivative | `Fabius.iterate_derivative_thueMorseBlockPolynomial_eval_one`, `Fabius.iterate_derivative_thueMorseBlockPolynomial_eval_one_of_lt`, `Fabius.iterate_derivative_thueMorseBlockPolynomial_eval_one_self` |
| Equation (7), maximum proxy | **False**: for every `x > 0` its terms are unbounded and no maximum exists | `Fabius.paperProxyTerm_succ`, `Fabius.paperProxyRatio_tendsto_atTop`, `Fabius.paperProxyTerm_unbounded`, `Fabius.paperProxyTerm_has_no_maximum` |
| Stirling estimate invoked after equation (7) | Proved exactly as `log(n!) = n log n - n + O(log n)` | `Fabius.log_factorial_sub_main_isBigO_log` |
| Equation (8), continuous stationary equation | Repaired positive-real calculus proved after making the draft's integer-to-real change explicit | `Fabius.paperStirlingPhi_hasDerivAt`, `Fabius.paper_stationary_iff_mul_two_rpow_neg` |
| Equation (9), Lambert `W_{-1}` solution | Proved for `0 < x` with `(log 2)x ≤ exp(-1)`, equivalently for the Lambert argument `z = -(log 2)x` in the full closed-left lower-branch domain `[-exp(-1),0)`.  On that domain, the branch has endpoint value `-1`, stays at or below `-1`, satisfies its defining equation, is the unique solution at or below `-1`, is strictly decreasing, and has image `(-∞,-1]`.  The stationary value solves equation (9) at the branch point as well, satisfies `1 / log 2 ≤ paperLambertN(x)`, attains equality exactly at the branch point, and is strictly larger in the interior.  The former strict-domain declarations remain as compatibility forms. | `Fabius.lowerLambertW_branchPoint`, `Fabius.lowerLambertW_le_neg_one`, `Fabius.lowerLambertW_mul_exp_of_mem_Ico`, `Fabius.lowerLambertW_unique_of_mem_Ico`, `Fabius.lowerLambertW_strictAntiOn_Ico`, `Fabius.lowerLambertW_image_Ico`, `Fabius.paperLambertN_eq9_of_le`, `Fabius.one_div_log_two_le_paperLambertN`, `Fabius.paperLambertN_eq_one_div_log_two`, `Fabius.paperLambertN_eq_one_div_log_two_iff`, `Fabius.one_div_log_two_lt_paperLambertN`, `Fabius.lowerLambertW_lt_neg_one`, `Fabius.lowerLambertW_mul_exp`, `Fabius.lowerLambertW_unique`, `Fabius.lowerLambertW_strictAntiOn`, `Fabius.lowerLambertW_image`, `Fabius.paperLambertN_eq9` |
| Equation (10), claimed `O(log n)` error after stationary substitution | **False for the displayed Stirling proxy**: substitution leaves an omitted linear `+n`, which is not `O(log n)` | `Fabius.paperStirlingPhi_of_stationary`, `Fabius.paperStirlingOmittedTerm_not_isBigO_log` |
| Standard lower-branch expansion used before equation (11) | Proved as a positive-side limit: `W₋₁(-ε) - (log ε - log |log ε|) → 0` | `Fabius.tendsto_lowerLambertW_expansion` |
| Equation (11), coarse log-squared decay | Proved rigorously without the false maximum/Lambert-W chain | `Fabius.log_fabiusLogPhi_add_quadratic_isBigO`, `Fabius.fabiusLogProfile_normalized_tendsto` |
| “Faster than every power” | Proved from smooth flatness | `Fabius.extendedFabius_isLittleO_pow_at_zero`, `Fabius.fabius_isLittleO_pow_at_zero` (two-sided), `Fabius.fabius_isLittleO_pow_at_zero_right` |
| “Slower than `exp(-c/x)`” | Proved precisely on the dyadic logarithmic scale: for every `c > 0`, `exp (-c 2^t)` is little-o of `F(2^-t)` | `Fabius.exp_neg_two_rpow_isLittleO_fabiusLogPhi`, `Fabius.exp_neg_two_rpow_isLittleO_fabius` |

The corrected approximation is a separate theorem, not a reinterpretation
that makes the literal source normalization true.  In particular, the
development does not claim the draft's suggested quantitative uniform rate.

## Corrections to the printed sources

The Lean declarations do not assert formulas known to be false.  The relevant
corrections are documented in their source modules:

- arXiv:1702.05442 equation (12) has a finite upper index;
- the step functions use half-weighted shared endpoints;
- equation (25) includes `t`, equation (26) assumes `n > 0`, and equation
  (32) uses consistent scaling;
- equations (33), (36), and (38) expose their necessary positivity or
  removable-singularity handling;
- arXiv:1702.06487 Lemma 1 assumes `0 ≤ scale + order`;
- `R_n` uses the positive exponent required by equation (27) and the examples;
- the proof-internal naturality assertion in Theorem 20 is stated for
  `2 * d_k * N_n`, since the printed assertion without the factor two is
  false already at small indices.
