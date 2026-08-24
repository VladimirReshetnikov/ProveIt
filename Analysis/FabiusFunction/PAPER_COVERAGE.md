# Fabius paper coverage

This file maps the named mathematical results in the two source papers to
their proved Lean declarations.  It also audits the numbered equations and
substantive prose claims in the two local TeX drafts.  All cited Lean names
are available from the public import `FabiusFunction`.

## arXiv:1702.05442

| Source result | Lean declaration(s) |
| --- | --- |
| Theorem 1 | `Fabius.IsOriginalFabius`, `Fabius.existsUnique_originalFabius`, `Fabius.originalFabius_eq_canonical` |
| Lemma 1 | `Fabius.finiteConvolutionProbability_tendsto`, `Fabius.finiteConvolutionProbability_tendsto_fabius`, `Fabius.integral_finiteConvolutionMeasure_tendsto`, `Fabius.integral_finiteConvolutionMeasure_complex_tendsto` |
| Theorem 2 | `Fabius.stepApproximant_tendsto_rvachevUp`, `Fabius.stepApproximant_tendsto_fabius` |
| Theorem 3 | `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSum_probability`, `Fabius.ProbabilityRepresentation.ofReal_rvachevUp_eq_weightedSum_probability` |
| Probability proposition after Theorem 3 | `Fabius.ProbabilityRepresentation.independent_uniform_coordinates`, `Fabius.ProbabilityRepresentation.coordinate_has_uniform_law` |
| Theorem 4(a–c) | `Fabius.original_theorem_four_a`, `Fabius.original_theorem_four_b`, `Fabius.original_theorem_four_c` |
| Unnumbered corollary | `Fabius.rvachev_not_analyticAt` |
| Theorem 5 | `Fabius.rvachev_poisson_summation` |
| Theorem 6 | `Fabius.original_theorem_six` |
| Theorem 7 | `Fabius.original_theorem_seven_global` |

The construction and proof infrastructure also formalizes the key supporting
Fourier, recurrence, convolution, polynomial, Taylor, Poisson, moment, and
generating-function identities in proof-oriented forms.  In particular:

- `Fabius.polynomialMeasure_eq_finiteConvolutionMeasure` is the exact bridge
  between equations (12) and (14);
- `Fabius.intervalIntegral_stepApproximant_tendsto` is the weak-limit bridge
  used in Theorem 2;
- `Fabius.rvachev_partition_one_over_nat`,
  `Fabius.rvachev_partition_unity`, `Fabius.rvachev_cosine_series`, and the
  two `rvachev_poisson_support_specialization` theorems cover equations
  (26)–(32);
- `Fabius.rvachevDyadic_cast_global` gives the executable equality underlying
  the global form of Theorem 7.

The second Euler/Weierstrass product displayed in equation (9) is a proof-body
identity rather than a theorem or lemma environment.  It is not part of the
named-result coverage claim.

## arXiv:1702.06487v3

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
| Proposition 15 | `Fabius.proposition_fifteen` |
| Conjecture 16 | `Fabius.conjecture_sixteen` |
| Theorem 17 | `Fabius.theorem_seventeen` |
| Proposition 18 | `Fabius.proposition_eighteen` |
| Proposition 19 | `Fabius.proposition_nineteen` |
| Theorem 20 | `Fabius.theorem_twenty` |
| Theorem 21 | `Fabius.theorem_twenty_one` |
| Proposition 22 | `Fabius.proposition_twenty_two_initial`, `Fabius.proposition_twenty_two` |

`FabiusFunction.Paper06487Supplement` additionally exposes the non-environment
claims used in the paper's prose and proofs: positivity, flat derivatives,
the doubled half-moment recurrence, multiplier divisibility and valuations,
the shifted dyadic-grid formula, the reordered sum, and the conditional
post-Conjecture-16 denominator formulas.

## Local draft: *Fabius Asymptotic*

The file `Papers/Fabius Asymptotic/Fabius Asymptotic.tex` contains **zero**
formal theorem, lemma, proposition, or corollary environments.  The table is
therefore a claim matrix, not a named-environment inventory.  Its public Lean
aggregate is `FabiusFunction.PaperFabiusAsymptotic`.

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
| Equation (11), bounded one-periodic remainder with `E(t) = O(log t / t)` | **Unsupported and not asserted in Lean.** The printed proof uses the false preceding residual estimate. | No declaration claims this refinement. |
| Final sharp formula obtained from equations (8) and (11) | **Not advertised as proved.** It depends on the unsupported periodic refinement. | No declaration claims this formula. |
| Rigorous coarse small-argument replacement | Proved: explicit dyadic error, eventual full-real bound, and `O(t log t)` error | `Fabius.abs_dyadicLogError_le`, `Fabius.eventually_abs_fabiusLogProfile_sub_quadratic_le`, `Fabius.fabiusLogProfile_sub_quadratic_isBigO`, `Fabius.log_fabiusLogPhi_add_quadratic_isBigO` |

The source's intermediate coefficient matching is not a proof about an
arbitrary remainder: its equation (4) drops `R(t)-R(t-1)`, and equation (6)
uses a bound on `R'` that was never assumed.  The Lean development therefore
checks the displayed explicit term through its exact residual instead of
formalizing those circular steps as theorems.

## Local draft: *K-fold summation over the signed Thue--Morse sequence*

The file
`Papers/K-fold summation over the signed Thue-Morse sequence/K-fold summation over the signed Thue-Morse sequence.tex`
also contains **zero** formal theorem, lemma, proposition, or corollary
environments.  Its public Lean aggregate is
`FabiusFunction.PaperKFoldThueMorse`.

| Source claim | Status | Lean declaration(s) |
| --- | --- | --- |
| Thue--Morse sign definition and self-similarity | Proved | `Fabius.binaryWeight`, `Fabius.thueMorseSign`, `Fabius.thueMorseSign_two_mul`, `Fabius.thueMorseSign_two_mul_add_one` |
| Inclusive iterated prefix sums and odd first-prefix zeros | Proved | `Fabius.iteratedPrefix`, `Fabius.iteratedPrefix_succ`, `Fabius.iteratedPrefix_succ_sub`, `Fabius.iteratedPrefix_one_two_mul_add_one` |
| Equation (1), literal normalized grid | Defined exactly | `Fabius.paperPrefixGridValue`, `Fabius.prefixGridPoint` |
| Equation (1), instruction to join consecutive grid points | Defined as the intended polygon, distinct from the contradictory floor/step wording | `Fabius.paperPrefixPolygon`, `Fabius.paperPrefixPolygon_grid`, `Fabius.paperPrefixPolygon_one` |
| Equation (2), discrete functional equation | Proved with the omitted unit-interval index condition made explicit | `Fabius.paperPrefixGridValue_equation`, `Fabius.paperPrefixGridValue_equation_of_pos`, `Fabius.prefixGridPoint_lower_argument_mem` |
| Equation (3), Fabius characterization | Repaired: the bounded derivative equation holds only on `[0,1/2]` and symmetry is required | `Fabius.IsFabius`, `Fabius.existsUnique_fabius` |
| Claimed convergence of the literal equation-(1) normalization | **False**, even pointwise at `x = 1`; the intended polygon has the same obstruction | `Fabius.paperPrefixGridValue_endpoint`, `Fabius.paperPrefixGridValue_endpoint_not_tendsto_one`, `Fabius.paperPrefixPolygon_endpoint_not_tendsto_one` |
| Corrected prefix approximation | Proved pointwise, with one prefix-order shift and the centered-cell interpretation; no uniform rate is claimed | `Fabius.correctedPrefixCoefficient_eq_stepApproximant`, `Fabius.correctedPrefixGridSample_tendsto_rvachevUp`, `Fabius.correctedPrefixGridSample_tendsto_fabius` |
| Repeated-derivative scaling | Proved for the signed global extension; the bounded global wording is domain-invalid | `Fabius.iteratedDeriv_extendedFabius` |
| Exact dyadic zero runs, including “exactly `k`” | Proved | `Fabius.iteratedPrefix_dyadic_endpoint`, `Fabius.iteratedPrefix_dyadic_zero_run`, `Fabius.iteratedPrefix_before_dyadic_run` |
| Equation (4), local `4h` error and global uniform error | **False** for the printed normalization | `Fabius.literalGridSlope_two_one`, `Fabius.literal_local_error_bound_false`, `Fabius.paperPrefixGridValue_endpoint_not_tendsto_one` |
| Equation (5), discrete B-spline kernel and binomial convolution | Proved in exact source-facing form, with a shifted recurrence also available | `Fabius.iteratedPrefixKernel`, `Fabius.iteratedPrefix_eq_sum_kernel`, `Fabius.iteratedPrefix_convolution` |
| Equation (6), both generating-series identities | Proved as formal power-series identities, with finite coefficient stabilization for the infinite product | `Fabius.thueMorseBlockPolynomial_eq_product`, `Fabius.coeff_finite_thueMorse_product`, `Fabius.iteratedPrefixSeries_eq`, `Fabius.one_sub_X_pow_mul_iteratedPrefixSeries`, `Fabius.coeff_eq6_finite` |
| Equation (7), maximum proxy | **False**: for every `x > 0` its terms are unbounded and no maximum exists | `Fabius.paperProxyTerm_succ`, `Fabius.paperProxyRatio_tendsto_atTop`, `Fabius.paperProxyTerm_unbounded`, `Fabius.paperProxyTerm_has_no_maximum` |
| Equation (8), continuous stationary equation | Repaired positive-real calculus proved after making the draft's integer-to-real change explicit | `Fabius.paperStirlingPhi_hasDerivAt`, `Fabius.paper_stationary_iff_mul_two_rpow_neg` |
| Equation (9), Lambert `W_{-1}` solution | **Not advertised as proved.** The draft omits necessary domains and this project defines no Lambert-W branch. | No Lambert-W declaration. |
| Equation (10), claimed `O(log n)` error after stationary substitution | **False for the displayed Stirling proxy**: substitution leaves an omitted linear `+n`, which is not `O(log n)` | `Fabius.paperStirlingPhi_of_stationary`, `Fabius.paperStirlingOmittedTerm_not_isBigO_log` |
| Equation (11), coarse log-squared decay | Proved rigorously without the false maximum/Lambert-W chain | `Fabius.log_fabiusLogPhi_add_quadratic_isBigO`, `Fabius.fabiusLogProfile_normalized_tendsto` |
| “Faster than every power” | Proved from smooth flatness | `Fabius.extendedFabius_isLittleO_pow_at_zero`, `Fabius.fabius_isLittleO_pow_at_zero_right` |
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
