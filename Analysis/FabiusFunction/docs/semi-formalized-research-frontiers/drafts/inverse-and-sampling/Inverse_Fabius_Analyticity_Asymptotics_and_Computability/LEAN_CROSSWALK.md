# Lean crosswalk for the canonical inverse-Fabius synthesis

This document records the source-level Lean correspondence for the 194 immutable source-result rows in theorem_concordance.csv and for five post-snapshot results added directly to the canonical volume.

## Evidence boundary

The audit inspected the actual Lean source files below Analysis/FabiusFunction/Lean/FabiusFunction. It did not infer coverage from .olean files, declaration names alone, generated documentation, or historical commit messages.

The inverse-computability tranches were checked by focused compilation of `EffectiveMonotoneInverse`, `EffectiveGapInverse`, `FabiusInverseComputable`, and the facade before this source-only bookkeeping pass. No Lean, Lake, or Git command was run during the bookkeeping update itself. Human-proved frontier result means that the canonical chapter contains a complete human-readable proof but the inspected Lean tree has only partial ingredients or no matching declaration.

The first ten columns of theorem_concordance.csv remain field-for-field identical to audit/source_result_inventory.csv: 194 rows were compared and no immutable-field difference was found.

## Status vocabulary

| Status | Meaning |
|---|---|
| Lean-proved | The source claim has a direct or normalization-equivalent Lean counterpart. The CSV records one principal module and declaration; its disposition note names any adjacent companion declarations needed for a multi-clause paper statement. |
| human-proved frontier result | The canonical text supplies a complete paper proof, but no exact Lean theorem covers the full statement. Formal-series results are not counted as analytic theorems. |
| conjecture | A precise, live, plausible conjecture retained as explicitly nonassertoric. |
| open problem | A research direction or a source conjecture deliberately demoted because the available evidence does not justify a precise conjectural assertion. |
| not applicable | A definition, algorithm specification, example, warning, discharged obligation, or retired/vacuous claim. |

## Coverage totals

| Source package | Rows | Lean-proved | Human-proved | Conjecture | Open problem | Not applicable |
|---|---:|---:|---:|---:|---:|---:|
| Inverse_and_Sampling_Frontiers | 83 | 10 | 50 | 2 | 10 | 11 |
| Inverse_Endpoint_All_Orders | 29 | 1 | 20 | 6 | 0 | 2 |
| Inverse_Fabius_Computability_Report | 40 | 23 | 7 | 1 | 4 | 5 |
| inverse_fabius_iterates_nowhere_analytic | 24 | 2 | 17 | 1 | 1 | 3 |
| Non_Elementarity_of_the_Fabius_Function | 18 | 14 | 1 | 0 | 0 | 3 |
| **Total** | **194** | **49** | **96** | **10** | **15** | **24** |

The high human-proved count is intentional. In particular, a full forward asymptotic expansion composed with F inverse is not an explicit all-orders inverse reversion theorem, and a formal Catalan or Richardson identity is not an analytic asymptotic for the actual finite-prefix quantiles.

## Canonical-label mapping

Most retained source labels use a stable namespace prefix:

| Source package or prefix | Canonical prefix |
|---|---|
| Inverse_and_Sampling_Frontiers p1, p2, p3 | is:p1, is:p2, is:p3 |
| Inverse_Endpoint_All_Orders | ao |
| Inverse_Fabius_Computability_Report | co |
| Non_Elementarity_of_the_Fabius_Function | ne |
| inverse_fabius_iterates_nowhere_analytic | ii |

The four historically unlabelled computability problems receive stable labels comp:prob:near-optimal-evaluation, comp:prob:uniform-base, comp:prob:atomic-transport, and comp:prob:branch-atlas.

Important non-identity mappings are:

| Source label | Canonical destination | Disposition |
|---|---|---|
| p1:thm:phase-two-orders | ao:thm:all-orders | Low-order specialization absorbed into the stronger all-orders theorem. |
| p1:cor:first-oscillatory-inverse | ao:thm:all-orders | First relative correction absorbed into the all-orders expansion. |
| p1:thm:inverse-limit-set | ao:thm:phase-locked | The normalized cluster interval is grouped with phase-locked endpoint sequences. |
| p1:thm:quantile-elasticity | ao:thm:elasticity | Two-term result absorbed into the all-orders elasticity theorem. |
| p1:thm:all-orders-endpoint-recursion | ao:thm:all-orders | The triangular recursion is part of the stronger canonical theorem. |
| p2:thm:algebraic-inverse-germ | is:p2:thm:algebraic-inverse-germ | The full reduced-dyadic algebraic shadow and nonzero flat-remainder theorem is retained; its general form remains outside Lean. |
| p2:thm:Catalan-quarter | is:p2:thm:Catalan-quarter | The complete quarter-point theorem is retained explicitly. Lean proves its all-order derivative formula, but not every clause of the packaged theorem, so the source row is human-proved. |
| p3:conj:positive-extremality | is:p3:prob:sparse-positive-phase | Corrected and demoted from an unsupported extremality conjecture to a sparse positive-filter design problem. |
| p3:conj:quantile-phase-locking | is:p3:prob:quantile-endpoint-alias | Corrected and demoted to the missing uniform endpoint/alias matching problem. |
| p3:conj:primitive-rules | none | Retired as vacuous: least-common-denominator normalization already forces primitive integer weights. |
| p1:conj:natural-threshold | none | Retired; the proved eventual-threshold result remains, while the universal n >= r+1 cutoff had no proof or Lean support. |

The four unlabelled source obligations are marked not applicable and point to the theorem that discharges them. The unlabelled first-derivatives example is folded into is:p2:thm:inverse-derivatives.

## Exact declaration index

The table below is generated from the 49 Lean-proved concordance rows. Declaration names are fully qualified.

| Source key | Canonical label | Lean module | Principal declaration |
|---|---|---|---|
| Inverse_and_Sampling_Frontiers:p1:lem:filter-moments | is:p1:lem:filter-moments | FabiusFunction.GeometricLagrangeQMoments | Fabius.quarterGeometricLagrangeQMoment_eq_residual_qBinomial |
| Inverse_and_Sampling_Frontiers:p1:thm:quarter-exact | is:p1:thm:quarter-exact | FabiusFunction.QuarterQuantile | Fabius.quarterQuantile_eq |
| Inverse_and_Sampling_Frontiers:p3:thm:self-sampling | is:p3:thm:self-sampling | FabiusFunction.PolynomialCombExactness | Fabius.integral_polynomial_mul_rvachevUp_eq_dyadic_tsum |
| Inverse_and_Sampling_Frontiers:p3:thm:Appell-deconvolution | is:p3:thm:Appell-deconvolution | FabiusFunction.RvachevMomentAppell | Fabius.integral_eval_rvachevAppellPolynomial_sub_mul_rvachev |
| Inverse_and_Sampling_Frontiers:p3:cor:Appell-mean-zero | is:p3:cor:Appell-mean-zero | FabiusFunction.RvachevMomentAppell | Fabius.integral_eval_rvachevAppellPolynomial_mul_rvachev_eq_zero |
| Inverse_and_Sampling_Frontiers:p3:cor:polynomial-deconvolution | is:p3:cor:polynomial-deconvolution | FabiusFunction.RvachevPolynomialSynthesis | Fabius.normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp |
| Inverse_and_Sampling_Frontiers:p3:prop:half-integer-sign | is:p3:prop:half-integer-sign | FabiusFunction.ThueMorseLobeSign | Fabius.rvachevFourierProduct_eq_thueMorse_sign_mul_norm |
| Inverse_and_Sampling_Frontiers:p3:lem:phi-half-lower | is:p3:lem:phi-half-lower | FabiusFunction.SincProductPositive | Fabius.four_ninths_lt_re_rvachevFourierProduct_half |
| Inverse_and_Sampling_Frontiers:p3:cor:forced-superconvergence | is:p3:cor:forced-superconvergence | FabiusFunction.RvachevSuperconvergentSynthesis | Fabius.integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent |
| Inverse_and_Sampling_Frontiers:p3:thm:Appell-lattice-reproduction | is:p3:thm:Appell-lattice-reproduction | FabiusFunction.RvachevSuperconvergentSynthesis | Fabius.normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent |
| Inverse_Endpoint_All_Orders:thm:K-decomposition | ao:thm:K-decomposition | FabiusFunction.NegativeLaplace | Fabius.negativeLaplaceLog_exact_periodic_decomposition |
| Inverse_Fabius_Computability_Report:thm:main | co:thm:main | FabiusFunction.FabiusInverseComputable | Fabius.fabiusInv_isComputableRealFunction |
| Inverse_Fabius_Computability_Report:thm:centered-error | co:thm:centered-error | FabiusFunction.FabiusComputability | Fabius.abs_uniformCenteredPartialCDF_sub_fabiusReal_le |
| Inverse_Fabius_Computability_Report:cor:F-computable | co:cor:F-computable | FabiusFunction.FabiusComputableSpline | Fabius.fabiusReal_isComputableRealFunction |
| Inverse_Fabius_Computability_Report:prop:strict-increase | co:prop:strict-increase | FabiusFunction.Monotonicity | Fabius.strictMonoOn_fabiusReal |
| Inverse_Fabius_Computability_Report:prop:density-shape | co:prop:density-shape | FabiusFunction.Convexity | Fabius.strictMonoOn_deriv_fabiusReal_Icc |
| Inverse_Fabius_Computability_Report:thm:least-mass | co:thm:least-mass | FabiusFunction.InverseModulus | Fabius.fabiusIntervalMass_eq_fabiusReal_iff |
| Inverse_Fabius_Computability_Report:cor:global-increment-shape | co:cor:global-increment-shape | FabiusFunction.InverseModulus | Fabius.fabiusReal_add_le |
| Inverse_Fabius_Computability_Report:thm:exact-inverse-modulus | co:thm:exact-inverse-modulus | FabiusFunction.InverseModulus | Fabius.sSup_abs_fabiusInv_sub_eq |
| Inverse_Fabius_Computability_Report:cor:effective-injectivity | co:cor:effective-injectivity | FabiusFunction.InverseModulus | Fabius.abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal |
| Inverse_Fabius_Computability_Report:thm:exact-strict-threshold | co:thm:exact-strict-threshold | FabiusFunction.InverseModulus | Fabius.forall_abs_fabiusInv_sub_lt_iff |
| Inverse_Fabius_Computability_Report:thm:closed-dyadic-modulus | co:thm:closed-dyadic-modulus | FabiusFunction.FabiusInverseEffectiveContinuity | Fabius.abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator |
| Inverse_Fabius_Computability_Report:thm:reciprocal-modulus | co:thm:reciprocal-modulus | FabiusFunction.FabiusInverseLogarithmicModulus | Fabius.fabiusInv_effectivelyUniformContinuous_logarithmicDelta |
| Inverse_Fabius_Computability_Report:lem:difference-certificate | co:lem:difference-certificate | FabiusFunction.EffectiveMonotoneInverse | Fabius.tolerantDifference_error |
| Inverse_Fabius_Computability_Report:lem:safe-updates | co:lem:safe-updates | FabiusFunction.EffectiveMonotoneInverse | Fabius.tolerantDifference_safe_updates |
| Inverse_Fabius_Computability_Report:lem:near-branch | co:lem:near-branch | FabiusFunction.EffectiveMonotoneInverse | Fabius.tolerantDifference_inconclusive |
| Inverse_Fabius_Computability_Report:thm:bisection-correct | co:thm:bisection-correct | FabiusFunction.EffectiveMonotoneInverse | Fabius.tolerantBisection_correct |
| Inverse_Fabius_Computability_Report:cor:G-sequential | co:cor:G-sequential | FabiusFunction.EffectiveMonotoneInverse | Fabius.effectiveInversionOn_Icc |
| Inverse_Fabius_Computability_Report:lem:clamp-computable | co:lem:clamp-computable | FabiusFunction.EffectiveMonotoneInverse | Fabius.unitClamp_sequentiallyComputable |
| Inverse_Fabius_Computability_Report:cor:GT-sequential | co:cor:GT-sequential | FabiusFunction.FabiusInverseComputable | Fabius.fabiusInv_isComputableRealFunction |
| Inverse_Fabius_Computability_Report:thm:abstract-inversion | co:thm:abstract-inversion | FabiusFunction.EffectiveGapInverse | Fabius.effectiveInversionOn_Icc_of_computablePositiveRationalGap |
| Inverse_Fabius_Computability_Report:lem:flatness-upper | co:lem:flatness-upper | FabiusFunction.SharpFlatness | Fabius.fabiusReal_le_two_pow_div_factorial_mul_pow |
| Inverse_Fabius_Computability_Report:thm:no-holder | co:thm:no-holder | FabiusFunction.FabiusInverseAsymptotic | Fabius.not_exists_fabiusInv_le_const_mul_rpow_near_zero |
| Inverse_Fabius_Computability_Report:cor:sub-holder | co:cor:sub-holder | FabiusFunction.FabiusInverseAsymptotic | Fabius.tendsto_fabiusInv_div_rpow_atTop_at_zero_right |
| Non_Elementarity_of_the_Fabius_Function:thm:nowhere | ne:thm:nowhere | FabiusFunction.NowhereAnalytic | Fabius.canonical_fabius_analyticAt_iff |
| Non_Elementarity_of_the_Fabius_Function:thm:density | ne:thm:density | FabiusFunction.ElementaryFunction | Fabius.IsElementary.dense_analyticLocus |
| Non_Elementarity_of_the_Fabius_Function:cor:main | ne:cor:main | FabiusFunction.NotElementary | Fabius.canonical_fabius_not_isElementary_eqOn_of_interior_nonempty |
| Non_Elementarity_of_the_Fabius_Function:prop:comp | ne:prop:comp | FabiusFunction.ElementaryFunction | Fabius.IsElementary.comp |
| Non_Elementarity_of_the_Fabius_Function:lem:open | ne:lem:open | FabiusFunction.ElementaryFunction | Fabius.isOpen_analyticLocus |
| Non_Elementarity_of_the_Fabius_Function:lem:key | ne:lem:key | FabiusFunction.ElementaryFunction | Fabius.dense_analyticLocus_comp |
| Non_Elementarity_of_the_Fabius_Function:thm:algebraic | ne:thm:algebraic | FabiusFunction.AlgebraicBranch | Fabius.analyticDenseOn_of_algebraic |
| Non_Elementarity_of_the_Fabius_Function:cor:algebraic | ne:cor:algebraic | FabiusFunction.NotElementary | Fabius.not_algebraicBranch_eqOn |
| Non_Elementarity_of_the_Fabius_Function:thm:ift | ne:thm:ift | FabiusFunction.InverseBranch | Fabius.analyticAt_of_rightInverse |
| Non_Elementarity_of_the_Fabius_Function:thm:invnowhere | ne:thm:invnowhere | FabiusFunction.InverseNotElementary | Fabius.analyticLocus_fabiusInv |
| Non_Elementarity_of_the_Fabius_Function:cor:invmain | ne:cor:invmain | FabiusFunction.InverseNotElementary | Fabius.not_eqOn_fabiusInv_of_dense_analyticLocus |
| Non_Elementarity_of_the_Fabius_Function:thm:invbranch | ne:thm:invbranch | FabiusFunction.InverseBranch | Fabius.analyticDenseOn_of_rightInverse |
| Non_Elementarity_of_the_Fabius_Function:thm:plusdense | ne:thm:plusdense | FabiusFunction.InverseBranch | Fabius.IsElementaryOrInverse.dense_analyticLocus |
| Non_Elementarity_of_the_Fabius_Function:cor:plusmain | ne:cor:plusmain | FabiusFunction.InverseNotElementary | Fabius.not_isElementaryOrInverse_eqOn_fabiusInv |
| inverse_fabius_iterates_nowhere_analytic:prop:fixed-k-minimum | ii:prop:fixed-k-minimum | FabiusFunction.PartitionDefect | Fabius.partitionDefect_fixed_block_eq_iff |
| inverse_fabius_iterates_nowhere_analytic:prop:first-shell | ii:prop:first-shell | FabiusFunction.PartitionDefect | Fabius.partitionDefect_eq_firstShell_iff |

Several paper rows contain multiple clauses. For those rows, the principal declaration above belongs to the following explicit finite family; the CSV repeats the exact family at the source-row level.

- Quarter-scale filter moments: `Fabius.geometricLagrangeQMoment_zero`, `Fabius.quarterGeometricLagrangeQMoment_eq_zero`, and `Fabius.quarterGeometricLagrangeQMoment_eq_residual_qBinomial` prove normalization, the cancelled range, and every residual moment.
- Density shape: `Fabius.strictMonoOn_deriv_fabiusReal_Icc`, `Fabius.strictAntiOn_deriv_fabiusReal_Icc`, and `Fabius.deriv_fabiusReal_one_sub` prove the two strict branches and reflection.
- Inverse Fabius computability: `Fabius.fabiusInv_isComputableRealFunction` packages sequential computability of the totalized inverse together with the logarithmic-Delta effective-continuity witness. `Fabius.effectiveInversionOn_Icc` supplies the unit-interval realizer, while `Fabius.abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator`, `Fabius.inverseFabiusLogarithmicOrder_isLeast`, and `Fabius.fabiusInv_effectivelyUniformContinuous_logarithmicDelta` supply the headline theorem's explicit dyadic and reciprocal-modulus clauses.
- Tolerant bisection: `Fabius.tolerantDifference_error`, `Fabius.tolerantDifference_safe_updates`, and `Fabius.tolerantDifference_inconclusive` certify the three comparison branches; `Fabius.tolerantBisection_correct` constructs the uniform computable output name, and `Fabius.unitClamp_sequentiallyComputable` supports totalization.
- Abstract effective inversion: the eight public declarations are `Fabius.EffectivelyUniformContinuousOn`, `Fabius.ComputablePositiveRationalSequence`, `Fabius.ComputablePositiveRationalSequence.value`, `Fabius.ComputablePositiveRationalSequence.reciprocalDenominator`, `Fabius.ComputablePositiveRationalSequence.reciprocalDenominator_spec`, `Fabius.inverseModulus_of_positiveRationalGap`, `Fabius.effectiveInversionOn_Icc_of_computablePositiveRationalGap`, and `Fabius.clampedEffectiveInversion_of_computablePositiveRationalGap`.  The principal theorem derives the reciprocal inverse modulus from computable positive rational forward gaps and proves subset sequential computability plus subset effective uniform continuity; the last declaration is the clamped total `IsComputableRealFunction` wrapper.
- Least interval mass: `Fabius.fabiusIntervalMass_reflect`, `Fabius.fabiusIntervalMass_eq_zero_of_add_nonpos`, `Fabius.fabiusIntervalMass_eq_zero_of_one_le`, `Fabius.strictMonoOn_fabiusIntervalMass_firstHalf`, `Fabius.strictAntiOn_fabiusIntervalMass_secondHalf`, `Fabius.fabiusReal_sub_le_sub`, `Fabius.fabiusIntervalMass_eq_fabiusReal_iff`, and `Fabius.fabiusReal_sub_eq_sub_iff` prove the global shape, minimum, and both equality formulations.
- Global increment shape: `Fabius.monotoneOn_fabiusIntervalMass_firstHalf`, `Fabius.antitoneOn_fabiusIntervalMass_secondHalf`, `Fabius.fabiusReal_add_le`, and `Fabius.fabiusReal_add_eq_iff` prove the half-line shape, constrained superadditivity, and its equality locus.
- Exact inverse modulus: `Fabius.sSup_abs_fabiusInv_sub_Icc_eq`, `Fabius.sSup_abs_fabiusInv_sub_eq`, `Fabius.fabiusInv_min_one`, `Fabius.abs_fabiusInv_sub_le`, `Fabius.fabiusInv_sub_le_sub`, `Fabius.fabiusInv_add_le`, `Fabius.fabiusInv_sub_eq_sub_iff_of_mem_Icc`, and `Fabius.abs_fabiusInv_sub_eq_iff_of_mem_Icc` prove the two exact suprema, saturation, pointwise and order-free gap inequalities, subadditivity, and equality loci.
- Effective injectivity: `Fabius.abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal`, `Fabius.abs_fabiusInv_sub_le_of_abs_sub_le_fabiusReal`, and `Fabius.fabiusReal_le_abs_sub_of_le_abs_fabiusInv_sub` prove the strict, closed, and contrapositive forms.
- Closed dyadic modulus: `Fabius.abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator` is the exact source theorem, and `Fabius.abs_fabiusInv_sub_le_inverse_two_pow_of_le_deltaDenominator` is the documented closed-boundary strengthening.
- Forced superconvergence: `Fabius.isRvachevSuperconvergentPhase_two_pow_iff` identifies the paper's parity-selected phases at mesh `M = 2^N`, and `Fabius.integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent` is the exact physical-coordinate quadrature theorem through degree `N + 1`. `Fabius.rvachevUp_nonneg`, `Fabius.rvachev_pos_iff_mem_Ioo`, `Fabius.rvachevDyadic_cast`, and `Fabius.rvachevUp_eq_zero_iff_not_mem_Ioo` supply the cited positivity, strict-support, rational-dyadic-value, and zero-off-support facts. These declarations do not classify all superconvergent phases or prove a sharpness theorem.
- Appell lattice reproduction: `Fabius.normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp`, specialized to `M = 2^N` and `P = X^n`, proves the arbitrary-phase formula for `n <= N`; `Fabius.normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent` proves the selected-phase extension through `n <= N + 1`, with `Fabius.isRvachevSuperconvergentPhase_two_pow_iff` translating the phase condition and `Fabius.finite_support_comb` certifying finiteness. No phase-classification or sharpness claim is inferred.
- Endpoint non-Hölder behavior: `Fabius.not_exists_fabiusInv_le_const_mul_rpow_near_zero` gives the zero-endpoint obstruction, `Fabius.tendsto_one_sub_fabiusInv_div_one_sub_rpow_atTop_at_one_left` gives its reflected endpoint-one form, and `Fabius.tendsto_fabiusInv_div_rpow_atTop_at_zero_right` together with `Fabius.sSup_abs_fabiusInv_sub_Icc_eq` gives the exact-modulus quotient divergence.
- Inverse nonrepresentability: `Fabius.not_eqOn_fabiusInv_of_dense_analyticLocus` together with `Fabius.IsElementary.dense_analyticLocus` proves the arbitrary nonempty-interior-set statement; `Fabius.canonical_fabiusInv_not_isElementary_on_Ioo` is its canonical-interval specialization.
- Fixed-block partition defect: `Fabius.partitionDefect_fixed_block_bound` and `Fabius.partitionDefect_fixed_block_eq_iff` prove the sharp minimum and complete equality profile.

## Formal kernels of stronger human-proved results

The following three canonical results have substantial Lean ingredients, but the
full paper statement is stronger than the cited declaration. They are therefore
classified as human-proved frontier results, and their Lean fields are
deliberately blank in the concordance.

| Canonical result | Formal kernel | Unformalized bridge or clause |
|---|---|---|
| `is:p3:prop:local-factorization` | `FabiusFunction.IntegerZeroLocalFactorization.Fabius.rvachevFourierProduct_int_add_factorization` proves the denominator-cleared integer-zero factorization; adjacent declarations construct the analytic cofactor and its derivative engine. | The same proposition includes the normalized exponential local form and its explicit logarithmic jet. |
| `is:p3:thm:first-defect` | `FabiusFunction.CombDefectSeries.Fabius.tsum_shifted_monomial_sub_integral_odd` proves the odd-alias representation, and `FabiusFunction.CombFirstDefect.Fabius.iteratedDeriv_rvachevFourierProduct_nat_mul_int_of_odd` evaluates the surviving derivative. | No named declaration assembles the evaluated complex series and both displayed sine/cosine forms. |
| `co:thm:abstract-inversion` | `FabiusFunction.EffectiveMonotoneInverse.Fabius.effectiveInversionOn_Icc` proves subset-domain sequential computability for an inverse once a computable positive reciprocal inverse modulus is supplied. | The paper starts from a computable positive forward-gap sequence, derives the inverse modulus, and also concludes effective uniform continuity. That gap-to-modulus/effective-continuity bridge is not packaged by the Lean theorem. |

## Post-source strengthenings

Five result labels were added directly to the canonical synthesis after the immutable source snapshot. They therefore have no concordance rows and do not change the 194-row source totals. Three are Lean-proved, one is human-proved, and one is an open problem.

### Exact Lean strengthening: derivative distributions

The canonical theorem rvd:thm:derivative-distribution has no concordance row because it was added after the immutable source snapshot. It is nevertheless directly backed by FabiusFunction.RvachevDerivativeDistribution.

The formal theorem family proves:

- the cell identity through Fabius.iteratedDeriv_rvachev_cell;
- its zero and absolute-value specializations through Fabius.iteratedDeriv_rvachev_cell_zero and Fabius.abs_iteratedDeriv_rvachev_cell;
- the general test-function integral law through Fabius.intervalIntegral_comp_iteratedDeriv_rvachev;
- normalized signed and absolute test-function laws through Fabius.intervalIntegral_comp_normalized_iteratedDeriv_rvachev and Fabius.intervalIntegral_comp_normalized_abs_iteratedDeriv_rvachev;
- signed and absolute Borel pushforward equalities through Fabius.map_normalized_iteratedDeriv_rvachev_restrict_Icc and Fabius.map_normalized_abs_iteratedDeriv_rvachev_restrict_Icc;
- natural signed moments, their even/odd specializations, and all nonnegative real absolute moments through Fabius.intervalIntegral_iteratedDeriv_rvachev_pow, Fabius.intervalIntegral_iteratedDeriv_rvachev_pow_of_even, Fabius.intervalIntegral_iteratedDeriv_rvachev_pow_eq_zero_of_odd, and Fabius.intervalIntegral_abs_iteratedDeriv_rvachev_rpow.

This result is not Appell biorthogonality. Its test function is applied to the value of an iterated derivative. It does not prove an integral pairing of an iterated derivative with an Appell polynomial in the spatial variable.

### Other exact Lean additions

The complete geometric residual theorem `is:p2:thm:geometric-lagrange-residual` is represented by `Fabius.sum_geometricLagrangeWeight_mul_pow_of_pos` in `FabiusFunction.GeometricResidualMoments`, together with `Fabius.completeHomogeneousEval_geometric` for the complete-homogeneous-polynomial form. For the paper's real hypothesis `0 < q < 1`, the required injectivity of the finite node family `j ↦ q^j` is immediate. These declarations cover both displayed residual forms and the vanishing range encoded by the Gaussian binomial.

The finite-product loss lemma `is:p3:lem:finite-product-loss` is exactly the initial-segment Weierstrass inequality `Fabius.one_sub_sum_range_le_prod_range_one_sub` in `FabiusFunction.WeierstrassProductBound`, instantiated with the range of length `J + 1`.

### Human-proved addition and new open problem

The base-b density proposition `is:p3:prop:base-b-density` constructs a nonnegative compactly supported smooth density, proves its Fourier product, total mass, exact support, and infinite-convolution interpretation, and thereby closes the analytic existence gap in the source base-b extension. `FabiusFunction.GeometricScaleProducts` formalizes the abstract geometric-product renormalization mechanism, but it does not construct this density or prove the proposition's full analytic statement. The proposition is therefore a human-proved frontier result.

The dyadic singularity atlas `is:p2:prob:dyadic-singularity-atlas` is explicitly an open problem asking for a recursive classification beyond the proved quarter- and eighth-point models.

## Principal formalization boundaries

| Area | Exact Lean core | Missing full bridge |
|---|---|---|
| Explicit all-orders inverse endpoint expansion | Full forward all-orders expansion, implicit pullback along the inverse, sharp leading inverse scale, Gamma-zeta periodic data | Explicit inverse coefficient reversion, diagonal formulas, inverse top jets, elasticity hierarchy, W-resummation, Gevrey/transseries theory |
| Inverse computability | Forward computability, sharp inverse modulus, effective injectivity, explicit effective continuity, tolerant bisection, computable positive-rational gap encoding, derived reciprocal inverse modulus, restricted inverse sequential computability, subset effective uniform continuity, computable clamping, and totalized `IsComputableRealFunction` theorems | Exact endpoint-mass ceiling minimality and input-bit asymptotics |
| Inverse iterates | Single-inverse nonanalyticity and exact PartitionDefect combinatorics | Every n > 1 iterate theorem, zero-radius transport, spine dominance, formal-reversion radius |
| Dyadic inverse germs | Exact quarter quantile, analytic quarter germ, complete quarter inverse jet | General reduced-dyadic analytic shadow, nonzero flat remainder, all-dyadic inverse derivatives |
| Appell and Bernoulli structure | Appell derivative/translation laws, moments, cumulants, continuous deconvolution, polynomial synthesis | Logistic dual, Barnes identifications, full finite-prefix collapse/recovery, some displayed Bernoulli recurrences |
| Shifted self-sampling | Exact polynomial self-sampling, sharp mesh exactness, integer-zero factorization, half-integer sign, positive half-frequency bound | Entire master-alias convergence theorem, complete phase classification, positive-filter uniqueness, tensor/base-b quadrature |

## Conjecture and problem discipline

All 10 rows classified as conjecture map to canonical conjecture environments and claim no proof. All 15 open-problem rows map to canonical problem environments. The source conjectures demoted to problems have explicit correction rationales in the CSV. The primitive-rule conjecture and the natural-threshold conjecture are not silently preserved as facts.

The six all-orders endpoint conjectures remain conjectural: Gevrey-one growth, optimal truncation, sharp strip inheritance, nonconstant phase at every inverse order, a two-level exponentially improved transseries, and a universal diagonal inversion class.

The direct inverse-spine asymptotic remains the one inverse-iterate conjecture. The former nested-Lambert conjecture is now a precise open problem: it asks for a recursive scale, coefficient, remainder, and non-erasure theorem rather than asserting an unsupported law.

## Highest-value next formalizations

1. Formalize exact endpoint-mass ceiling minimality and the asymptotically sharp input-bit requirement on top of the existing inverse-modulus bounds.
2. Build a generic asymptotic series-reversion layer with Bell-polynomial coefficient extraction, then instantiate it with the existing forward Lambert expansion.
3. Prove positive convergence-radius preservation under formal compositional inversion and use it for the iterate Taylor-radius transport theorem.
4. Formalize the Q-factorization and analytic spine estimates on top of PartitionDefect; the existing defect theorems do not by themselves prove iterate nonanalyticity.
5. Generalize the quarter-cell analytic germ and inverse-jet bridge to every reduced dyadic point.
6. Assemble the coefficientwise comb identities into the entire master-alias theorem with locally normal convergence.
7. Derive the displayed Bernoulli-refined Appell recurrence and separate any genuine Appell biorthogonality theorem from the derivative-distribution pushforward law.
8. Define the regrouped 2-adic exponential B-series and prove its Mellin representation, contour shift, and saddle map.

## Static consistency checks performed

- Exactly 194 concordance rows.
- No blank canonical status or disposition note.
- Every Lean-proved row has both a module and declaration; no other status has Lean fields.
- Every retained assertion has a canonical label.
- Every conjecture maps to a conjecture label and every open problem maps to a problem label.
- Every populated canonical label was present in the current canonical chapter sources.
- All ten immutable source fields matched audit/source_result_inventory.csv for every row.

These are static source and CSV checks only. They are not a substitute for the consolidated Lean build, the canonical validator's pinned-history replay, or the publication build.
