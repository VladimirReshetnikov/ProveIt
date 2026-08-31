# Lean crosswalk for *Fabius dyadic chaos frontiers*

This file is a bookkeeping index between the labeled mathematical statements
in `fabius_dyadic_chaos_frontiers.tex` and the current Lean corpus.  It is not
an additional mathematical exposition, and it does not change the provenance
claims made in the paper.

> **Critical status distinction.**  The symbols **P** and **I** in the paper
> are *paper-provenance markers*: **P** means “proved in this report” and **I**
> means “imported from the surrounding human-readable corpus.”  They do **not**
> mean “proved in Lean.”  The original intake contained 36 nonconjectural
> labeled results.  The maintained report now contains 41: five deliberately
> statement-exact additions are compiler-backed, while the other 36 retain
> the status recorded below.

## Lean-status legend

- **Unformalized**: the Lean tree has no declaration encoding the result's
  defining objects and conclusion.  Generic Mathlib facts may still be
  available.
- **Partial**: exact prerequisites, a finite/algebraic core, or a close analogue
  is already formalized, but at least one substantial report-specific bridge
  remains.
- **Near-complete**: the report statement appears to be a direct specialization
  or short composition of strong existing theorems, but that specialization or
  composition is not itself a Lean declaration.  This is still **not** a claim
  that the report theorem has compiled.
- **Complete**: every mathematical clause of the report statement has an exact,
  compiler-validated Lean counterpart under hypotheses no stronger than the
  report's and with the same or a stronger conclusion.  No analytic,
  probabilistic, indexing, or normalization bridge remains for that label.

All declaration names below were checked against source declarations, not
inferred from filenames.  Module names such as
`FabiusFunction.ThueMorseMixedDifference` correspond to files under
`Analysis/FabiusFunction/Lean/FabiusFunction/`.

## Auditable inventory

| Report class | Number in report |
|---|---:|
| Theorem | 14 |
| Proposition | 8 |
| Lemma | 3 |
| Corollary | 16 |
| **Nonconjectural total** | **41** |

| Lean status | Number below |
|---|---:|
| Unformalized | 12 |
| Partial | 21 |
| Near-complete | 3 |
| Complete | 5 |
| **Crosswalk total** | **41** |

The ordinal in the first column is solely an audit key.  The original keys
1--36 remain stable; the five formalization-backed additions are appended as
37--41 even though they occur at their natural expository locations in the
report.  Every theorem/proposition/lemma/corollary label from the TeX source
occurs exactly once in the following table.

Rows 37--41 track the activation source milestone
`f45041685da96aae71cbd8d2d7979476eefe93ec`.  This current provenance
supersedes the narrower historical activation checkpoint `7c8d1f1...`
without rewriting that older checkpoint's evidence.

| # | Exact report label and class | Report title | Provenance | Lean status | Existing declarations and exact remaining gap |
|---:|---|---|:---:|---|---|
| 1 | `thm:exact-Hoeffding` — theorem | Exact dyadic Hoeffding components | P | **Partial** | `Fabius.ProbabilityRepresentation.independent_uniform_coordinates`, `coordinate_has_uniform_law`, and `weightedUniformSeries` in `FabiusFunction.WeightedUniformSeries` construct the independent coordinates and their series; `Fabius.rvachevMeasure_eq_map_weightedSum` in `FabiusFunction.RandomSeriesLaw` identifies its law; `Fabius.integrable_exp_rvachevMeasure` in `FabiusFunction.GeometricCgfTails` supplies exponential integrability.  Missing are the coordinate conditional-expectation operators, the exact finite-support Hoeffding projections, orthogonality, and the unconditional `L²` sum over `Finset ℕ` with the tail normalization used in the report. |
| 2 | `cor:R-product` — corollary | Second-moment product and refinement quotient | P | **Partial** | `FabiusFunction.HyperbolicActivation` now defines the totalized real hyperbolic sinc and activation odds and proves `one_add_activationOdds`, `activationOdds_nonneg`, and `activationOdds_pos_iff`.  `Fabius.geometric_tail_dictionary_up` in `FabiusFunction.GeometricTailDictionary` gives exact finite-prefix MGF refinement, while `Fabius.centeredComplexGeneratingFunction_eq_centeredSincProduct` and `centeredComplexGeneratingFunction_shell` in `FabiusFunction.FourierLaplaceRotation` give the centered entire-product and shell laws.  Missing are the summable infinite odds product `R(t)=∏(1+r_j)`, its exact identification with the report's real MGF quotient, and the variance formula. |
| 3 | `prop:chaos-refinement` — proposition | Dyadic chaos refinement | P | **Partial** | `Fabius.centeredComplexGeneratingFunction_shell` in `FabiusFunction.FourierLaplaceRotation` is the exact dyadic shell analogue.  Lean lacks the bivariate chaos product `C(t,z)`, its coefficients `A_k`, the coefficient recurrence, and the logarithmic-derivative identity for `A_1`. |
| 4 | `prop:Newton-Bell` — proposition | Newton--Bell formula | P | **Partial** | `Fabius.completeBellPolynomial` and `completeBellPolynomial_succ` in `FabiusFunction.MomentCumulantAlgebra`, `Fabius.elementarySymmetricEval` in `FabiusFunction.SymmetricFunctionOrthogonality`, `Fabius.elementarySymmetricGeneratingSeries_eq_prod` in `FabiusFunction.SymmetricFunctionGenerating`, and the logarithmic product APIs `Fabius.hasSum_powerSum_log_one_sub` / `tsum_log_one_sub` in `FabiusFunction.EulerLogTransform` formalize the finite/formal algebra.  The summable odds sequence `j ↦ r(t2⁻ʲ)`, its power sums `s_l`, and the analytic passage from the infinite product to the displayed Bell formula are absent. |
| 5 | `thm:active-set-law` — theorem | Variance shares are an active-set law | P | **Unformalized** | `FabiusFunction.HyperbolicActivation` now supplies the totalized probabilities `activationProbability` and their exact odds bridge.  No declaration constructs the independent Bernoulli active set with those coordinate probabilities or identifies its law with normalized Hoeffding energy.  This should be proved first as a general finite/countable product-observable theorem and then specialized to dyadic uniform coordinates. |
| 6 | `cor:no-active` — corollary | No-active atom | P | **Unformalized** | The requisite `R` and active-set law are missing.  Existing MGF/product infrastructure does not state `P(K_t=0)=1/R(t)` or the chi-square/Esscher interpretation. |
| 7 | `cor:Sobol` — corollary | Closed Sobol formulae | P | **Unformalized** | No Lean API currently defines these first-order/total-effect Sobol indices or the finite-coordinate Hoeffding projection norm and error.  It depends on #1 and #5. |
| 8 | `lem:p-bounds` — lemma | Activation bounds | P | **Partial** | `FabiusFunction.HyperbolicActivation` defines the totalized `activationProbability`, proves its value at zero and the off-zero identity `activationProbability_of_ne_zero`, continuity and evenness, strict positivity exactly away from zero, the global bounds `activationProbability_le_min_one_sq_div_three` and `activationProbability_lt_one`, and the complementary positive-argument bound `one_sub_activationProbability_le_min_one_inv_of_pos`.  Thus every order/bound clause is formalized, in the stronger global real form where appropriate.  `FabiusFunction.ActivationAsymptotics` additionally proves that the quadratic coefficient tends sharply to `1/3`.  The displayed Taylor jet through `O(x^10)` remains unformalized, so the compound report lemma is still only Partial. |
| 9 | `cor:K-variance-bound` — corollary | Uniform interaction-count variance | P | **Unformalized** | The local inequalities needed for the coarse/fine split are now proved in `FabiusFunction.HyperbolicActivation`.  No Lean object `K_t`, Bernoulli variance sum, or theorem identifying that variance with `∑ p_j(1-p_j)` exists.  After the active-count construction, the remaining work is the dyadic split yielding the explicit `22/9` constant. |
| 10 | `prop:local-Parseval` — proposition | Local active-degree Parseval identity | P | **Partial** | `Fabius.legendrePolynomial` and `integral_sq_eval_legendrePolynomial` in `FabiusFunction.LegendrePolynomial`, the orthogonality theorem `Fabius.integral_eval_legendrePolynomial_mul` in `FabiusFunction.FabiusLegendreSeries`, and `Fabius.hasSum_rvachevLegendreCoefficient_energy` in `FabiusFunction.FabiusLegendreEnergy` provide the one-dimensional Parseval pattern.  Lean lacks the modified spherical-Bessel coefficients `i_n(x)`, their exponential Legendre expansion, the local energy identity, and the totalized degree law `D(0,z)=z`. |
| 11 | `thm:tensor-Legendre` — theorem | Exact tensor-Legendre coefficients | P | **Partial** | The same `FabiusFunction.LegendrePolynomial` foundation and `Fabius.hasSum_legendrePolynomialSeries_eq` / `hasSum_legendrePolynomialSeries_eq_uniform` in `FabiusFunction.LegendreSeriesConvergence` formalize one-dimensional Legendre completeness and convergence; the `FabiusLegendre*` modules formalize a one-dimensional Rvachev expansion only.  Missing are finitely supported multi-indices, infinite tensor basis/conditional-expectation limits, the coefficient product, and the support-energy/Hoeffding identification. |
| 12 | `cor:joint-generating` — corollary | Joint interaction-degree generating function | P | **Unformalized** | No marked active-set process or tensor-coefficient probability generating function is defined.  This follows only after #5, #10, and #11, including the origin convention for `D`. |
| 13 | `lem:replacement-norm` — lemma | Exact replacement norm | P | **Unformalized** | The corpus has no replacement-copy operator `Delta_S`, coordinate-centering projection `Q_j`, or iterated exact `2^|S|` norm identity.  A general independent-coordinate lemma would serve every smooth-observable result below. |
| 14 | `thm:smooth-interaction` — theorem | Mixed-derivative interaction inequality | P | **Partial** | `Fabius.mixedDifference`, `mixedDifference_insert`, and `mixedDifference_eq_sum_powerset_smul` in `FabiusFunction.ThueMorseMixedDifference` give the exact algebra of commuting finite differences.  They do not supply independent replacements, conditional expectations, the multivariate fundamental-theorem-of-calculus estimate, or the `L²` Hoeffding energy bound. |
| 15 | `lem:geometric-e` — lemma | Geometric elementary symmetric function | I | **Partial** | `Fabius.sum_pow_sum_powersetCard_eq_gaussianBinomial` and `sum_pow_sum_powersetCard_Icc_eq_gaussianBinomial` in `FabiusFunction.BitPositionQBinomial`, together with `Fabius.finiteQPochhammerIn_self_mul_gaussianBinomial` in `FabiusFunction.FiniteQBinomialCore`, prove exact finite Gaussian-binomial identities.  The report's infinite elementary-symmetric sums require a summability definition and a rigorously controlled limit as the finite prefix tends to infinity. |
| 16 | `cor:dyadic-interaction` — corollary | Dyadic q-Pochhammer interaction bound | P | **Partial** | The q-Pochhammer factor has the finite exact foundations cited in #15, and `Fabius.geometricUniformWeight`, `hasSum_geometricUniformWeight`, and `geometricUniformSeries` in `FabiusFunction.GeometricUniformLaw` provide the general geometric-q weights.  The analytic interaction inequality and infinite elementary-symmetric limit are both missing. |
| 17 | `thm:monomial-sharp` — theorem | Exact top-order monomial energy | P | **Partial** | `Fabius.mixedDifference_polynomial_eq_coeff_card` in `FabiusFunction.ThueMorseMixedDifference` formalizes exact top-degree finite-difference extraction.  `Fabius.thueMorsePowerSumRing_eq_zero_of_lt` and `thueMorsePowerSumRing_self` in `FabiusFunction.ThueMorsePrefix` give the dyadic Prouhet zero/top moments.  The probabilistic monomial Hoeffding component and its uniform-coordinate `L²` norm are not formalized. |
| 18 | `prop:all-monomial-components` — proposition | All monomial Hoeffding components | P | **Partial** | `Fabius.integral_eval₂_eq_sum_completeBell_momentCumulant` in `FabiusFunction.PolynomialExpectationCumulant` and `Fabius.completeBellPolynomial` in `FabiusFunction.MomentCumulantAlgebra` formalize polynomial expectations through cumulants; `Fabius.centeredRvachevEvenCumulant_eq_bernoulliMersenne_formula` in `FabiusFunction.SinhDivBernoulliLog` supplies the dyadic cumulants.  The conditional multinomial expansion indexed by a finite coordinate set and the product of centered local powers remain absent. |
| 19 | `cor:analytic-tail` — corollary | Analytic-observable order tail | P | **Unformalized** | The report-specific Hoeffding components, total order energy, dyadic q-Pochhammer bound, and orthogonal truncation operator are all missing, so the superexponential tail has no current Lean statement. |
| 20 | `thm:q-leading` — theorem | Dyadic q-binomial chaos asymptotic | P | **Partial** | `FabiusFunction.BitPositionQBinomial`, `FabiusFunction.FiniteQBinomialCore`, `FabiusFunction.SymmetricFunctionGenerating`, and `FabiusFunction.MomentPowerSeries` supply finite q-binomial, symmetric-function, and power-series algebra.  Lean still lacks the analytic local-odds series, the infinite elementary-symmetric coefficient `A_k(t)`, uniform summable remainder control, and the first-correction asymptotic. |
| 21 | `cor:q-leading-general` — corollary | General geometric-q leading law | P | **Partial** | `Fabius.geometricUniformWeight` / `geometricUniformSeries` in `FabiusFunction.GeometricUniformLaw` and `Fabius.geometric_tail_dictionary_geometricUniform` in `FabiusFunction.GeometricUniformDictionary` construct the q-law and its refinement.  `FabiusFunction.GeometricActivationDimension` formalizes summability, refinement, positivity, certified finite-prefix bounds, and the normalized squared-weight sum; `Fabius.tendsto_geometricActivationDimension_div_sq` gives the deterministic activation sum's exact fixed-q leading coefficient `(1-q)/(3*(1+q))` whenever `|q|<1`.  The report corollary instead concerns the q-dependent chaos coefficient `A_k^(q)`, whose infinite elementary-symmetric identity, q-binomial factor, and small-field asymptotic remain absent. |
| 22 | `cor:small-order-law` — corollary | Small-field order law | P | **Unformalized** | The active count, conditional order law, and asymptotics of `A_k/(R-1)` are all absent.  This should be a short corollary only after #5, #20, and the `A_1` leading term are formalized. |
| 23 | `prop:Bell-Bernoulli-energy` — proposition | Bell--Bernoulli energy coefficients | P | **Partial** | `Fabius.centeredRvachevEvenCumulant_eq_bernoulliMersenne_formula` in `FabiusFunction.SinhDivBernoulliLog`, `Fabius.completeBellPolynomial` in `FabiusFunction.MomentCumulantAlgebra`, and the power-series infrastructure in `FabiusFunction.MomentPowerSeries` formalize the coefficient algebra.  Missing are the report's `R`, `log R`, their analytic identities, and the distinct radius proofs (`pi` for `log R`, `4*pi` for `R` and `R-1`). |
| 24 | `prop:mu-refinement` — proposition | Effective-dimension refinement | P | **Partial** | `FabiusFunction.GeometricActivationDimension` defines the totalized geometric activation sum and the dyadic specialization; proves summability for `|q|<1`, the generic and dyadic refinement identities, exact finite-prefix splittings, positivity, the simplified normalized quadratic bound, and certified generic and dyadic tails.  `Fabius.tendsto_geometricActivationDimension_div_sq` and `Fabius.tendsto_dyadicEffectiveDimension_div_sq` now give the deterministic series' exact leading coefficients.  Its algebraic theorem includes negative `q`; the probability-law interpretation remains restricted to the report's `0<q<1`.  Missing are the Bernoulli coefficient formulas, the full convergent power-series identities for `mu` and `mu_q` with their stated radii, and the formal bridge from the deterministic dyadic sum to the active-count expectation.  Hence the compound proposition remains Partial. |
| 25 | `thm:Mellin-p` — theorem | Closed Mellin transforms | P | **Partial** | `Fabius.bose_mellin_integral_zeta` in `FabiusFunction.MellinBose`, `Fabius.mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_pos_re` and `mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_re_zero` in `FabiusFunction.PeriodicFourier`, plus `FabiusFunction.MellinFinitePart` / `BoseFinitePartIntegral`, provide close Mellin--Gamma--zeta templates.  The totalized activation profile and its elementary global bounds now exist in `FabiusFunction.HyperbolicActivation`.  Lean still lacks its derivative formula as a reusable activation theorem, the sech-squared Mellin transform, the two convergence strips, the integration-by-parts bridge, and the boundary continuation convention. |
| 26 | `thm:mu-phase` — theorem | Exact dyadic phase expansion | P | **Unformalized** | `FabiusFunction.GeometricActivationDimension` now defines the dyadic activation sum and proves its refinement and quantitative tail.  No renormalized bilateral lattice sum `P(theta)`, periodic correction `Q`, Mellin-derived phase expansion, or exact `2/t` remainder decomposition is declared. |
| 27 | `thm:Q-Fourier` — theorem | Fourier coefficients of the phase | P | **Partial** | `Fabius.negativeLaplacePsiFourierCoeff_eq_gamma_zeta`, `summable_negativeLaplacePsiFourierCoeff`, and `hasSum_negativeLaplacePsi_fourierSeries` in `FabiusFunction.PeriodicFourier` prove a closely analogous Fourier reconstruction for the negative-Laplace phase.  They do not concern the active-count phase `Q`; the Mellin-to-Fourier transfer and its coefficients must be repeated for the new kernel. |
| 28 | `thm:phase-law` — theorem | Dyadic phase law in total variation | P | **Unformalized** | No bilateral integer-valued phase variable `K_theta`, coupling with `K_t`, total-variation bound, or locally uniform Laurent probability-generating product on `ℂˣ` exists in Lean. |
| 29 | `cor:no-CLT-width` — corollary | No central-limit widening | P | **Unformalized** | The phase coupling and active-count variance series are missing.  The formal proof should use the report's direct tail identity rather than infer uniform integrability of squares from bounded second moments. |
| 30 | `cor:phase-logconcave` — corollary | Log-concavity and full support | P | **Unformalized** | The corpus has no finite Poisson-binomial log-concavity theorem connected to a bilateral total-variation limit, nor the positivity/full-support product argument for `K_theta`. |
| 31 | `thm:Laplace-transfer` — theorem | Exact Laplace transfer of the ANOVA atom | P | **Near-complete** | `Fabius.mgf_weightedSumDistribution_eq_generatingFunction` in `FabiusFunction.FabiusComplexMGF`, `Fabius.ProbabilityRepresentation.weightedSumDistribution_reflection` in `FabiusFunction.ProbabilityRepresentation`, `Fabius.rvachevMeasure_eq_map_weightedSum` in `FabiusFunction.RandomSeriesLaw`, and `Fabius.exp_negativeLaplaceLog_eq_generatingFunction_neg` in `FabiusFunction.NegativeLaplace` supply the law/MGF/Laplace bridges.  The exact no-active probability is not yet defined, so the displayed identity and logarithmic form still need an explicit wrapper theorem and positivity bookkeeping. |
| 32 | `cor:transported-phase` — corollary | Transported quadratic-log phase | P+I | **Near-complete** | `Fabius.negativeLaplaceLog_exact_periodic_decomposition`, `negativeLaplacePeriodicCorrection`, `negativeLaplaceTailError`, and `abs_negativeLaplaceTailError_le_four_exp` in `FabiusFunction.NegativeLaplace` formalize the exact imported endpoint decomposition and tail.  The remaining work is to compose it with #31, normalize variables/constants exactly as in the report, and state the resulting no-active asymptotic. |
| 33 | `thm:TM-corner` — theorem | Continuous Thue--Morse corner identity | P | **Near-complete** | `Fabius.symmetricMixedDifference_eq_sum_powerset_smul`, `symmetricMixedDifference_polynomial_eq_coeff_card`, `symmetricMixedDifference_polynomial_of_degree_lt`, `symmetricMixedDifference_pow_card`, and `symmetricDyadicMixedDifference_eq_sum_thueMorseSign_smul` in the compiler-validated `FabiusFunction.ThueMorseSymmetricDifference` prove the centered Boolean-cube identity, arbitrary-step polynomial extraction/cancellation/top value, and centered dyadic Thue--Morse block.  The report-facing theorems `symmetricDyadicMixedDifference_inv_two_pow_eq_sum_thueMorseSign_smul` and `symmetricDyadicMixedDifference_inv_two_pow_succ_eq_sum_thueMorseSign_smul` give the exact affine grid `x - (1 - 2^(-N)) + k / 2^(N-1)` and complement sign `(-1)^N`, over any characteristic-zero field and with an arbitrary additive target.  They reuse the general mixed-difference/Prouhet core in `FabiusFunction.ThueMorseMixedDifference` and `FabiusFunction.ThueMorsePrefix`.  The only mathematical clause of the report theorem not yet formalized is the repeated-integral identity under its `C^N` hypotheses; after that analytic bridge, one report-shaped wrapper should combine all clauses. |
| 34 | `cor:Walsh-corner` — corollary | Highest Walsh sign coefficient | P | **Partial** | `Fabius.sum_thueMorseSign_smul_eq_mixedDifference` in `FabiusFunction.ThueMorseMixedDifference` gives the finite sign/mixed-difference algebra.  Lean lacks the sign--magnitude probability construction, conditioning on magnitudes and a tail variable, and the conditional-expectation normalization `2^(-N)`. |
| 35 | `prop:Rodrigues-bound` — proposition | Rodrigues bound for local coefficients | P | **Partial** | `Fabius.legendrePolynomial` in `FabiusFunction.LegendrePolynomial` uses Rodrigues normalization, while `Fabius.oddDoubleFactorial`, `oddDoubleFactorial_succ`, and `oddDoubleFactorial_pos` in `FabiusFunction.Arithmetic` provide the denominator arithmetic.  The complex coefficient `i_n(x)`, repeated integration by parts with endpoint vanishing, the beta integral, and the complex norm bound are missing. |
| 36 | `cor:Lambert-degree` — corollary | Lambert-W inversion rule | P | **Partial** | `Fabius.principalLambertW_mul_exp` and `principalLambertW_unique` in `FabiusFunction.PrincipalLambertW`, `Fabius.log_factorial_sub_main_isBigO_log` in `FabiusFunction.StirlingAsymptotics`, and the `PowerExponentialLambert*` modules formalize the inversion technology.  The exact envelope `b_n(x)`, monotone-tail threshold `n_epsilon(x)`, certified tail, odd-double-factorial asymptotic, and the stated epsilon-to-zero asymptotic have not been connected. |
| 37 | `thm:totalized-activation-dictionary` — theorem | Totalized activation dictionary | P | **Complete** | `FabiusFunction.HyperbolicActivation` supplies the literal real-valued statement through the `realSinhc` and `tanhDiv` continuity, parity, positivity, double-angle, and comparison declarations; `one_add_activationOdds`, `one_add_activationOdds_pos`, `activationOdds_of_ne_zero`, `activationOdds_nonneg`, `activationOdds_pos_iff`; and the global odds/probability bridge, sign, and off-zero quotient declarations.  The theorem concerns the real totalized kernel; it does not claim the complex sinc API, analyticity, a random-variable construction, or a Taylor series. |
| 38 | `cor:sharp-activation-quadratic` — corollary | Sharp quadratic activation coefficient | P | **Complete** | `Fabius.tendsto_activationProbability_div_sq` and `Fabius.tendsto_activationProbability_mul_div_sq` in `FabiusFunction.ActivationAsymptotics` give the literal punctured-neighborhood limits `activationProbability x / x^2 -> 1/3` and `activationProbability (a*x) / x^2 -> a^2/3` for every real `a`, including zero.  The proof uses one l'Hopital step and the continuous totalization `tanhDiv`; no Taylor-series conclusion is inferred. |
| 39 | `prop:geometric-activation-dimension` — proposition | Geometric activation dimension | P | **Complete** | `FabiusFunction.GeometricActivationDimension` proves termwise comparison, summability for `|q|<1`, the exact and simplified geometric budgets, `hasSum_normalizedGeometricWeight_sq`, zero/nonnegative/even laws, positivity exactly off zero, one-step and finite-prefix refinements, certified prefix enclosures, and all stated dyadic specializations.  `Fabius.tendsto_geometricActivationDimension_div_sq` and `Fabius.tendsto_dyadicEffectiveDimension_div_sq` in `FabiusFunction.GeometricActivationAsymptotics` prove the exact punctured coefficient `(1-q)/(3*(1+q))` and its dyadic specialization `1/9`.  For negative `q`, this activation result is used here only as a deterministic signed-weight series theorem; the report's positive-weight active-count interpretation remains restricted to `0<q<1`, and equality with `E K_t` is not claimed by this result. |
| 40 | `cor:dyadic-activation-truncation` — corollary | Certified dyadic activation truncation | P | **Complete** | `dyadicEffectiveDimension_eq_sum_range_add`, `dyadicEffectiveDimension_nonneg`, and `dyadicEffectiveDimension_tail_le` give exactly the first-`N` split and tail bound under the index correspondence `j=n+1`.  The omitted term is `dyadicEffectiveDimension ((1/2)^N*t)` and its bound is `(t^2/9)*(1/4)^N = t^2/(9*4^N)`.  This is a deterministic activation-sum theorem, not yet a probability-of-omission statement. |
| 41 | `thm:square-summable-activation-series` — theorem | Square-summable activation series | P | **Complete** | `Fabius.activationProbability_mul_le_quadratic`, `summable_activationProbability_mul_of_summable_sq`, and `tsum_activationProbability_mul_le` in `FabiusFunction.ActivationSeries` prove the pointwise rescaled bound, genuine summability, and global budget for every arbitrary-index square-summable real family, including signed and zero weights.  `Fabius.tendsto_activationProbability_mul_div_sq` is the pointwise scaled-limit engine, and `Fabius.tendsto_tsum_activationProbability_mul_div_sq` in `FabiusFunction.ActivationSeriesAsymptotics` passes it through the sum by Tannery's theorem.  The summability hypothesis rules out reliance on totalized fallback `tsum` semantics. |

### Count check by class and Lean status

| Class | Unformalized | Partial | Near-complete | Complete | Total |
|---|---:|---:|---:|---:|---:|
| Theorem | 3 | 7 | 2 | 2 | 14 |
| Proposition | 0 | 7 | 0 | 1 | 8 |
| Lemma | 1 | 2 | 0 | 0 | 3 |
| Corollary | 8 | 5 | 1 | 2 | 16 |
| **Total** | **12** | **21** | **3** | **5** | **41** |

## Conjectures and open problems

These seven labels are deliberately excluded from the 41-result count.  A
future Lean file may encode them as named propositions for vocabulary and
dependency tracking, but it must not assert them as theorems.

| Exact report label and class | Report title | Current status and nearby Lean material |
|---|---|---|
| `conj:unique-mode` — conjecture | Unique phase mode | Open.  It depends on the unformalized phase law and would require strict adjacent-ratio control beyond the proved non-strict log-concavity. |
| `conj:differential-transcendence` — conjecture | Differential transcendence | Open.  The Thue--Morse/Mahler corpus, especially `FabiusFunction.ThueMorseMahler` and `FabiusFunction.ThueMorseNaturalBoundary`, is contextual only; it does not establish this claim for the report's generating functions. |
| `conj:strict-logconcavity` — conjecture | Strict phase log-concavity | Open.  It strengthens the report's proved non-strict phase-log-concavity corollary; no Lean active-phase law currently exists. |
| `prob:q-phase` — problem | Mellin phase for X_q | Open as stated.  `FabiusFunction.GeometricUniformLaw` and `FabiusFunction.GeometricUniformDictionary` construct the fixed-q law; the fixed-q phase program is not formalized.  For fixed `0<q<1`, the same coupling suggests a theorem before attempting uniform control as `q` approaches the endpoints. |
| `prob:inverse-chaos` — problem | Quantile-chaos transfer | Open.  `FabiusFunction.QuantileTransport` is relevant infrastructure, not a proof of the report's inverse-Fabius chaos law. |
| `prob:best-N` — problem | Optimal coefficient geometry | Open.  The existing one-dimensional `FabiusLegendre*` approximation theory does not solve best N-term selection in the infinite tensor expansion. |
| `prob:TM-sign-topology` — problem | Thue--Morse sign topology | Open.  The `ThueMorse*` Lean modules formalize extensive finite sign algebra and automatic-sequence structure, but not this topological classification. |

Inventory check: **3 conjectures + 4 problems = 7 open labels**.

## Statement hygiene and formalization blockers

The present TeX source already incorporates several repairs that are essential
for a faithful Lean transcription.  They must not be lost when statements are
extracted into declarations:

1. `r` is defined by `m(2x)/m(x)^2-1` at every real `x`, with `r(0)=0`; the
   identity `r(x)=x*coth(x)-1` is restricted to `x != 0`.
2. `p` is totalized by `p(0)=0`, and the complementary bound containing `1/x`
   is restricted to `x>0`.
3. The local marked-degree quotient is used only for `x != 0`, and its
   generating function has the explicit continuous value `D(0,z)=z`.
4. The Bell--Bernoulli theorem distinguishes the Taylor disk `|t|<pi` for
   `log R` from `|t|<4*pi` for `R` and `R-1`.
5. The Mellin proof performs the exponential-series interchange only for
   `Re(s)>2`, extends the sech-squared identity analytically to `Re(s)>0`, and
   then uses integration by parts.  On `Re(s)=0`, `M_p` denotes continuation,
   not its non-absolutely-convergent defining integral.
6. “No central-limit widening” is an asymptotic as `t -> infinity`, uniform in
   dyadic phase, and its variance convergence uses the direct missing-tail
   estimate, not an invalid bounded-second-moment uniform-integrability claim.
7. The bilateral phase PGF is stated for `z ∈ ℂˣ`, with local uniform
   convergence on that punctured plane.
8. Phase log-concavity implies a nonempty finite *interval* of modes; it does
   not by itself imply a one- or two-point plateau.
9. The continuous Thue--Morse corner assumes `g in C^N(I)` on an open interval
   containing the entire integration box.
10. The Lambert cutoff is the minimum on a monotone tail, is proved nonempty,
    and certifies every later coefficient; it is not merely the first observed
    small coefficient.

The remaining blockers are primarily choices that must be made explicit in
Lean rather than defects in the repaired paper statement:

- Choose one canonical product probability space and define coordinate
  conditional expectations, Hoeffding projections, and independent-copy
  replacement operators there.  Ad hoc copies of these objects would make the
  energy, Sobol, smooth-interaction, and tensor results diverge.
- Represent the sum over finite coordinate sets as an explicit `HasSum` (or an
  equivalent orthogonal Hilbert sum) indexed by `Finset ℕ`; “unconditional in
  `L²`” should not be left as prose.
- Define infinite elementary-symmetric sums independently of their closed
  q-Pochhammer value, then prove the finite-prefix limit.  This avoids using the
  desired identity as a definition.
- Translate `g in C^k(I)` into precise `ContDiffOn`/neighborhood hypotheses
  strong enough for the repeated integral and conditional differentiation;
  the notation `norm(g^(k))_infinity` must name its domain.
- Bind all asymptotic parameters explicitly: `k` is fixed in the dyadic
  q-binomial chaos asymptotic, `q` is fixed with `0<q<1` in its geometric-q
  generalization, phase is uniform only where stated, and `x != 0` is fixed as
  epsilon tends to zero in the Lambert-W cutoff theorem.
- Use an integer-valued type for the bilateral limit `K_theta` and a
  natural-valued type for `K_t`; state shifts, laws, moments, and total
  variation through explicit pushforwards rather than silently coercing the
  two types.
- Define the set of modes of an integer-valued law before formalizing the
  phase-log-concavity corollary; positivity, tail decay, interval structure,
  and finiteness are separate lemmas.

## Recommended formalization order

The following order maximizes reuse and exposes errors early.

1. **Finish the local analytic series.**  The compiler-validated
   `HyperbolicActivation`, `ActivationSeries`, `ActivationAsymptotics`,
   `ActivationSeriesAsymptotics`, `GeometricActivationDimension`, and
   `GeometricActivationAsymptotics` modules now provide totalized `realSinhc`,
   `tanhDiv`, odds and probability, all elementary activation bounds, the
   scaled sharp quadratic limit, arbitrary-index square-summable budgets and
   Tannery limit, geometric/dyadic summability and refinement, normalized
   geometric-weight square sum, exact finite-prefix splitting, certified
   geometric tails, and sharp geometric/dyadic coefficients.  The next local
   milestone is the Taylor jet of `activationProbability`, followed by the
   Bernoulli coefficient series and their exact convergence radii.  Those
   remaining analytic clauses close the original report rows #8 and #24 and
   feed #2--#9 and #20--#30.
2. **Finish the symmetric Thue--Morse specialization.**  The compiled
   `FabiusFunction.ThueMorseSymmetricDifference` module now supplies the
   centered wrapper, exact Boolean-cube expansion, polynomial extraction and
   zero/top results, centered dyadic block, and the exact decreasing-weight
   report reindexing.  Add the analytic repeated-integral bridge under precise
   `ContDiffOn`/neighborhood hypotheses, then package a report-shaped wrapper
   theorem to close #33.
3. **General product-observable Hoeffding API.**  On the existing independent
   uniform-coordinate space, formalize finite coordinate projections,
   independent replacements, orthogonality, exact components of a product
   observable, and the active-set energy law.  Specialize only afterward to
   `exp(tX)`.  This single layer feeds #1 and #5--#7, #9, #13--#19, and #34.
4. **Infinite geometric elementary symmetric identity.**  Pass the exact
   finite q-binomial theorems to a summable infinite limit.  Combine it with
   the general mixed-derivative bound for #15--#17 and #19.
5. **Local and tensor Legendre layer.**  Define `i_n`, prove local Parseval and
   its totalized mark, then build finite tensor prefixes and take the `L²`
   martingale limit.  This orders #10 before #11 and #12, and supplies #35.
6. **Bell/q asymptotics.**  Reuse the totalized odds, infinite elementary
   symmetric identity, and existing cumulant/Bell APIs to prove #3--#4,
   #18, and #20--#24 with explicit convergence radii.
7. **Mellin and phase law.**  Formalize the activation Mellin transform using
   the existing Bose/periodic templates, then the lattice phase, Fourier
   series, coupling, tightness, variance tail, and log-concavity in that order
   (#25--#30).
8. **Laplace transport.**  Once the no-active atom exists, package the short
   MGF/reflection bridge (#31) and compose it with the already formalized
   negative-Laplace decomposition (#32).
9. **Rodrigues--Lambert cutoff.**  Complete the complex Legendre coefficient
   bound, define the monotone threshold with `Nat.find`, and connect the
   odd-double-factorial asymptotic to the principal Lambert-W API (#35--#36).

This order deliberately treats the three **near-complete** rows as missing
declarations until their exact report formulations have been typechecked.  It
also keeps all seven conjectures/problems visibly open rather than replacing
them with premise-free placeholder theorems.
