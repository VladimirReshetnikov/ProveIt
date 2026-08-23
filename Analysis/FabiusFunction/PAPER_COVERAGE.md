# Fabius paper coverage

This file maps the named mathematical results in the two source papers to
their proved Lean declarations.  All names below are available from the
public import `FabiusFunction`.

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
