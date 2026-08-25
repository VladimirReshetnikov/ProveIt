import FabiusFunction.OriginalUniqueness
import FabiusFunction.StepApproximationLimit
import FabiusFunction.ProbabilityRepresentation
import FabiusFunction.WeakConvergence
import FabiusFunction.OriginalPaperSupplement
import FabiusFunction.PoissonSummation

/-!
# *An infinitely differentiable function with compact support*

This is the public import for Juan Arias de Reyna's
*An infinitely differentiable function with compact support: Definition and
Properties* (arXiv:1702.05442).

Every theorem, lemma, corollary, and prose proposition in the paper has a
proved Lean counterpart:

* Theorem 1: `Fabius.IsOriginalFabius`,
  `Fabius.IsFabius.isOriginalFabius_rvachevUp`,
  `Fabius.isOriginalFabius_iff_eq_canonical`,
  `Fabius.isOriginalFabius_iff_existsUnique_isFabius`, and
  `Fabius.existsUnique_originalFabius`;
* Lemma 1: `Fabius.finiteConvolutionProbability_tendsto` and its real and
  complex bounded-continuous test-function forms;
* Theorem 2: `Fabius.stepApproximant_tendsto_rvachevUp`;
* Theorem 3 and its prose probability proposition:
  `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSum_probability`,
  `Fabius.ProbabilityRepresentation.independent_uniform_coordinates`, and
  `Fabius.ProbabilityRepresentation.coordinate_has_uniform_law`;
* Theorem 4: `Fabius.original_theorem_four_a`,
  `Fabius.original_theorem_four_b`, and `Fabius.original_theorem_four_c`;
* the unnumbered non-analyticity corollary: `Fabius.rvachev_not_analyticAt`;
* Theorem 5: `Fabius.rvachev_poisson_summation`;
* Theorem 6: `Fabius.original_theorem_six`;
* Theorem 7: `Fabius.original_theorem_seven_global`.

The Theorem 3 declaration in that list deliberately preserves the paper's
source-facing domain `x ∈ [-1,0]` and event description.  The probability
construction also exposes stronger corollaries valid for every `x : ℝ`:

* `Fabius.ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal` and
  `Fabius.ProbabilityRepresentation.fabiusReal_eq_weightedSum_probability`
  identify the bounded Fabius function with the random-series CDF globally on
  its real domain;
* `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSumCDF` and
  `Fabius.ProbabilityRepresentation.rvachevUp_eq_weightedSum_probability_global`
  give `up(x) = P[X ≤ 1 - |x|]` for all real `x`.

Here the suffix `_global` means “no restriction on the real input.”  It does
not mean the signed extension `Fabius.extendedFabius` or its canonical form
`Fabius.globalFabius`; the probability identities describe the bounded CDF
and its folded compactly supported bump.

The source contains several typographical or endpoint defects.  The Lean
statements use the mathematically valid forms: equation (12) is a finite
convolution, Theorem 2 uses half-weighted cell endpoints, equation (25)
retains its missing `t`, equation (26) assumes a positive natural number,
and equation (32) is normalized consistently.  These corrections are
explained next to the relevant definitions and theorems.
-/
