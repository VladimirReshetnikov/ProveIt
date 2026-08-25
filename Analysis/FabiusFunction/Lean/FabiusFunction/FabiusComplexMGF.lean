import FabiusFunction.ProbabilityLaplaceMoments
import FabiusFunction.NegativeLaplaceVerticalLog
import Mathlib.Probability.Moments.ComplexMGF

/-!
# The Fabius generating function as a complex MGF

The probabilistic construction realizes the Fabius law as the distribution of a random weighted
sum in `[0,1]`.  This module identifies the entire generating function already used in the
project with Mathlib's complex moment-generating function of that distribution.  It follows that
all complex derivatives are tilted moments.  Their norms at an arbitrary complex parameter `z`
are bounded by the real tilted moments at scale `-z.re`; the vertical-line estimate needed for
the saddle Taylor remainder is exposed as a direct specialization.
-/

set_option autoImplicit false

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

namespace Fabius

open ProbabilityRepresentation

/-- The real MGF of the weighted-sum law is the Fabius exponential generating function. -/
theorem mgf_weightedSumDistribution_eq_generatingFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    mgf id weightedSumDistribution = generatingFunction F := by
  funext t
  have h := unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    F hF 0 (-t)
  rw [fabiusLaplaceMoment_zero] at h
  unfold unitLaplaceMoment at h
  unfold mgf
  rw [← weightedSumDistribution_restrict_Icc]
  simpa [id_eq] using h

/-- Every real exponential tilt of the compactly supported weighted-sum law is integrable. -/
lemma weightedSumDistribution_mem_integrableExpSet (t : ℝ) :
    t ∈ integrableExpSet id weightedSumDistribution := by
  unfold integrableExpSet
  rw [← weightedSumDistribution_restrict_Icc]
  exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (t * id x))).integrableOn_Icc

/-- The interval of definition of the weighted-sum MGF is all of `ℝ`. -/
lemma weightedSumDistribution_integrableExpSet :
    integrableExpSet id weightedSumDistribution = Set.univ := by
  ext t
  simp [weightedSumDistribution_mem_integrableExpSet]

/-- Exact identification of the probabilistic complex MGF with the project's entire generating
function. -/
theorem complexMGF_weightedSumDistribution_eq_complexGeneratingFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    complexMGF id weightedSumDistribution = complexGeneratingFunction F := by
  have hleft : AnalyticOnNhd ℂ (complexMGF id weightedSumDistribution) Set.univ := by
    simpa [weightedSumDistribution_integrableExpSet] using
      (analyticOnNhd_complexMGF (X := id) (μ := weightedSumDistribution))
  have hright : AnalyticOnNhd ℂ (complexGeneratingFunction F) Set.univ :=
    (differentiable_complexGeneratingFunction F hF).differentiableOn.analyticOnNhd isOpen_univ
  have hreal : ∃ᶠ (x : ℝ) in 𝓝[≠] 0,
      complexMGF id weightedSumDistribution x = complexGeneratingFunction F x := by
    apply Filter.Frequently.of_forall
    intro x
    rw [complexMGF_ofReal, mgf_weightedSumDistribution_eq_generatingFunction F hF]
    exact (complexGeneratingFunction_ofReal F x).symm
  have hcomplex : ∃ᶠ (z : ℂ) in 𝓝[≠] 0,
      complexMGF id weightedSumDistribution z = complexGeneratingFunction F z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => heq n⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · convert Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1 using 1 <;>
        simp [Function.comp_def]
    · simpa using hxs.2
  have heq : Set.EqOn (complexMGF id weightedSumDistribution)
      (complexGeneratingFunction F) Set.univ := by
    apply hleft.eqOn_of_preconnected_of_frequently_eq hright isPreconnected_univ
      (z₀ := (0 : ℂ)) (by simp)
    exact hcomplex
  funext z
  exact heq (Set.mem_univ z)

/-- Every complex derivative of the generating function is the corresponding tilted raw moment. -/
theorem iteratedDeriv_complexGeneratingFunction_eq_integral
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (complexGeneratingFunction F) z =
      ∫ x : ℝ, (x : ℂ) ^ n * Complex.exp (z * x) ∂weightedSumDistribution := by
  rw [← complexMGF_weightedSumDistribution_eq_complexGeneratingFunction F hF]
  have hz : z.re ∈ interior (integrableExpSet id weightedSumDistribution) := by
    simp [weightedSumDistribution_integrableExpSet]
  simpa [id_eq] using
    (iteratedDeriv_complexMGF (X := id) (μ := weightedSumDistribution) hz n)

/-- At an arbitrary complex parameter, the norm of the `n`th derivative is
bounded by the real tilted moment at the opposite real part. -/
theorem norm_iteratedDeriv_complexGeneratingFunction_le_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (z : ℂ) :
    ‖iteratedDeriv n (complexGeneratingFunction F) z‖ ≤
      fabiusLaplaceMoment F n (-z.re) := by
  rw [iteratedDeriv_complexGeneratingFunction_eq_integral F hF]
  rw [← unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    F hF n (-z.re)]
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ n * Complex.exp (z * x)
  let bound : ℝ → ℝ := fun x => Real.exp (-(-z.re) * x) * x ^ n
  have hboundInt : Integrable bound weightedSumDistribution := by
    rw [← weightedSumDistribution_restrict_Icc]
    exact (by fun_prop : Continuous bound).integrableOn_Icc
  have hnorm : ∀ᵐ x ∂weightedSumDistribution, ‖g x‖ ≤ bound x := by
    filter_upwards [ae_weightedSumDistribution_mem_Icc] with x hx
    dsimp [g, bound]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx.1, Complex.norm_exp]
    have hre : (z * (x : ℂ)).re = z.re * x := by simp
    rw [hre]
    have harg : - -z.re * x = z.re * x := by ring
    rw [harg]
    exact (mul_comm _ _).le
  have hle := norm_integral_le_of_norm_le hboundInt hnorm
  unfold unitLaplaceMoment
  rw [weightedSumDistribution_restrict_Icc]
  exact hle

/-- On a vertical negative-Laplace line, the norm of the `n`th complex derivative is bounded by
the corresponding real tilted moment. -/
theorem norm_iteratedDeriv_complexGeneratingFunction_neg_vertical_le
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (r θ : ℝ) :
    ‖iteratedDeriv n (complexGeneratingFunction F)
        (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))‖ ≤
      fabiusLaplaceMoment F n r := by
  have h := norm_iteratedDeriv_complexGeneratingFunction_le_fabiusLaplaceMoment
    F hF n (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))
  have hre : (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I))).re = -r := by
    norm_num
  rw [hre, neg_neg] at h
  exact h

end Fabius
