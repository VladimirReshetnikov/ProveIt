import FabiusFunction.GeometricReciprocalGamma
import FabiusFunction.GeometricSincFactorization

/-!
# The geometric sinc product as a characteristic function

This file identifies the phase-bearing characteristic function of the
geometric-uniform random series with the analytic `geometricSincProduct`.
For every real ratio `|q| < 1`, including `q = 0` and negative ratios,

`φ_q(t) = exp(i t / 2) · S_q((1-q)t/(2π))`,

where `S_q(z) = ∏' k, sinc(π q^k z)`.  This closes the exact bridge between
the probability-side prefix limit and the reciprocal-Gamma-side infinite
product without imposing positivity on the geometric weights.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory
open scoped BigOperators Topology

namespace Fabius

open ProbabilityRepresentation

noncomputable section

/-- **Characteristic-function/geometric-sinc bridge.**  For every real
strict contraction `q`, the characteristic function of the normalized
geometric-uniform law is the centered phase times the rescaled geometric
sinc product.  The result includes `q = 0` and negative `q`. -/
theorem charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    charFun (geometricUniformDistribution q) t =
      cexp ((((t / 2 : ℝ) : ℂ) * I)) *
        geometricSincProduct (q : ℂ)
          ((((1 - q) * t) / (2 * Real.pi) : ℝ) : ℂ) := by
  let z : ℝ := ((1 - q) * t) / (2 * Real.pi)
  have hqComplex : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hq
  have hfactor : (fun k : ℕ ↦
      complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ)) =
      fun k : ℕ ↦ complexSinc
        (Real.pi * ((q : ℂ) ^ k * (z : ℂ))) := by
    funext k
    congr 1
    dsimp [z]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hproduct : Filter.Tendsto (fun m : ℕ ↦
      ∏ k ∈ Finset.range m,
        complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      Filter.atTop
      (nhds (geometricSincProduct (q : ℂ) (z : ℂ))) := by
    rw [hfactor]
    exact (hasProd_geometricSincProduct (q : ℂ) (z : ℂ) hqComplex).tendsto_prod_nat
  have hqPow : Filter.Tendsto (fun m : ℕ ↦ q ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have hphaseReal : Filter.Tendsto
      (fun m : ℕ ↦ 2⁻¹ * ((1 - q ^ m) * t))
      Filter.atTop (nhds (t / 2)) := by
    convert ((tendsto_const_nhds.sub hqPow).mul_const t).const_mul (2⁻¹ : ℝ) using 1
    all_goals ring_nf
  have hphaseComplex : Filter.Tendsto
      (fun m : ℕ ↦ cexp
        (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I))
      Filter.atTop (nhds (cexp ((((t / 2 : ℝ) : ℂ) * I)))) := by
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hphaseReal).mul_const I)
  have hlimit := hphaseComplex.mul hproduct
  rw [show ((((1 - q) * t) / (2 * Real.pi) : ℝ) : ℂ) = (z : ℂ) by rfl]
  exact tendsto_nhds_unique (tendsto_prefix_sinc_charFun hq t) hlimit

/-- **Characteristic-function/reciprocal-Gamma bridge.**  The geometric sinc
product in the characteristic-function formula is equivalently the product
of the geometric reciprocal-Gamma functions at opposite arguments. -/
theorem charFun_geometricUniformDistribution_eq_phase_mul_geometricReciprocalGamma
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    charFun (geometricUniformDistribution q) t =
      cexp ((((t / 2 : ℝ) : ℂ) * I)) *
        (geometricReciprocalGamma (q : ℂ)
            ((((1 - q) * t) / (2 * Real.pi) : ℝ) : ℂ) *
          geometricReciprocalGamma (q : ℂ)
            (-((((1 - q) * t) / (2 * Real.pi) : ℝ) : ℂ))) := by
  have hqComplex : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hq
  rw [geometricReciprocalGamma_mul_neg _ _ hqComplex]
  exact charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct hq t

end

end Fabius
