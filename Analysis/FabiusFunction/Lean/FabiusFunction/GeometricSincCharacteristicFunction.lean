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
product without imposing positivity on the geometric weights.  The finite
phase-bearing prefixes converge locally uniformly on the whole real line,
and hence uniformly on every compact frequency set.
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

/-- **Locally uniform phase-bearing characteristic-prefix limit.**  For every
real strict contraction `q`, the finite phase-collapsed sinc prefixes converge
locally uniformly on the real frequency line to the characteristic function
of the geometric-uniform law.  The theorem includes `q = 0` and negative `q`;
no positivity or support hypothesis is used. -/
theorem tendstoLocallyUniformly_prefix_sinc_charFun
    {q : ℝ} (hq : |q| < 1) :
    TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
          ∏ k ∈ Finset.range m,
            complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      (fun t : ℝ => charFun (geometricUniformDistribution q) t)
      Filter.atTop := by
  let z : ℝ → ℂ := fun t =>
    ((((1 - q) * t) / (2 * Real.pi) : ℝ) : ℂ)
  have hqComplex : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hq
  have hz : Continuous z := by
    dsimp [z]
    fun_prop
  have hproductCanonical : TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        ∏ k ∈ Finset.range m,
          complexSinc (Real.pi * ((q : ℂ) ^ k * z t)))
      (fun t : ℝ => geometricSincProduct (q : ℂ) (z t))
      Filter.atTop := by
    have h := hasProdLocallyUniformly_geometricSincProduct (q : ℂ) hqComplex
      |>.tendstoLocallyUniformly_finsetRange.comp z hz
    change TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        ∏ k ∈ Finset.range m,
          complexSinc (Real.pi * ((q : ℂ) ^ k * z t)))
      (fun t : ℝ => geometricSincProduct (q : ℂ) (z t))
      Filter.atTop at h
    exact h
  have hproduct : TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        ∏ k ∈ Finset.range m,
          complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      (fun t : ℝ => geometricSincProduct (q : ℂ) (z t))
      Filter.atTop := by
    refine hproductCanonical.congr ?_
    intro m t
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    dsimp [z]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hqPow : Filter.Tendsto (fun m : ℕ => q ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have hcoeff : Filter.Tendsto
      (fun m : ℕ => 2⁻¹ * (1 - q ^ m))
      Filter.atTop (nhds (2⁻¹ : ℝ)) := by
    convert (tendsto_const_nhds.sub hqPow).const_mul (2⁻¹ : ℝ) using 1
    all_goals ring_nf
  have hphase : TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I))
      (fun t : ℝ => cexp ((((2⁻¹ * t : ℝ) : ℂ) * I)))
      Filter.atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    let phaseFamily : ℝ → K → ℂ := fun a t =>
      cexp ((((a * (t : ℝ) : ℝ) : ℂ) * I))
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hphaseFamily : Continuous ↿phaseFamily := by
      dsimp [phaseFamily]
      fun_prop
    have hnear : TendstoUniformly phaseFamily (phaseFamily (2⁻¹ : ℝ))
        (nhds (2⁻¹ : ℝ)) :=
      Continuous.tendstoUniformly phaseFamily hphaseFamily (2⁻¹ : ℝ)
    have hseq : TendstoUniformly
        (fun m : ℕ => phaseFamily (2⁻¹ * (1 - q ^ m)))
        (phaseFamily (2⁻¹ : ℝ)) Filter.atTop := by
      intro u hu
      exact hcoeff.eventually (hnear u hu)
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    change TendstoUniformly
      (fun m : ℕ => fun t : K =>
        cexp (((2⁻¹ * ((1 - q ^ m) * (t : ℝ)) : ℝ) : ℂ) * I))
      (fun t : K => cexp ((((2⁻¹ * (t : ℝ) : ℝ) : ℂ) * I)))
      Filter.atTop
    simpa only [phaseFamily, mul_assoc] using hseq
  have hproductContinuous : Continuous
      (fun t : ℝ => geometricSincProduct (q : ℂ) (z t)) :=
    (geometricSincProduct_differentiable (q : ℂ) hqComplex).continuous.comp hz
  have hcombined : TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
          ∏ k ∈ Finset.range m,
            complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      (fun t : ℝ => cexp ((((2⁻¹ * t : ℝ) : ℂ) * I)) *
        geometricSincProduct (q : ℂ) (z t))
      Filter.atTop := by
    have h := hphase.mul₀ hproduct (by fun_prop) hproductContinuous
    change TendstoLocallyUniformly
      (fun m : ℕ => fun t : ℝ =>
        cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
          ∏ k ∈ Finset.range m,
            complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      (fun t : ℝ => cexp ((((2⁻¹ * t : ℝ) : ℂ) * I)) *
        geometricSincProduct (q : ℂ) (z t))
      Filter.atTop at h
    exact h
  refine hcombined.congr_right ?_
  intro t
  have ht : (2⁻¹ : ℝ) * t = t / 2 := by
    rw [div_eq_mul_inv, mul_comm]
  rw [ht]
  exact (charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct
    hq t).symm

/-- On every compact real frequency set, the phase-bearing geometric sinc
prefixes converge uniformly to the geometric-uniform characteristic function. -/
theorem tendstoUniformlyOn_prefix_sinc_charFun
    {q : ℝ} (hq : |q| < 1) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun m : ℕ => fun t : ℝ =>
        cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
          ∏ k ∈ Finset.range m,
            complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      (fun t : ℝ => charFun (geometricUniformDistribution q) t)
      Filter.atTop K :=
  (tendstoLocallyUniformly_iff_forall_isCompact.mp
    (tendstoLocallyUniformly_prefix_sinc_charFun hq)) K hK

end

end Fabius
