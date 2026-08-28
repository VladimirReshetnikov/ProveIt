import FabiusFunction.CauchyCDF
import FabiusFunction.LaplaceTransform

/-!
# Survival companions of the Cauchy--Stieltjes integration by parts

The integration volume's transform-layer statusbox records that the
CDF-side integration-by-parts formulas are formal but "their survival
companions … are not exported by this module".  This module exports
them.

* `intervalIntegral_inv_sub_sq` — the closed kernel primitive
  `∫_a^b (z-t)⁻² dt = (z-b)⁻¹ - (z-a)⁻¹`, for `z` off the interval;
* `integral_inv_sub_eq_mass_smul_add_intervalIntegral_measureReal_Ioi`
  — **the survival integration by parts** for any finite measure
  almost surely supported on `[a,b]`:
  `∫ (z-x)⁻¹ dμ = μ(ℝ)·(z-a)⁻¹ + ∫_a^b μ((t,∞))·(z-t)⁻² dt`.
  Mass sits at the *lower* endpoint and the survival function replaces
  the CDF; atoms are retained by the open upper ray.
* `fabiusStieltjesTransform_eq_inv_add_intervalIntegral_rvachevUp` —
  the Fabius instance: on the slit domain,
  `S_unit(z) = z⁻¹ + ∫₀¹ up(t)·(z-t)⁻² dt` — the Stieltjes transform
  of the unit-interval law through the up-density directly.
-/

set_option autoImplicit false

open MeasureTheory Set Complex

namespace Fabius

/-- The closed kernel primitive:
`∫_a^b (z-t)⁻² dt = (z-b)⁻¹ - (z-a)⁻¹` for `z` off the interval. -/
theorem intervalIntegral_inv_sub_sq {a b : ℝ} (hab : a ≤ b) {z : ℂ}
    (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) :
    ∫ t in a..b, ((z - (t : ℂ))⁻¹ ^ 2) =
      (z - (b : ℂ))⁻¹ - (z - (a : ℂ))⁻¹ := by
  have hne : ∀ t ∈ Icc a b, z - (t : ℂ) ≠ 0 := by
    intro t ht h0
    exact hz ⟨t, ht, ((sub_eq_zero.mp h0).symm : (algebraMap ℝ ℂ) t = z)⟩
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s : ℝ => (z - (s : ℂ))⁻¹)
        ((z - (t : ℂ))⁻¹ ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hbase : HasDerivAt (fun s : ℝ => z - (s : ℂ)) (-1) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_sub z
    have hinv := hbase.inv (hne t ht)
    have hval : - (-1 : ℂ) / (z - (t : ℝ)) ^ 2 =
        (z - ((t : ℝ) : ℂ))⁻¹ ^ 2 := by
      rw [neg_neg, one_div, inv_pow]
    rw [← hval]
    exact hinv
  have hint : IntervalIntegrable
      (fun t : ℝ => (z - (t : ℂ))⁻¹ ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact ((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow 2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- **The survival integration by parts**: for a finite measure almost
surely supported on `[a,b]` and `z` off the interval,
`∫ (z-x)⁻¹ dμ = μ(ℝ)·(z-a)⁻¹ + ∫_a^b μ((t,∞))·(z-t)⁻² dt`. -/
theorem integral_inv_sub_eq_mass_smul_add_intervalIntegral_measureReal_Ioi
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {z : ℂ}
    (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) :
    (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ) =
      μ.real univ • (z - (a : ℂ))⁻¹ +
        ∫ t in a..b, μ.real (Ioi t) • ((z - (t : ℂ))⁻¹ ^ 2) := by
  have hne : ∀ t ∈ Icc a b, z - (t : ℂ) ≠ 0 := by
    intro t ht h0
    exact hz ⟨t, ht, ((sub_eq_zero.mp h0).symm : (algebraMap ℝ ℂ) t = z)⟩
  have hkcont : ContinuousOn (fun t : ℝ => (z - (t : ℂ))⁻¹ ^ 2)
      (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact ((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow 2
  have hk_int : IntervalIntegrable
      (fun t : ℝ => (z - (t : ℂ))⁻¹ ^ 2) volume a b :=
    hkcont.intervalIntegrable
  have hIoi_anti : Antitone (fun t : ℝ => μ.real (Ioi t)) := by
    intro s t hst
    exact measureReal_mono (Ioi_subset_Ioi hst)
  have hIoi_int : IntervalIntegrable
      (fun t : ℝ => μ.real (Ioi t) • ((z - (t : ℂ))⁻¹ ^ 2))
      volume a b :=
    hIoi_anti.intervalIntegrable.smul_continuousOn hkcont
  have hsplit : ∀ t : ℝ,
      μ.real (Iic t) = μ.real univ - μ.real (Ioi t) := by
    intro t
    have hc : μ.real (Iic t) + μ.real (Ioi t) = μ.real univ := by
      rw [← measureReal_union (Iic_disjoint_Ioi le_rfl)
        measurableSet_Ioi, Iic_union_Ioi]
    linarith
  rw [integral_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic
    μ hab hμ hz]
  have hIic_eq : (fun t : ℝ =>
      μ.real (Iic t) • ((z - (t : ℂ))⁻¹ ^ 2)) =
      fun t : ℝ => μ.real univ • ((z - (t : ℂ))⁻¹ ^ 2) -
        μ.real (Ioi t) • ((z - (t : ℂ))⁻¹ ^ 2) := by
    funext t
    rw [hsplit t, sub_smul]
  have hconst_int : IntervalIntegrable
      (fun t : ℝ => μ.real univ • ((z - (t : ℂ))⁻¹ ^ 2))
      volume a b :=
    hk_int.smul (μ.real univ)
  rw [hIic_eq, intervalIntegral.integral_sub hconst_int hIoi_int,
    intervalIntegral.integral_smul,
    intervalIntegral_inv_sub_sq hab hz]
  module

/-- **The survival Stieltjes formula for the Fabius law**: on the slit
domain, `S_unit(z) = z⁻¹ + ∫₀¹ up(t)·(z-t)⁻² dt` — the transform of
the unit-interval law through the up-density itself. -/
theorem fabiusStieltjesTransform_eq_inv_add_intervalIntegral_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ}
    (hz : z ∈ fabiusStieltjesDomain) :
    fabiusStieltjesTransform z =
      z⁻¹ + ∫ t in (0 : ℝ)..1,
        rvachevUp F t • ((z - (t : ℂ))⁻¹ ^ 2) := by
  have hz' : z ∉ algebraMap ℝ ℂ '' Icc (0 : ℝ) 1 := by
    simpa only [fabiusStieltjesDomain, mem_compl_iff] using hz
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, z - (t : ℂ) ≠ 0 := by
    intro t ht h0
    exact hz' ⟨t, ht, ((sub_eq_zero.mp h0).symm : (algebraMap ℝ ℂ) t = z)⟩
  have hkcont : ContinuousOn (fun t : ℝ => (z - (t : ℂ))⁻¹ ^ 2)
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow 2
  have hk_int : IntervalIntegrable
      (fun t : ℝ => (z - (t : ℂ))⁻¹ ^ 2) volume 0 1 :=
    hkcont.intervalIntegrable
  have hup_int : IntervalIntegrable
      (fun t : ℝ => rvachevUp F t • ((z - (t : ℂ))⁻¹ ^ 2))
      volume 0 1 :=
    ((rvachev_contDiff F hF).continuous.intervalIntegrable
      (μ := volume) 0 1).smul_continuousOn hkcont
  rw [fabiusStieltjesTransform_eq_inv_sub_one_sub_intervalIntegral_fabiusReal
    F hF hz]
  have hF_eq : ∀ t ∈ uIcc (0 : ℝ) 1,
      fabiusReal F t • ((z - (t : ℂ))⁻¹ ^ 2) =
        (z - (t : ℂ))⁻¹ ^ 2 -
          rvachevUp F t • ((z - (t : ℂ))⁻¹ ^ 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hup := rvachevUp_eq_one_sub_fabiusReal_of_nonneg F hF ht.1
    have hFt : fabiusReal F t = 1 - rvachevUp F t := by linarith
    rw [hFt, sub_smul, one_smul]
  rw [intervalIntegral.integral_congr hF_eq,
    intervalIntegral.integral_sub hk_int hup_int,
    intervalIntegral_inv_sub_sq (by norm_num : (0 : ℝ) ≤ 1) hz']
  have hz0 : z - ((0 : ℝ) : ℂ) = z := by norm_num
  have hz1 : z - ((1 : ℝ) : ℂ) = z - 1 := by norm_num
  rw [hz0, hz1]
  abel

end Fabius
