import FabiusFunction.CauchySurvival

/-!
# The full higher-power Cauchy--Stieltjes families

The last unexported piece of the transform layer's statusbox: the
integration-by-parts formulas for every resolvent power.  For `p ≥ 1`,
a finite measure almost surely supported on `[a,b]`, and `z` off the
interval:

* `intervalIntegral_pow_inv_sub` — the closed kernel primitive
  `∫_a^b p·(z-t)^{-(p+1)} dt = (z-b)^{-p} - (z-a)^{-p}`;
* `integral_pow_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic`
  — the CDF family
  `∫ (z-x)^{-p} dμ = μ(ℝ)·(z-b)^{-p} - ∫_a^b μ((-∞,t])·p·(z-t)^{-(p+1)} dt`;
* `integral_pow_inv_sub_eq_mass_smul_add_intervalIntegral_measureReal_Ioi`
  — the survival family
  `∫ (z-x)^{-p} dμ = μ(ℝ)·(z-a)^{-p} + ∫_a^b μ((t,∞))·p·(z-t)^{-(p+1)} dt`.

`p = 1` recovers the first-power formulas of `CauchyCDF.lean` and
`CauchySurvival.lean`; inverse powers are written as powers of the
inverse, `(z-t)^{-p} = ((z-t)⁻¹)^p`.
-/

set_option autoImplicit false

open MeasureTheory Set Complex

namespace Fabius

/-- The higher-power derivative step:
`d/dt ((z-t)⁻¹)^p = p·((z-t)⁻¹)^(p+1)` for `p ≥ 1` and `z ≠ t`. -/
theorem hasDerivAt_pow_inv_sub {z : ℂ} {t : ℝ} (hzt : z - (t : ℂ) ≠ 0)
    {p : ℕ} (hp : 1 ≤ p) :
    HasDerivAt (fun s : ℝ => ((z - (s : ℂ))⁻¹) ^ p)
      ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)) t := by
  have hsub : HasDerivAt (fun w : ℂ => z - w) (-1) (t : ℂ) := by
    simpa only [id_eq] using (hasDerivAt_id ((t : ℝ) : ℂ)).const_sub z
  have hinv := hsub.inv hzt
  have hpow := hinv.pow p
  have hcomp := hpow.comp_ofReal
  have hval : (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p - 1) *
      (- (-1) / (z - (t : ℂ)) ^ 2) =
      (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1) := by
    rw [neg_neg, one_div, ← inv_pow, mul_assoc, ← pow_add,
      show p - 1 + 2 = p + 1 from by omega]
  rw [← hval]
  exact hcomp

/-- The closed higher-power kernel primitive:
`∫_a^b p·(z-t)^{-(p+1)} dt = (z-b)^{-p} - (z-a)^{-p}`. -/
theorem intervalIntegral_pow_inv_sub {a b : ℝ} (hab : a ≤ b) {z : ℂ}
    (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) {p : ℕ} (hp : 1 ≤ p) :
    ∫ t in a..b, (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1) =
      ((z - (b : ℂ))⁻¹) ^ p - ((z - (a : ℂ))⁻¹) ^ p := by
  have hne : ∀ t ∈ Icc a b, z - (t : ℂ) ≠ 0 := by
    intro t ht h0
    exact hz ⟨t, ht, ((sub_eq_zero.mp h0).symm : (algebraMap ℝ ℂ) t = z)⟩
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s : ℝ => ((z - (s : ℂ))⁻¹) ^ p)
        ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_pow_inv_sub (hne t ht) hp
  have hint : IntervalIntegrable
      (fun t : ℝ => (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.mul (((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow (p + 1))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- **The higher-power CDF family**: for `p ≥ 1`,
`∫ (z-x)^{-p} dμ = μ(ℝ)·(z-b)^{-p} - ∫_a^b μ((-∞,t])·p·(z-t)^{-(p+1)} dt`. -/
theorem integral_pow_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {z : ℂ}
    (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : ℝ, ((z - (x : ℂ))⁻¹) ^ p ∂μ) =
      μ.real univ • ((z - (b : ℂ))⁻¹) ^ p -
        ∫ t in a..b, μ.real (Iic t) •
          ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)) := by
  have hne : ∀ t ∈ Icc a b, z - (t : ℂ) ≠ 0 := by
    intro t ht h0
    exact hz ⟨t, ht, ((sub_eq_zero.mp h0).symm : (algebraMap ℝ ℂ) t = z)⟩
  set r : ℝ → ℂ := fun t => ((z - (t : ℂ))⁻¹) ^ p with hrdef
  set k : ℝ → ℂ := fun t => (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)
    with hkdef
  have hrcont : ContinuousOn r (Icc a b) :=
    ((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow p
  have hkcont : ContinuousOn k (Icc a b) :=
    continuousOn_const.mul (((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow (p + 1))
  have hk : IntervalIntegrable k volume a b :=
    hkcont.intervalIntegrable_of_Icc hab
  have hprimitive : ∀ x ∈ Icc a b, (∫ t in x..b, k t) = r b - r x := by
    intro x hx
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hx.2] at ht
      exact hasDerivAt_pow_inv_sub (hne t ⟨hx.1.trans ht.1, ht.2⟩) hp
    · exact (hkcont.mono
        (Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable_of_Icc hx.2
  have hrestrict : μ.restrict (Icc a b) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hrμ : Integrable r μ := by
    rw [← hrestrict]
    exact hrcont.integrableOn_Icc
  have hlayer :=
    intervalIntegral_cdf_smul_eq_integral_of_ae_mem_Icc μ hab hμ k hk
  have hinner : (∫ x : ℝ, (∫ t in x..b, k t) ∂μ) =
      μ.real univ • r b - ∫ x : ℝ, r x ∂μ := by
    calc (∫ x : ℝ, (∫ t in x..b, k t) ∂μ)
        = ∫ x : ℝ, (r b - r x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hμ] with x hx
          exact hprimitive x hx
      _ = (∫ _ : ℝ, r b ∂μ) - ∫ x : ℝ, r x ∂μ := by
          rw [integral_sub (integrable_const _) hrμ]
      _ = μ.real univ • r b - ∫ x : ℝ, r x ∂μ := by
          rw [integral_const]
  change (∫ x : ℝ, r x ∂μ) =
    μ.real univ • r b - ∫ t in a..b, μ.real (Iic t) • k t
  rw [hlayer, hinner]
  abel

/-- **The higher-power survival family**: for `p ≥ 1`,
`∫ (z-x)^{-p} dμ = μ(ℝ)·(z-a)^{-p} + ∫_a^b μ((t,∞))·p·(z-t)^{-(p+1)} dt`. -/
theorem integral_pow_inv_sub_eq_mass_smul_add_intervalIntegral_measureReal_Ioi
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {z : ℂ}
    (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : ℝ, ((z - (x : ℂ))⁻¹) ^ p ∂μ) =
      μ.real univ • ((z - (a : ℂ))⁻¹) ^ p +
        ∫ t in a..b, μ.real (Ioi t) •
          ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)) := by
  have hne : ∀ t ∈ Icc a b, z - (t : ℂ) ≠ 0 := by
    intro t ht h0
    exact hz ⟨t, ht, ((sub_eq_zero.mp h0).symm : (algebraMap ℝ ℂ) t = z)⟩
  have hkcont : ContinuousOn
      (fun t : ℝ => (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1))
      (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact continuousOn_const.mul (((continuous_const.sub
      Complex.continuous_ofReal).continuousOn.inv₀ hne).pow (p + 1))
  have hk_int : IntervalIntegrable
      (fun t : ℝ => (p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1))
      volume a b :=
    hkcont.intervalIntegrable
  have hIoi_anti : Antitone (fun t : ℝ => μ.real (Ioi t)) := by
    intro s t hst
    exact measureReal_mono (Ioi_subset_Ioi hst)
  have hIoi_int : IntervalIntegrable
      (fun t : ℝ => μ.real (Ioi t) •
        ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1))) volume a b :=
    hIoi_anti.intervalIntegrable.smul_continuousOn hkcont
  have hconst_int : IntervalIntegrable
      (fun t : ℝ => μ.real univ •
        ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1))) volume a b :=
    hk_int.smul (μ.real univ)
  have hsplit : ∀ t : ℝ,
      μ.real (Iic t) = μ.real univ - μ.real (Ioi t) := by
    intro t
    have hc : μ.real (Iic t) + μ.real (Ioi t) = μ.real univ := by
      rw [← measureReal_union (Iic_disjoint_Ioi le_rfl)
        measurableSet_Ioi, Iic_union_Ioi]
    linarith
  rw [integral_pow_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic
    μ hab hμ hz hp]
  have hIic_eq : (fun t : ℝ => μ.real (Iic t) •
      ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1))) =
      fun t : ℝ => μ.real univ •
        ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)) -
        μ.real (Ioi t) • ((p : ℂ) * ((z - (t : ℂ))⁻¹) ^ (p + 1)) := by
    funext t
    rw [hsplit t, sub_smul]
  rw [hIic_eq, intervalIntegral.integral_sub hconst_int hIoi_int,
    intervalIntegral.integral_smul,
    intervalIntegral_pow_inv_sub hab hz hp]
  module

end Fabius
