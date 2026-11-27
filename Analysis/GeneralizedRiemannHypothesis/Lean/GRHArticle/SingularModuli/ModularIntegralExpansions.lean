import GRHArticle.SingularModuli.ModularInvariant
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Integral expansions of the discriminant and modular invariant

The quadratic and cubic contributions to `(E₄³-E₆²)/1728` are visibly
integral. The linear contribution is integral by the congruence
`5*d^3+7*d^5 ≡ 0 (mod 12)` for every divisor `d`.
-/

namespace GRHArticle.SingularModuli

open Filter Function UpperHalfPlane ModularForm CongruenceSubgroup PowerSeries
open scoped PowerSeries MatrixGroups Topology

local notation "intSeriesMap" => PowerSeries.map (Int.castRingHom ℂ)
local notation "σ" => ArithmeticFunction.sigma

private theorem twelve_dvd_sigma_combo (n : ℕ) :
    12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  have hres (x : ZMod 12) : 5 * x ^ 3 + 7 * x ^ 5 = 0 := by
    fin_cases x <;> decide
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_sum,
    Nat.cast_pow, Nat.cast_ofNat, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun d _ ↦ hres (d : ZMod 12)

/-- The integer power series of divisor sums of (k)-th powers. -/
def divisorPowerSeries (k : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ k n : ℤ)

private def discriminantLinearSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)

/-- The integral Fourier series of the modular discriminant. -/
noncomputable def integralDiscriminantExpansion : ℤ⟦X⟧ :=
  discriminantLinearSeries + 100 * divisorPowerSeries 3 ^ 2 +
    8000 * divisorPowerSeries 3 ^ 3 - 147 * divisorPowerSeries 5 ^ 2

private theorem linearSeries_eq : (12 : ℂ) • intSeriesMap discriminantLinearSeries =
    (5 : ℂ) • intSeriesMap (divisorPowerSeries 3) +
      (7 : ℂ) • intSeriesMap (divisorPowerSeries 5) := by
  ext n
  have h := Nat.mul_div_cancel' (twelve_dvd_sigma_combo n)
  simp only [coeff_smul, map_add, coeff_map, discriminantLinearSeries, divisorPowerSeries,
    coeff_mk, Int.coe_castRingHom, Int.cast_natCast, smul_eq_mul]
  exact_mod_cast h

private theorem qExpansion_E₄_integral :
    qExpansion 1 E₄ = 1 + 240 * intSeriesMap (divisorPowerSeries 3) := by
  ext n
  have h := EisensteinSeries.E_qExpansion_coeff (by decide : 3 ≤ 4) (by decide : Even 4) n
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 4 ≠ 1), bernoulli'_four] at h
  have h240 : (240 : ℂ⟦X⟧) = C (240 : ℂ) := (map_natCast (C : ℂ →+* ℂ⟦X⟧) 240).symm
  rw [h240, map_add, coeff_C_mul, coeff_one]
  rw [h]
  simp only [coeff_map, divisorPowerSeries, coeff_mk, Int.coe_castRingHom, Int.cast_natCast]
  split_ifs with hn <;> norm_num [hn]

private theorem bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

private theorem qExpansion_E₆_integral :
    qExpansion 1 E₆ = 1 - 504 * intSeriesMap (divisorPowerSeries 5) := by
  ext n
  have h := EisensteinSeries.E_qExpansion_coeff (by decide : 3 ≤ 6) (by decide : Even 6) n
  rw [bernoulli_six] at h
  have h504 : (504 : ℂ⟦X⟧) = C (504 : ℂ) := (map_natCast (C : ℂ →+* ℂ⟦X⟧) 504).symm
  rw [h504, map_sub, coeff_C_mul, coeff_one]
  rw [h]
  simp only [coeff_map, divisorPowerSeries, coeff_mk, Int.coe_castRingHom, Int.cast_natCast]
  split_ifs with hn <;> norm_num [hn]

private theorem qExpansion_discriminant_mul :
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      (qExpansion 1 E₄) ^ 3 - (qExpansion 1 E₆) ^ 2 := by
  have h : (⇑((1728 : ℂ) • CuspForm.discriminant) : ℍ → ℂ) =
      (⇑(E₄.pow 3) : ℍ → ℂ) - (⇑(E₆.pow 2) : ℍ → ℂ) := by
    funext z
    change (1728 : ℂ) * ModularForm.discriminant z = E₄ z ^ 3 - E₆ z ^ 2
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have h' := congrArg (qExpansion 1) h
  rw [CuspForm.IsGLPos.coe_smul] at h'
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ)
    CuspForm.discriminant] at h'
  simpa only [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, CuspForm.coe_discriminant] using h'

/-- Casting the coefficients of the integer series gives the actual analytic
Fourier expansion of the discriminant. -/
theorem map_integralDiscriminantExpansion :
    intSeriesMap integralDiscriminantExpansion = qExpansion 1 ModularForm.discriminant := by
  have h := qExpansion_discriminant_mul
  rw [qExpansion_E₄_integral, qExpansion_E₆_integral] at h
  have hl := linearSeries_eq
  simp only [smul_eq_C_mul, map_ofNat] at h hl
  have he : (1728 : ℂ⟦X⟧) * intSeriesMap integralDiscriminantExpansion =
       (1728 : ℂ⟦X⟧) * qExpansion 1 ModularForm.discriminant := by
    rw [h]
    simp only [integralDiscriminantExpansion, map_add, map_sub, map_mul, map_ofNat, map_pow]
    linear_combination 144 * hl
  refine mul_left_cancel₀ ?_ he
  intro hz
  have hzero := congrArg (constantCoeff (R := ℂ)) hz
  norm_num [map_ofNat, map_zero] at hzero

/-- The discriminant's integral series after removing the initial `q`. -/
noncomputable def integralNormalizedDiscriminantExpansion : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ integralDiscriminantExpansion.coeff (n + 1)

theorem constantCoeff_integralNormalizedDiscriminantExpansion :
    constantCoeff integralNormalizedDiscriminantExpansion = 1 := by
  have h := congrArg (fun f : ℂ⟦X⟧ ↦ f.coeff 1) map_integralDiscriminantExpansion
  rw [coeff_map, discriminant_qExpansion_coeff_one] at h
  change (integralDiscriminantExpansion.coeff 1 : ℂ) = 1 at h
  rw [← coeff_zero_eq_constantCoeff_apply, integralNormalizedDiscriminantExpansion, coeff_mk]
  exact_mod_cast h

/-- The integer series for `q*j`, with the initial pole of `j` removed. -/
noncomputable def integralNormalizedJExpansion : ℤ⟦X⟧ :=
  (1 + 240 * divisorPowerSeries 3) ^ 3 *
    invOfUnit integralNormalizedDiscriminantExpansion 1

theorem constantCoeff_integralNormalizedJExpansion :
    constantCoeff integralNormalizedJExpansion = 1 := by
  have hσ : constantCoeff (divisorPowerSeries 3) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [divisorPowerSeries]
  simp [integralNormalizedJExpansion, hσ]

private noncomputable def taylorAtZero (f : ℂ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n ↦ (↑n.factorial)⁻¹ * iteratedDeriv n f 0

private theorem taylorAtZero_mul {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (f * g) = taylorAtZero f * taylorAtZero g := by
  ext n
  simp only [taylorAtZero, coeff_mk, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    Finset.mul_sum, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

private theorem taylorAtZero_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorAtZero (f ^ n) = (taylorAtZero f) ^ n := by
  induction n with
  | zero =>
    ext i
    by_cases hi : i = 0
    · subst i
      simp [taylorAtZero]
    · simp only [pow_zero, taylorAtZero, coeff_mk, coeff_one, if_neg hi]
      change (↑i.factorial : ℂ)⁻¹ * iteratedDeriv i (fun _ : ℂ ↦ 1) 0 = 0
      simp [iteratedDeriv_const, hi]
  | succ n h =>
    rw [pow_succ, pow_succ, taylorAtZero_mul (hf.pow n) hf, h]

private theorem taylorAtZero_id : taylorAtZero (id : ℂ → ℂ) = X := by
  ext n
  rcases n with (_ | _ | n) <;> simp [taylorAtZero, iteratedDeriv_id, coeff_X]

local notation "D₀" => cuspFunction 1 ModularForm.discriminant
local notation "D₁" => dslope D₀ 0
local notation "E₀" => cuspFunction 1 E₄

private theorem D₀_zero : D₀ 0 = 0 := by
  rw [← CuspForm.coe_discriminant]
  exact CuspFormClass.cuspFunction_apply_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

private theorem D₁_analytic : AnalyticAt ℂ D₁ 0 := by
  have h := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  rw [CuspForm.coe_discriminant] at h
  obtain ⟨p, hp⟩ := h
  exact hp.has_fpower_series_dslope_fslope.analyticAt

private theorem D₁_one : D₁ 0 = 1 := by
  rw [dslope_same]
  simpa [qExpansion_coeff] using discriminant_qExpansion_coeff_one

private theorem taylorAtZero_D₁ :
    taylorAtZero D₁ = intSeriesMap integralNormalizedDiscriminantExpansion := by
  have h : (id : ℂ → ℂ) * D₁ = D₀ := by
    funext q
    by_cases hq : q = 0
    · simp [hq, D₀_zero]
    · simp only [Pi.mul_apply, id_eq, dslope_of_ne D₀ hq, slope_def_field, D₀_zero, sub_zero]
      exact mul_div_cancel₀ _ hq
  have ht := taylorAtZero_mul (f := id) analyticAt_id D₁_analytic
  rw [taylorAtZero_id, h] at ht
  ext n
  have hc := congrArg (fun f : ℂ⟦X⟧ ↦ f.coeff (n + 1)) ht
  rw [coeff_succ_X_mul] at hc
  rw [coeff_map, integralNormalizedDiscriminantExpansion, coeff_mk]
  rw [← coeff_map, map_integralDiscriminantExpansion]
  exact hc.symm

private noncomputable def normalizedJCusp : ℂ → ℂ := E₀ ^ 3 / D₁

private theorem normalizedJCusp_analytic : AnalyticAt ℂ normalizedJCusp 0 :=
  ((ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos
    one_mem_strictPeriods_SL).pow 3).div D₁_analytic (D₁_one.trans_ne one_ne_zero)

private theorem taylorAtZero_normalizedJCusp :
    taylorAtZero normalizedJCusp = intSeriesMap integralNormalizedJExpansion := by
  have hE : AnalyticAt ℂ E₀ 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
  have hEq : normalizedJCusp * D₁ =ᶠ[𝓝 0] E₀ ^ 3 := by
    filter_upwards [D₁_analytic.continuousAt.eventually_ne (D₁_one.trans_ne one_ne_zero)]
      with z hz
    simp only [normalizedJCusp, Pi.mul_apply, Pi.div_apply]
    exact div_mul_cancel₀ _ hz
  have hT : taylorAtZero (normalizedJCusp * D₁) = taylorAtZero (E₀ ^ 3) := by
    ext n
    simp only [taylorAtZero, coeff_mk, hEq.iteratedDeriv_eq]
  rw [taylorAtZero_mul normalizedJCusp_analytic D₁_analytic, taylorAtZero_pow hE,
    taylorAtZero_D₁] at hT
  change _ = (qExpansion 1 E₄) ^ 3 at hT
  rw [qExpansion_E₄_integral] at hT
  have hInv :
      intSeriesMap integralNormalizedDiscriminantExpansion *
        intSeriesMap (invOfUnit integralNormalizedDiscriminantExpansion 1) = 1 := by
    rw [← map_mul, mul_invOfUnit, map_one]
    exact constantCoeff_integralNormalizedDiscriminantExpansion
  calc
    taylorAtZero normalizedJCusp =
        (taylorAtZero normalizedJCusp * intSeriesMap integralNormalizedDiscriminantExpansion) *
          intSeriesMap (invOfUnit integralNormalizedDiscriminantExpansion 1) := by
      rw [mul_assoc, hInv, mul_one]
    _ = intSeriesMap integralNormalizedJExpansion := by
      rw [hT, integralNormalizedJExpansion, map_mul, map_pow, map_add, map_mul, map_one, map_ofNat]

private theorem normalizedJCusp_apply (z : ℍ) :
    normalizedJCusp (Periodic.qParam 1 z) = Periodic.qParam 1 z * modularInvariant z := by
  have hq := Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  have hE := SlashInvariantFormClass.eq_cuspFunction E₄ z one_mem_strictPeriods_SL one_ne_zero
  have hD := SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant z
    one_mem_strictPeriods_SL one_ne_zero
  rw [CuspForm.coe_discriminant] at hD
  simp only [normalizedJCusp, Pi.div_apply, Pi.pow_apply, dslope_of_ne D₀ hq, slope_def_field,
    D₀_zero, sub_zero, hE, hD, modularInvariant]
  rw [div_div_eq_mul_div]
  ring

/-- On a neighborhood of the cusp, the integer series sums to the actual
analytic normalized modular invariant. -/
theorem hasSum_integralNormalizedJExpansion :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℍ, ‖Periodic.qParam 1 z‖ < ε →
      HasSum (fun n : ℕ ↦ (integralNormalizedJExpansion.coeff n : ℂ) *
        Periodic.qParam 1 z ^ n) (Periodic.qParam 1 z * modularInvariant z) := by
  have hseries := normalizedJCusp_analytic.hasFPowerSeriesAt
  change HasFPowerSeriesAt normalizedJCusp
    (FormalMultilinearSeries.ofScalars ℂ (fun n ↦
      iteratedDeriv n normalizedJCusp 0 / n.factorial)) 0 at hseries
  have hc (n : ℕ) : iteratedDeriv n normalizedJCusp 0 / (n.factorial : ℂ) =
      (integralNormalizedJExpansion.coeff n : ℂ) := by
    simpa only [taylorAtZero, coeff_mk, coeff_map, Int.coe_castRingHom, div_eq_mul_inv,
      mul_comm] using congrArg (fun f : ℂ⟦X⟧ ↦ f.coeff n) taylorAtZero_normalizedJCusp
  simp_rw [hc] at hseries
  have hevent : ∀ᶠ w : ℂ in 𝓝 0, HasSum
      (fun n : ℕ ↦ (integralNormalizedJExpansion.coeff n : ℂ) * w ^ n)
      (normalizedJCusp w) := by
    obtain ⟨r, hr⟩ := hseries
    filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hr.r_pos] with w hw
    simpa [FormalMultilinearSeries.ofScalars, zero_add, Finset.prod_const] using hr.hasSum hw
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, hε, fun z hz ↦ ?_⟩
  rw [← normalizedJCusp_apply]
  exact h (by simpa [dist_zero_right] using hz)

end GRHArticle.SingularModuli
