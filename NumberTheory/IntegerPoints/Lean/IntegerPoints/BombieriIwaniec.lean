import IntegerPoints.ExponentialSums
import IntegerPoints.KuzminLandau
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Towards Zhai–Cao, Lemma 5 (Bombieri–Iwaniec)

Stage A.  Let `ψ₁ = 1_{(a₁, b₁)}` with `a₁ = ⌈N⌉ - ½`, `b₁ = ⌊N₁⌋ + ½`, and
`ψ₂ = 1_{(-½, ½)}`.  The trapezoid `τ = ψ₁ ⋆ ψ₂` is continuous, equals the
indicator of `(N, N₁]` on the integers, and by the convolution theorem
`𝓕τ = 𝓕ψ₁ · 𝓕ψ₂` with `|𝓕 1_{(a,b)}(w)| ≤ min(b - a, 1/(π|w|))`.
-/

open MeasureTheory Real Set
open scoped FourierTransform Convolution

namespace LeanProofs.IntegerPoints

namespace BI

/-- The indicator of `(a, b)` as a complex-valued function. -/
noncomputable def ind (a b : ℝ) : ℝ → ℂ := (Set.Ioo a b).indicator (fun _ => (1 : ℂ))

theorem integrable_ind (a b : ℝ) : Integrable (ind a b) :=
  (integrable_indicator_iff measurableSet_Ioo).2
    (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))

theorem norm_ind_le (a b t : ℝ) : ‖ind a b t‖ ≤ 1 := by
  unfold ind
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- `𝓕 1_{(a,b)}(w) = ∫_a^b e^{-2πi v w} dv`. -/
theorem fourier_ind (a b : ℝ) (hab : a ≤ b) (w : ℝ) :
    𝓕 (ind a b) w = ∫ v in a..b, Complex.exp (((-2 * π * w : ℝ) : ℂ) * Complex.I * v) := by
  rw [Real.fourier_eq']
  have : ∀ v : ℝ, Complex.exp ((↑(-2 * π * inner ℝ v w) : ℂ) * Complex.I) • ind a b v =
      (Set.Ioo a b).indicator (fun v => Complex.exp (((-2 * π * w : ℝ) : ℂ) * Complex.I * v)) v := by
    intro v
    unfold ind
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one]
      congr 1
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    · rw [smul_zero]
  simp_rw [this]
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab]

/-- `|𝓕 1_{(a,b)}(w)| ≤ b - a`. -/
theorem norm_fourier_ind_le_length (a b : ℝ) (hab : a ≤ b) (w : ℝ) :
    ‖𝓕 (ind a b) w‖ ≤ b - a := by
  rw [fourier_ind a b hab w]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun v : ℝ => Complex.exp (((-2 * π * w : ℝ) : ℂ) * Complex.I * v)) fun v _ => by
      rw [show ((-2 * π * w : ℝ) : ℂ) * Complex.I * v = ((-2 * π * w * v : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [one_mul, abs_of_nonneg (by linarith)] at this
  exact this

/-- `|𝓕 1_{(a,b)}(w)| ≤ 1/(π|w|)` for `w ≠ 0`. -/
theorem norm_fourier_ind_le_inv (a b : ℝ) (hab : a ≤ b) (w : ℝ) (hw : w ≠ 0) :
    ‖𝓕 (ind a b) w‖ ≤ 1 / (π * |w|) := by
  rw [fourier_ind a b hab w]
  set c : ℂ := ((-2 * π * w : ℝ) : ℂ) * Complex.I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw :
      (-2 * π * w : ℝ) ≠ 0)
  rw [integral_exp_mul_complex hc0, norm_div]
  have hnc : ‖c‖ = 2 * π * |w| := by
    rw [hc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  rw [hnc, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ‖Complex.exp (c * b) - Complex.exp (c * a)‖ ≤ 2 := by
    have e1 : ‖Complex.exp (c * b)‖ = 1 := by
      rw [hc, show ((-2 * π * w : ℝ) : ℂ) * Complex.I * b = ((-2 * π * w * b : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have e2 : ‖Complex.exp (c * a)‖ = 1 := by
      rw [hc, show ((-2 * π * w : ℝ) : ℂ) * Complex.I * a = ((-2 * π * w * a : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    calc ‖Complex.exp (c * b) - Complex.exp (c * a)‖ ≤ ‖Complex.exp (c * b)‖ + ‖Complex.exp (c * a)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [e1, e2]; norm_num
  nlinarith [mul_pos Real.pi_pos (abs_pos.2 hw)]

/-- The trapezoid `τ = 1_{(a₁,b₁)} ⋆ 1_{(-½,½)}`. -/
noncomputable def tau (a₁ b₁ : ℝ) : ℝ → ℂ := ind a₁ b₁ ⋆[ContinuousLinearMap.mul ℂ ℂ] ind (-1 / 2) (1 / 2)

/-- The explicit value of the trapezoid. -/
noncomputable def tauR (a₁ b₁ x : ℝ) : ℝ := max 0 (min b₁ (x + 1 / 2) - max a₁ (x - 1 / 2))

theorem tau_eq (a₁ b₁ : ℝ) (x : ℝ) : tau a₁ b₁ x = (tauR a₁ b₁ x : ℂ) := by
  unfold tau
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (ind a₁ b₁ t) (ind (-1 / 2) (1 / 2) (x - t)) =
      (Set.Ioo a₁ b₁ ∩ Set.Ioo (x - 1 / 2) (x + 1 / 2)).indicator (fun _ => (1 : ℂ)) t := by
    intro t
    simp only [ContinuousLinearMap.mul_apply', ind]
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_inter_iff, Set.mem_Ioo]
    by_cases h1 : a₁ < t ∧ t < b₁ <;> by_cases h2 : x - 1 / 2 < t ∧ t < x + 1 / 2
    · rw [if_pos h1, if_pos (by constructor <;> linarith [h2.1, h2.2]), if_pos ⟨h1, h2⟩, mul_one]
    · rw [if_pos h1, if_neg (by intro h; exact h2 ⟨by linarith [h.2], by linarith [h.1]⟩),
        if_neg (fun h => h2 h.2), mul_zero]
    · rw [if_neg h1, zero_mul, if_neg (fun h => h1 h.1)]
    · rw [if_neg h1, zero_mul, if_neg (fun h => h1 h.1)]
  simp_rw [this]
  rw [MeasureTheory.integral_indicator_const _ (measurableSet_Ioo.inter measurableSet_Ioo),
    Set.Ioo_inter_Ioo, Real.volume_real_Ioo, Complex.real_smul, mul_one]
  unfold tauR
  rw [max_comm]

theorem tauR_nonneg (a₁ b₁ x : ℝ) : 0 ≤ tauR a₁ b₁ x := le_max_left _ _

theorem tauR_le_one (a₁ b₁ x : ℝ) : tauR a₁ b₁ x ≤ 1 := by
  unfold tauR
  rw [max_le_iff]
  refine ⟨by norm_num, ?_⟩
  have h1 : min b₁ (x + 1 / 2) ≤ x + 1 / 2 := min_le_right _ _
  have h2 : x - 1 / 2 ≤ max a₁ (x - 1 / 2) := le_max_right _ _
  linarith

theorem continuous_tauR (a₁ b₁ : ℝ) : Continuous (tauR a₁ b₁) := by
  unfold tauR
  fun_prop

/-- `τ = 1` on `[a₁ + ½, b₁ - ½]`. -/
theorem tauR_eq_one (a₁ b₁ x : ℝ) (h1 : a₁ + 1 / 2 ≤ x) (h2 : x ≤ b₁ - 1 / 2) : tauR a₁ b₁ x = 1 := by
  unfold tauR
  rw [min_eq_right (by linarith : x + 1 / 2 ≤ b₁), max_eq_right (by linarith : a₁ ≤ x - 1 / 2),
    max_eq_right (by linarith : (0 : ℝ) ≤ x + 1 / 2 - (x - 1 / 2))]
  ring

/-- `τ = 0` outside `(a₁ - ½, b₁ + ½)`. -/
theorem tauR_eq_zero (a₁ b₁ x : ℝ) (h : x + 1 / 2 ≤ a₁ ∨ b₁ ≤ x - 1 / 2) : tauR a₁ b₁ x = 0 := by
  unfold tauR
  rw [max_eq_left]
  rcases h with h | h
  · have := min_le_right b₁ (x + 1 / 2)
    have := le_max_left a₁ (x - 1 / 2)
    linarith
  · have := min_le_left b₁ (x + 1 / 2)
    have := le_max_right a₁ (x - 1 / 2)
    linarith

/-! ### Stage B: the Fourier transform of the trapezoid and inversion -/

theorem fourier_tau (a₁ b₁ w : ℝ) :
    𝓕 (tau a₁ b₁) w = 𝓕 (ind a₁ b₁) w * 𝓕 (ind (-1 / 2) (1 / 2)) w :=
  Real.fourier_mul_convolution_eq (integrable_ind _ _) (integrable_ind _ _) w

theorem norm_fourier_ind_half_le_one (w : ℝ) : ‖𝓕 (ind (-1 / 2) (1 / 2)) w‖ ≤ 1 := by
  have := norm_fourier_ind_le_length (-1 / 2) (1 / 2) (by norm_num) w
  rwa [show (1 / 2 : ℝ) - -1 / 2 = 1 by norm_num] at this

/-- `‖𝓕τ(w)‖ ≤ b₁ - a₁` for all `w`. -/
theorem norm_fourier_tau_le (a₁ b₁ : ℝ) (hab : a₁ ≤ b₁) (w : ℝ) :
    ‖𝓕 (tau a₁ b₁) w‖ ≤ b₁ - a₁ := by
  rw [fourier_tau, norm_mul]
  calc ‖𝓕 (ind a₁ b₁) w‖ * ‖𝓕 (ind (-1 / 2) (1 / 2)) w‖ ≤ (b₁ - a₁) * 1 :=
        mul_le_mul (norm_fourier_ind_le_length a₁ b₁ hab w)
          (norm_fourier_ind_half_le_one w)
          (norm_nonneg _) (by linarith)
    _ = b₁ - a₁ := mul_one _

/-- `‖𝓕τ(w)‖ ≤ min (b₁ - a₁) (1/(π|w|)) · min 1 (1/(π|w|))` for `w ≠ 0`. -/
theorem norm_fourier_tau_le' (a₁ b₁ : ℝ) (hab : a₁ ≤ b₁) (w : ℝ) (hw : w ≠ 0) :
    ‖𝓕 (tau a₁ b₁) w‖ ≤ min (b₁ - a₁) (1 / (π * |w|)) * min 1 (1 / (π * |w|)) := by
  rw [fourier_tau, norm_mul]
  refine mul_le_mul (le_min (norm_fourier_ind_le_length a₁ b₁ hab w)
    (norm_fourier_ind_le_inv a₁ b₁ hab w hw)) (le_min ?_ (norm_fourier_ind_le_inv _ _ (by norm_num) w hw))
    (norm_nonneg _) (le_min (by linarith) (by positivity))
  exact norm_fourier_ind_half_le_one w

/-- `‖𝓕τ(w)‖ ≤ biKernel M M₁ w` for `w ≠ 0` when `b₁ - a₁ ≤ M₁ - M + 1`. -/
theorem norm_fourier_tau_le_biKernel (a₁ b₁ M M₁ : ℝ) (hab : a₁ ≤ b₁) (hW : b₁ - a₁ ≤ M₁ - M + 1)
    (w : ℝ) (hw : w ≠ 0) : ‖𝓕 (tau a₁ b₁) w‖ ≤ biKernel M M₁ w := by
  refine (norm_fourier_tau_le' a₁ b₁ hab w hw).trans ?_
  unfold biKernel
  have hp : 0 < (π * |w|)⁻¹ := by positivity
  rw [one_div]
  refine le_min ?_ (le_min ?_ ?_)
  · calc min (b₁ - a₁) (π * |w|)⁻¹ * min 1 (π * |w|)⁻¹ ≤ (b₁ - a₁) * 1 :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min (by linarith) hp.le) (by linarith)
      _ ≤ M₁ - M + 1 := by linarith
  · calc min (b₁ - a₁) (π * |w|)⁻¹ * min 1 (π * |w|)⁻¹ ≤ (π * |w|)⁻¹ * 1 :=
        mul_le_mul (min_le_right _ _) (min_le_left _ _) (le_min (by linarith) hp.le) hp.le
      _ = (π * |w|)⁻¹ := mul_one _
  · calc min (b₁ - a₁) (π * |w|)⁻¹ * min 1 (π * |w|)⁻¹ ≤ (π * |w|)⁻¹ * (π * |w|)⁻¹ :=
        mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min (by linarith) hp.le) hp.le
      _ = (π * |w|)⁻¹ ^ 2 := by ring

/-- `min(W, (π w)⁻²) ≤ 2 max(W, π⁻²) / (1 + w²)`: the dominating function. -/
theorem bound_le_inv_one_add_sq (W w : ℝ) (hW : 0 ≤ W) :
    min W ((π * |w|)⁻¹ ^ 2) ≤ 2 * max W (π ^ 2)⁻¹ / (1 + w ^ 2) := by
  have hπ : 0 < π ^ 2 := by positivity
  rcases le_or_gt (w ^ 2) 1 with h | h
  · calc min W ((π * |w|)⁻¹ ^ 2) ≤ W := min_le_left _ _
      _ ≤ max W (π ^ 2)⁻¹ := le_max_left _ _
      _ = max W (π ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ max W (π ^ 2)⁻¹ * (2 / (1 + w ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (le_trans hW (le_max_left _ _))
          rw [le_div_iff₀ (by positivity)]
          linarith
      _ = 2 * max W (π ^ 2)⁻¹ / (1 + w ^ 2) := by ring
  · have hw0 : w ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    calc min W ((π * |w|)⁻¹ ^ 2) ≤ (π * |w|)⁻¹ ^ 2 := min_le_right _ _
      _ = (π ^ 2)⁻¹ * (1 / w ^ 2) := by
          rw [inv_pow, mul_pow, sq_abs, mul_inv, one_div]
      _ ≤ max W (π ^ 2)⁻¹ * (2 / (1 + w ^ 2)) := by
          apply mul_le_mul (le_max_right _ _) _ (by positivity) (le_trans hW (le_max_left _ _))
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = 2 * max W (π ^ 2)⁻¹ / (1 + w ^ 2) := by ring

theorem measurable_biKernel (M M₁ : ℝ) : Measurable (biKernel M M₁) := by
  unfold biKernel
  fun_prop

/-- `biKernel M M₁ w ≤ min W (π w)⁻²` with `W = M₁ - M + 1`. -/
theorem biKernel_le (M M₁ w : ℝ) : biKernel M M₁ w ≤ min (M₁ - M + 1) ((π * |w|)⁻¹ ^ 2) := by
  unfold biKernel
  exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

theorem biKernel_nonneg (M M₁ w : ℝ) (hM : M ≤ M₁) : 0 ≤ biKernel M M₁ w := by
  unfold biKernel
  exact le_min (by linarith) (le_min (by positivity) (by positivity))

/-- `τ` is integrable. -/
theorem integrable_tau (a₁ b₁ : ℝ) : Integrable (tau a₁ b₁) := by
  have heq : tau a₁ b₁ = (Set.Icc (a₁ - 1 / 2) (b₁ + 1 / 2)).indicator (tau a₁ b₁) := by
    ext x
    rw [Set.indicator_apply]
    split_ifs with h
    · rfl
    · rw [tau_eq, tauR_eq_zero]
      · simp
      · rw [Set.mem_Icc, not_and_or] at h
        rcases h with h | h <;> push Not at h
        · left; linarith
        · right; linarith
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · have : Continuous (tau a₁ b₁) := by
      have : tau a₁ b₁ = fun x => (tauR a₁ b₁ x : ℂ) := funext (tau_eq a₁ b₁)
      rw [this]
      exact Complex.continuous_ofReal.comp (continuous_tauR a₁ b₁)
    exact this.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [tau_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tauR_nonneg _ _ _)]
    exact tauR_le_one _ _ _

theorem continuous_tau (a₁ b₁ : ℝ) : Continuous (tau a₁ b₁) := by
  have : tau a₁ b₁ = fun x => (tauR a₁ b₁ x : ℂ) := funext (tau_eq a₁ b₁)
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_tauR a₁ b₁)

/-- `𝓕τ` is integrable. -/
theorem integrable_fourier_tau (a₁ b₁ : ℝ) (hab : a₁ ≤ b₁) : Integrable (𝓕 (tau a₁ b₁)) := by
  set W := b₁ - a₁ with hW
  have hW0 : 0 ≤ W := by linarith
  refine Integrable.mono' (g := fun w => 2 * max W (π ^ 2)⁻¹ / (1 + w ^ 2)) ?_ ?_ ?_
  · have := integrable_inv_one_add_sq
    simpa [div_eq_mul_inv] using this.const_mul (2 * max W (π ^ 2)⁻¹)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) (integrable_tau a₁ b₁)).aestronglyMeasurable
  · refine (ae_iff.2 ?_)
    refine measure_mono_null (fun w hw => ?_) (measure_singleton (0 : ℝ))
    by_contra h0
    apply hw
    have hw0 : w ≠ 0 := h0
    calc ‖𝓕 (tau a₁ b₁) w‖ ≤ min (b₁ - a₁) (1 / (π * |w|)) * min 1 (1 / (π * |w|)) :=
          norm_fourier_tau_le' a₁ b₁ hab w hw0
      _ ≤ min W ((π * |w|)⁻¹ ^ 2) := by
          rw [one_div, hW]
          have hp : 0 < (π * |w|)⁻¹ := by positivity
          refine le_min ?_ ?_
          · calc min (b₁ - a₁) (π * |w|)⁻¹ * min 1 (π * |w|)⁻¹ ≤ (b₁ - a₁) * 1 :=
                mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min (by linarith) hp.le)
                  (by linarith)
              _ = b₁ - a₁ := mul_one _
          · calc min (b₁ - a₁) (π * |w|)⁻¹ * min 1 (π * |w|)⁻¹ ≤ (π * |w|)⁻¹ * (π * |w|)⁻¹ :=
                mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min (by linarith) hp.le)
                  hp.le
              _ = (π * |w|)⁻¹ ^ 2 := by ring
      _ ≤ 2 * max W (π ^ 2)⁻¹ / (1 + w ^ 2) := bound_le_inv_one_add_sq W w hW0

/-- Fourier inversion for the trapezoid at a point: `τ(x) = ∫ 𝓕τ(w) e(x w) dw`. -/
theorem tau_eq_integral (a₁ b₁ : ℝ) (hab : a₁ ≤ b₁) (x : ℝ) :
    tau a₁ b₁ x = ∫ w : ℝ, 𝓕 (tau a₁ b₁) w * e (x * w) := by
  have h := (continuous_tau a₁ b₁).fourier_inversion (integrable_tau a₁ b₁)
    (integrable_fourier_tau a₁ b₁ hab)
  have h' := congrFun h x
  rw [Real.fourierInv_eq'] at h'
  rw [← h']
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [smul_eq_mul, mul_comm]
  congr 1
  unfold e
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-! ### Stage B5–B6: values at integers and the assembly of part 1 -/

/-- With `a₁ = ⌊N⌋₊ + ½`, `b₁ = ⌊N₁⌋₊ + ½`, the trapezoid is the indicator of
`(N, N₁]` on the integers. -/
theorem tauR_nat (N N₁ : ℝ) (m : ℕ) :
    tauR ((⌊N⌋₊ : ℝ) + 1 / 2) ((⌊N₁⌋₊ : ℝ) + 1 / 2) m =
      if m ∈ intRange N N₁ then 1 else 0 := by
  simp only [intRange, Finset.mem_Ioc]
  split_ifs with h
  · refine tauR_eq_one _ _ _ ?_ ?_
    · have : (⌊N⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast h.1
      linarith
    · have : (m : ℝ) ≤ ⌊N₁⌋₊ := by exact_mod_cast h.2
      linarith
  · refine tauR_eq_zero _ _ _ ?_
    rw [not_and_or] at h
    rcases h with h | h
    · left
      have : (m : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast not_lt.1 h
      linarith
    · right
      have : (⌊N₁⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast not_le.1 h
      linarith

theorem integrable_biKernel (M M₁ : ℝ) (hM : M ≤ M₁) : Integrable (biKernel M M₁) := by
  set W := M₁ - M + 1 with hW
  have hW0 : 0 ≤ W := by linarith
  refine Integrable.mono' (g := fun w => 2 * max W (π ^ 2)⁻¹ / (1 + w ^ 2)) ?_
    (measurable_biKernel M M₁).aestronglyMeasurable ?_
  · have := integrable_inv_one_add_sq
    simpa [div_eq_mul_inv] using this.const_mul (2 * max W (π ^ 2)⁻¹)
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (biKernel_nonneg M M₁ w hM)]
    exact (biKernel_le M M₁ w).trans (bound_le_inv_one_add_sq W w hW0)

theorem continuous_expSum (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous fun θ : ℝ => ∑ m ∈ S, a m * e (m * θ) := by
  refine continuous_finset_sum _ fun m _ => continuous_const.mul ?_
  unfold e
  fun_prop

theorem norm_expSum_le (S : Finset ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    ‖∑ m ∈ S, a m * e (m * θ)‖ ≤ ∑ m ∈ S, ‖a m‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_e, mul_one]

/-- **Zhai–Cao, Lemma 5, part 1.** -/
theorem part1 (M N N₁ M₁ : ℝ) (a : ℕ → ℂ) (hM0 : 0 ≤ M) (hMN : M ≤ N) (hNN : N < N₁)
    (hN₁ : N₁ ≤ M₁) :
    ‖∑ n ∈ intRange N N₁, a n‖ ≤
      ∫ θ : ℝ, biKernel M M₁ θ * ‖∑ m ∈ intRange M M₁, a m * e (m * θ)‖ := by
  classical
  set a₁ : ℝ := (⌊N⌋₊ : ℝ) + 1 / 2 with ha₁
  set b₁ : ℝ := (⌊N₁⌋₊ : ℝ) + 1 / 2 with hb₁
  have hN0 : 0 ≤ N := le_trans hM0 hMN
  have hab : a₁ ≤ b₁ := by
    have : (⌊N⌋₊ : ℝ) ≤ ⌊N₁⌋₊ := by exact_mod_cast Nat.floor_le_floor hNN.le
    rw [ha₁, hb₁]
    linarith
  have hW : b₁ - a₁ ≤ M₁ - M + 1 := by
    have h1 : (⌊N₁⌋₊ : ℝ) ≤ N₁ := Nat.floor_le (by linarith)
    have h2 : N < ⌊N⌋₊ + 1 := Nat.lt_floor_add_one N
    rw [ha₁, hb₁]
    linarith
  have hMM₁ : M ≤ M₁ := by linarith
  set S := intRange M M₁ with hS
  have hsub : intRange N N₁ ⊆ S := by
    simp only [intRange, hS]
    exact Finset.Ioc_subset_Ioc (Nat.floor_le_floor hMN) (Nat.floor_le_floor hN₁)
  -- the left side as a sum over `S` against the trapezoid
  have h1 : ∑ n ∈ intRange N N₁, a n = ∑ m ∈ S, a m * tau a₁ b₁ m := by
    have : ∑ n ∈ intRange N N₁, a n = ∑ m ∈ S, (if m ∈ intRange N N₁ then a m else 0) := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [tau_eq, ha₁, hb₁, tauR_nat]
    split_ifs <;> simp
  -- exchange sum and integral
  have hint : ∀ m : ℕ, Integrable fun w : ℝ => a m * (𝓕 (tau a₁ b₁) w * e (m * w)) := by
    intro m
    refine Integrable.const_mul ?_ (a m)
    have hc : Continuous fun w : ℝ => e (m * w) := by
      unfold e
      fun_prop
    have hb : Integrable fun w : ℝ => e (m * w) * 𝓕 (tau a₁ b₁) w :=
      (integrable_fourier_tau a₁ b₁ hab).bdd_mul (c := 1) hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => by rw [norm_e])
    refine hb.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    ring
  have h2 : ∑ m ∈ S, a m * tau a₁ b₁ m =
      ∫ w : ℝ, 𝓕 (tau a₁ b₁) w * ∑ m ∈ S, a m * e (m * w) := by
    simp_rw [tau_eq_integral a₁ b₁ hab, ← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_finset_sum _ (fun m _ => hint m)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [h1, h2]
  have hK := integrable_biKernel M M₁ hMM₁
  have hSc := continuous_expSum S a
  have hbdd : Integrable fun w => biKernel M M₁ w * ‖∑ m ∈ S, a m * e (m * w)‖ := by
    have := hK.bdd_mul (f := fun w => ‖∑ m ∈ S, a m * e (m * w)‖) (c := ∑ m ∈ S, ‖a m‖)
      hSc.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_expSum_le S a w)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    ring
  refine norm_integral_le_of_norm_le hbdd ?_
  refine ae_iff.2 (measure_mono_null (fun w hw => ?_) (measure_singleton (0 : ℝ)))
  by_contra h0
  apply hw
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_fourier_tau_le_biKernel a₁ b₁ M M₁ hab hW w h0)
    (norm_nonneg _)

/-! ### Stage C: the integral of the kernel -/

/-- `π > 3`, from `sin(1/2) < 1/2 = sin(π/6)`. -/
theorem pi_gt_three' : 3 < π := by
  by_contra h
  push Not at h
  have h1 : Real.sin (π / 6) ≤ Real.sin (1 / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.two_le_pi])
      (by linarith)
  rw [Real.sin_pi_div_six] at h1
  have := Real.sin_lt (by norm_num : (0 : ℝ) < 1 / 2)
  linarith

/-- `log 2 > 4/7`, from `log 2 = 2 log √2 ≥ 2(1 - 1/√2)` and `√2 > 1.41`. -/
theorem log_two_gt : 4 / 7 < Real.log 2 := by
  have hs : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have h1 : Real.log 2 = 2 * Real.log (Real.sqrt 2) := by
    rw [Real.log_sqrt (by norm_num)]
    ring
  have h2 : 1 - 1 / Real.sqrt 2 ≤ Real.log (Real.sqrt 2) := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / Real.sqrt 2)
    rw [Real.log_div one_ne_zero hs0.ne', Real.log_one] at this
    linarith
  have h3 : 1 / Real.sqrt 2 < 1 / 1.41 := one_div_lt_one_div_of_lt (by norm_num) hs
  have h4 : (1 : ℝ) / 1.41 < 0.71 := by norm_num
  linarith

/-- The kernel as a function of `|θ|`. -/
noncomputable def gK (W t : ℝ) : ℝ := min W (min (π * t)⁻¹ ((π * t)⁻¹ ^ 2))

theorem biKernel_eq_gK (M M₁ : ℝ) : biKernel M M₁ = fun θ => gK (M₁ - M + 1) |θ| := by
  funext θ
  rfl

theorem measurable_gK (W : ℝ) : Measurable (gK W) := by
  unfold gK
  fun_prop

theorem gK_nonneg (W t : ℝ) (hW : 0 ≤ W) (ht : 0 ≤ t) : 0 ≤ gK W t :=
  le_min hW (le_min (inv_nonneg.2 (mul_nonneg Real.pi_pos.le ht))
    (pow_nonneg (inv_nonneg.2 (mul_nonneg Real.pi_pos.le ht)) 2))

/-- On `(0, 1/(πW)]` the kernel is `W`. -/
theorem gK_eq_W (W t : ℝ) (hW : 1 ≤ W) (ht0 : 0 < t) (ht : t ≤ 1 / (π * W)) : gK W t = W := by
  unfold gK
  have hπt : 0 < π * t := mul_pos Real.pi_pos ht0
  have hW0 : (0 : ℝ) < W := by linarith
  have hx : W ≤ (π * t)⁻¹ := by
    rw [le_div_iff₀ (mul_pos Real.pi_pos hW0)] at ht
    have e : W * (π * t) = t * (π * W) := by ring
    rw [show (π * t)⁻¹ = 1 / (π * t) by rw [one_div], le_div_iff₀ hπt]
    linarith
  have hx1 : 1 ≤ (π * t)⁻¹ := le_trans hW hx
  rw [min_eq_left (show (π * t)⁻¹ ≤ (π * t)⁻¹ ^ 2 by nlinarith), min_eq_left hx]

/-- On `(1/(πW), 1/π]` the kernel is `(πt)⁻¹`. -/
theorem gK_eq_inv (W t : ℝ) (hW : 1 ≤ W) (ht1 : 1 / (π * W) < t) (ht2 : t ≤ 1 / π) :
    gK W t = (π * t)⁻¹ := by
  unfold gK
  have ht0 : 0 < t := lt_trans (by positivity) ht1
  have hπt : 0 < π * t := mul_pos Real.pi_pos ht0
  have hx1 : 1 ≤ (π * t)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hπt, inv_one]
    rw [le_div_iff₀ Real.pi_pos] at ht2
    linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hxW : (π * t)⁻¹ ≤ W := by
    rw [div_lt_iff₀ (mul_pos Real.pi_pos hW0)] at ht1
    have e : t * (π * W) = (π * t) * W := by ring
    rw [show (π * t)⁻¹ = 1 / (π * t) by rw [one_div], div_le_iff₀ hπt]
    linarith
  rw [min_eq_left (show (π * t)⁻¹ ≤ (π * t)⁻¹ ^ 2 by nlinarith), min_eq_right hxW]

/-- On `(1/π, ∞)` the kernel is `(πt)⁻²`. -/
theorem gK_eq_inv_sq (W t : ℝ) (hW : 1 ≤ W) (ht : 1 / π < t) : gK W t = (π * t)⁻¹ ^ 2 := by
  unfold gK
  have ht0 : 0 < t := lt_trans (by positivity) ht
  have hπt : 0 < π * t := mul_pos Real.pi_pos ht0
  have hx1 : (π * t)⁻¹ < 1 := by
    rw [inv_lt_comm₀ hπt (by norm_num), inv_one]
    rw [div_lt_iff₀ Real.pi_pos] at ht
    linarith
  have hx0 : 0 < (π * t)⁻¹ := by positivity
  have hsq : (π * t)⁻¹ ^ 2 ≤ (π * t)⁻¹ := by nlinarith
  rw [min_eq_right hsq, min_eq_right (by nlinarith)]

/-- `∫_{(0, 1/(πW)]} g = 1/π`. -/
theorem integral_gK_I1 (W : ℝ) (hW : 1 ≤ W) :
    ∫ t in Set.Ioc 0 (1 / (π * W)), gK W t = 1 / π := by
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => gK_eq_W W t hW ht.1 ht.2),
    setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), smul_eq_mul]
  field_simp
  ring

/-- `∫_{(1/(πW), 1/π]} g = log W / π`. -/
theorem integral_gK_I2 (W : ℝ) (hW : 1 ≤ W) :
    ∫ t in Set.Ioc (1 / (π * W)) (1 / π), gK W t = Real.log W / π := by
  have hab : 1 / (π * W) ≤ 1 / π := by
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => gK_eq_inv W t hW ht.1 ht.2),
    ← intervalIntegral.integral_of_le hab]
  have : ∀ t : ℝ, (π * t)⁻¹ = π⁻¹ * t⁻¹ := fun t => by rw [mul_inv]
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_inv]
  · rw [show (1 / π) / (1 / (π * W)) = W by field_simp]
    ring
  · rw [Set.uIcc_of_le hab]
    intro h
    have := h.1
    have : 0 < 1 / (π * W) := by positivity
    linarith

/-- `∫_{(1/π, ∞)} g = 1/π`. -/
theorem integral_gK_I3 (W : ℝ) (hW : 1 ≤ W) :
    ∫ t in Set.Ioi (1 / π), gK W t = 1 / π := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => gK_eq_inv_sq W t hW ht)]
  have hb : (0 : ℝ) < 1 / π := by positivity
  have : ∀ t ∈ Set.Ioi (1 / π), (π * t)⁻¹ ^ 2 = (π ^ 2)⁻¹ * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hb ht
    rw [Real.rpow_neg ht0.le, Real.rpow_two, mul_inv, mul_pow, inv_pow, inv_pow]
  rw [setIntegral_congr_fun measurableSet_Ioi this, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) hb]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, one_div, inv_inv]
  field_simp

theorem integrableOn_gK_Ioc (W a b : ℝ) (hW : 1 ≤ W) (ha : 0 ≤ a) :
    IntegrableOn (gK W) (Set.Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := W) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_gK W).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (gK_nonneg W t (by linarith) (by linarith [ht.1]))]
  exact min_le_left _ _

theorem integrableOn_gK_Ioi (W : ℝ) (hW : 1 ≤ W) : IntegrableOn (gK W) (Set.Ioi (1 / π)) := by
  have hb : (0 : ℝ) < 1 / π := by positivity
  have hint : IntegrableOn (fun t : ℝ => (π ^ 2)⁻¹ * t ^ (-2 : ℝ)) (Set.Ioi (1 / π)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hb).const_mul _
  refine hint.mono' (measurable_gK W).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := lt_trans hb ht
  rw [Real.norm_eq_abs, abs_of_nonneg (gK_nonneg W t (by linarith) ht0.le), gK_eq_inv_sq W t hW ht,
    Real.rpow_neg ht0.le, Real.rpow_two, mul_inv, mul_pow, inv_pow, inv_pow]

/-- `∫_{(0,∞)} g = (2 + log W)/π`. -/
theorem integral_gK_Ioi (W : ℝ) (hW : 1 ≤ W) :
    ∫ t in Set.Ioi (0 : ℝ), gK W t = (2 + Real.log W) / π := by
  have ha : (0 : ℝ) ≤ 1 / (π * W) := by positivity
  have hab : 1 / (π * W) ≤ 1 / π := by
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsplit1 : Set.Ioi (0 : ℝ) = Set.Ioc 0 (1 / π) ∪ Set.Ioi (1 / π) :=
    (Set.Ioc_union_Ioi_eq_Ioi (le_trans ha hab)).symm
  have hsplit2 : Set.Ioc (0 : ℝ) (1 / π) = Set.Ioc 0 (1 / (π * W)) ∪ Set.Ioc (1 / (π * W)) (1 / π) :=
    (Set.Ioc_union_Ioc_eq_Ioc ha hab).symm
  have hd1 : Disjoint (Set.Ioc (0 : ℝ) (1 / π)) (Set.Ioi (1 / π)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx
    rw [Set.mem_Ioi] at hx'
    linarith
  have hd2 : Disjoint (Set.Ioc (0 : ℝ) (1 / (π * W))) (Set.Ioc (1 / (π * W)) (1 / π)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx hx'
    linarith
  rw [hsplit1, setIntegral_union hd1 measurableSet_Ioi
    (integrableOn_gK_Ioc W _ _ hW le_rfl) (integrableOn_gK_Ioi W hW),
    hsplit2, setIntegral_union hd2 measurableSet_Ioc (integrableOn_gK_Ioc W _ _ hW le_rfl)
    (integrableOn_gK_Ioc W _ _ hW ha), integral_gK_I1 W hW, integral_gK_I2 W hW,
    integral_gK_I3 W hW]
  field_simp
  ring

/-- `(2/π)(2 + log W) ≤ 3 log(1 + W)` for `W ≥ 1`. -/
theorem numeric_bound (W : ℝ) (hW : 1 ≤ W) :
    2 * ((2 + Real.log W) / π) ≤ 3 * Real.log (1 + W) := by
  have hπ := pi_gt_three'
  have hL : 0 ≤ Real.log W := Real.log_nonneg hW
  have hx1 : Real.log W ≤ Real.log (1 + W) := Real.log_le_log (by linarith) (by linarith)
  have hx2 : Real.log 2 ≤ Real.log (1 + W) := Real.log_le_log (by norm_num) (by linarith)
  have h47 := log_two_gt
  have h1 : 2 * ((2 + Real.log W) / π) ≤ 2 * ((2 + Real.log W) / 3) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hπ.le
  linarith

/-- **Zhai–Cao, Lemma 5, part 2.** -/
theorem part2 (M M₁ : ℝ) (hM : M ≤ M₁) :
    ∫ θ : ℝ, biKernel M M₁ θ ≤ 3 * Real.log (2 + M₁ - M) := by
  rw [biKernel_eq_gK, integral_comp_abs, integral_gK_Ioi _ (by linarith)]
  have := numeric_bound (M₁ - M + 1) (by linarith)
  rwa [show (1 : ℝ) + (M₁ - M + 1) = 2 + M₁ - M by ring] at this

end BI

/-- **Zhai–Cao, Lemma 5** (`zhaiCao_lemma5`), the Bombieri–Iwaniec inequality. -/
theorem zhaiCao_lemma5_holds : zhaiCao_lemma5 :=
  ⟨fun M N N₁ M₁ a hM0 hMN hNN hN₁ => BI.part1 M N N₁ M₁ a hM0 hMN hNN hN₁,
    fun M M₁ hM => BI.part2 M M₁ hM⟩



end LeanProofs.IntegerPoints
