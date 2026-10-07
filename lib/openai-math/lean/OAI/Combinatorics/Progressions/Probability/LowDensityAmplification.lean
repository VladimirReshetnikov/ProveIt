import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth

namespace OAI

section

namespace Erdos3

open Filter

def LowDensityThreshold (H a : ℝ) : Prop := 0 < a ∧ H ^ 2 * a ≤ 1

theorem exists_low_density_discount {H₀ : ℝ} (hH : 1 < H₀) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ 1 ≤ κ ^ 2 * H₀ := by
  have hH0 : 0 < H₀ := by linarith
  have hs := Real.sq_sqrt hH0.le
  have hs0 := Real.sqrt_pos.mpr hH0
  have hs1 : 1 < Real.sqrt H₀ := by nlinarith
  refine ⟨(Real.sqrt H₀)⁻¹, inv_pos.mpr hs0, (inv_lt_one₀ hs0).mpr hs1, ?_⟩
  have hid : (Real.sqrt H₀)⁻¹ ^ 2 * H₀ = 1 := by
    calc
      _ = (Real.sqrt H₀)⁻¹ ^ 2 * (Real.sqrt H₀) ^ 2 := by rw [hs]
      _ = 1 := by field_simp
  exact hid.ge

theorem LowDensityThreshold.raw_target_lt_one {H a : ℝ}
    (h : LowDensityThreshold H a) (hH : 1 < H) : H * a < 1 := by
  have hHa : 0 < H * a := mul_pos (by linarith) h.1
  have hstrict := mul_lt_mul_of_pos_right hH hHa
  nlinarith [h.2]

theorem LowDensityThreshold.mul_of_next {κ H a : ℝ}
    (h : LowDensityThreshold (κ * H ^ 2) a) (hH : 1 < H) (hκH : 1 ≤ κ ^ 2 * H) :
    LowDensityThreshold H (H * a) := by
  refine ⟨mul_pos (by linarith) h.1, ?_⟩
  have hscale := mul_le_mul_of_nonneg_right hκH
    (mul_nonneg (pow_nonneg (by linarith : 0 ≤ H) 3) h.1.le)
  have hid : (κ ^ 2 * H) * (H ^ 3 * a) = (κ * H ^ 2) ^ 2 * a := by ring
  rw [hid] at hscale
  have hlast := hscale.trans h.2
  nlinarith

theorem LowDensityThreshold.of_next {κ H a : ℝ}
    (h : LowDensityThreshold (κ * H ^ 2) a) (hH : 1 < H) (hκH : 1 ≤ κ ^ 2 * H) :
    LowDensityThreshold H a ∧ a ≤ H * a := by
  have hmul := h.mul_of_next hH hκH
  have hmono : a ≤ H * a := by nlinarith [h.1]
  exact ⟨⟨h.1, (mul_le_mul_of_nonneg_left hmono (sq_nonneg H)).trans hmul.2⟩, hmono⟩

theorem amplificationGain_low_density_parameters {κ H₀ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 1 < H₀) (hκH : 1 ≤ κ ^ 2 * H₀) (j : ℕ) :
    1 < amplificationGain κ H₀ j ∧ 1 ≤ κ ^ 2 * amplificationGain κ H₀ j := by
  induction j with
  | zero => exact ⟨hH, hκH⟩
  | succ j ih =>
    let H := amplificationGain κ H₀ j
    have hH0 : 0 < H := by dsimp only [H]; linarith [ih.1]
    have hkk : κ ^ 2 < κ := by nlinarith
    have hκH' : 1 < κ * H :=
      ih.2.trans_lt (mul_lt_mul_of_pos_right hkk hH0)
    have hgrow : H < κ * H ^ 2 := by
      have h := mul_lt_mul_of_pos_right hκH' hH0
      nlinarith
    constructor
    · exact ih.1.trans hgrow
    · exact ih.2.trans (mul_le_mul_of_nonneg_left hgrow.le (sq_nonneg κ))

theorem low_density_amplification_calls {κ H₀ a : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 1 < H₀) (hκH : 1 ≤ κ ^ 2 * H₀)
    (j : ℕ) (ha : LowDensityThreshold (amplificationGain κ H₀ (j + 1)) a) :
    let H := amplificationGain κ H₀ j
    LowDensityThreshold H a ∧ LowDensityThreshold H (H * a) ∧
      a ≤ H * a ∧ H * (H * a) < 1 := by
  obtain ⟨hHj, hκHj⟩ := amplificationGain_low_density_parameters hκ hκ1 hH hκH j
  have hfirst := ha.of_next hHj hκHj
  have hsecond := ha.mul_of_next hHj hκHj
  exact ⟨hfirst.1, hsecond, hfirst.2, hsecond.raw_target_lt_one hHj⟩

theorem log_amplificationGain_le {κ H₀ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 0 < H₀) (j : ℕ) :
    Real.log (amplificationGain κ H₀ j) ≤ (2 : ℝ) ^ j * Real.log H₀ := by
  induction j with
  | zero => simp [amplificationGain]
  | succ j ih =>
    have hpos := amplificationGain_pos hκ hH j
    have hlogκ : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1
    rw [amplificationGain, Real.log_mul hκ.ne' (pow_ne_zero _ hpos.ne'),
      Real.log_pow, pow_succ]
    push_cast
    linarith

theorem log_gain_at_selected_level_le {κ H₀ K p : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 1 ≤ H₀) (hK : 1 < K) (hp : 1 ≤ p) :
    Real.log (amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊) ≤
      p ^ gainExponent K * Real.log H₀ := by
  exact (log_amplificationGain_le hκ hκ1 (by linarith) _).trans
    (mul_le_mul_of_nonneg_right (gain_base_at_selected_level hK hp).2 (Real.log_nonneg hH))

theorem eventually_low_density_at_selected_level {κ H₀ K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 1 ≤ H₀) (hK : 2 ≤ K) :
    ∀ᶠ p : ℝ in atTop,
      LowDensityThreshold (amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊)
        (Real.exp (-p)) := by
  obtain ⟨hν, hνq⟩ := gainExponent_pos_le_quarter hK
  have hν1 : gainExponent K < 1 := by linarith
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr hν1)).eventually_ge_atTop (2 * Real.log H₀)
  filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with p hpow hp
  have hp0 : 0 < p := by linarith
  have hlog := log_gain_at_selected_level_le (K := K) hκ hκ1 hH (by linarith) hp
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp0.le (gainExponent K))
  have hid : p ^ (1 - gainExponent K) * p ^ gainExponent K = p := by
    rw [← Real.rpow_add hp0, sub_add_cancel, Real.rpow_one]
  rw [hid] at hmul
  let H := amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊
  have hH0 : 0 < H := amplificationGain_pos hκ (by linarith) _
  have hlogbound : 2 * Real.log H - p ≤ 0 := by dsimp only [H]; linarith
  refine ⟨Real.exp_pos _, ?_⟩
  change H ^ 2 * Real.exp (-p) ≤ 1
  calc
    H ^ 2 * Real.exp (-p) = Real.exp (2 * Real.log H - p) := by
      rw [Real.exp_sub, show 2 * Real.log H = Real.log H + Real.log H by ring,
        Real.exp_add, Real.exp_log hH0, Real.exp_neg]
      ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr hlogbound

end Erdos3

end

end OAI
