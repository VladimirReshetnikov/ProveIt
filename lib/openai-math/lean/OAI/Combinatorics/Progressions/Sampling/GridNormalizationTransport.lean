import OAI.Combinatorics.Progressions.Estimates.SelectedWindowIndicator

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem grid_rescale_coordinate {K : ℝ} (hK : K ≠ 0) (N z : ℝ) :
    (K / N) * (z / K) = z / N := by
  calc
    _ = (K / K) * (z / N) := by ring
    _ = _ := by rw [div_self hK, one_mul]

theorem grid_normalization_identity (K N : ℝ) (hN : N ≠ 0) (d : ℕ) (z : ℂ) :
    ((K / N : ℝ) : ℂ) ^ d * ((N : ℂ) ^ d * z) = (K : ℂ) ^ d * z := by
  rw [Complex.ofReal_div, div_pow, ← mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hN))]

theorem grid_normalization_error {K N ε : ℝ} (hK : 0 ≤ K) (hN : 0 < N)
    (d : ℕ) (f g : ℂ) (he : ‖(N : ℂ) ^ d * f - g‖ ≤ ε) :
    ‖(K : ℂ) ^ d * f - ((K / N : ℝ) : ℂ) ^ d * g‖ ≤ (K / N) ^ d * ε := by
  have hid : (K : ℂ) ^ d * f - ((K / N : ℝ) : ℂ) ^ d * g =
      ((K / N : ℝ) : ℂ) ^ d * ((N : ℂ) ^ d * f - g) := by
    rw [mul_sub, grid_normalization_identity K N hN.ne']
  rw [hid, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg hK hN.le)]
  exact mul_le_mul_of_nonneg_left he (pow_nonneg (div_nonneg hK hN.le) _)

theorem complex_lipschitz_rescale (f : ℝ → ℂ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (r : ℝ≥0) : LipschitzWith (L * r) (fun x => f (r * x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ (L : ℝ) * dist ((r : ℝ) * x) ((r : ℝ) * y) := hf.dist_le_mul _ _
    _ = _ := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg r.coe_nonneg,
        NNReal.coe_mul, Real.dist_eq]
      ring

theorem grid_site_coefficient_norm {F : Type*} [Fintype F]
    (c : F → ℂ) {r : ℝ} (hr : 0 ≤ r) (d : ℕ) :
    (∑ i, ‖(r : ℂ) ^ d * c i‖) = r ^ d * ∑ i, ‖c i‖ := by
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr, Finset.mul_sum]

theorem grid_site_normalization_error {F T : Type*} [Fintype F] [Fintype T]
    {K N ε : ℝ} (hK : 0 < K) (hN : 0 < N) (d : ℕ)
    (mass : ℂ) (c : F → ℂ) (f : F → T → ℝ → ℂ) (y : T → ℝ)
    (he : ‖(N : ℂ) ^ d * mass - ∑ i, c i * ∏ t, f i t (y t / N)‖ ≤ ε) :
    ‖(K : ℂ) ^ d * mass -
      ∑ i, (((K / N : ℝ) : ℂ) ^ d * c i) * ∏ t, f i t ((K / N) * (y t / K))‖ ≤
      (K / N) ^ d * ε := by
  simp_rw [grid_rescale_coordinate hK.ne']
  simpa only [Finset.mul_sum, mul_assoc] using
    grid_normalization_error hK.le hN d mass (∑ i, c i * ∏ t, f i t (y t / N)) he

end Erdos3

end

end OAI
