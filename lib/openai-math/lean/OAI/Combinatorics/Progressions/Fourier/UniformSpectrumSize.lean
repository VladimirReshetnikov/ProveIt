import OAI.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters

namespace OAI

section

namespace Erdos3

noncomputable def uniformBlockRetainedBias (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  min 1 (ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1))

theorem uniformBlockRetainedBias_spec (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    0 < uniformBlockRetainedBias n j t U V W ε ∧
      uniformBlockRetainedBias n j t U V W ε ≤ 1 ∧
      uniformBlockSpectrumAccuracyConstant n j t U V W *
        uniformBlockRetainedBias n j t U V W ε ≤ ε := by
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hnonneg : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  have hpos : 0 < uniformBlockRetainedBias n j t U V W ε :=
    lt_min (by norm_num) (div_pos hε (by linarith))
  refine ⟨hpos, min_le_left _ _, ?_⟩
  calc
    _ ≤ (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) *
        uniformBlockRetainedBias n j t U V W ε :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ ≤ (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) *
        (ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    _ = ε := by field_simp

theorem uniformSpectrumBlockCount_quadratic (n j s : ℕ) :
    uniformSpectrumBlockCount n j (s * j) ≤
      (4 * majorArcBiasExponent n + 4 * majorArcErrorExponent n + majorArcLengthExponent n * s + 1) *
        (j + 1) ^ 2 := by
  have hj : j ≤ (j + 1) ^ 2 := by nlinarith
  have hj2 : j ^ 2 ≤ (j + 1) ^ 2 := by nlinarith
  have h1 : 1 ≤ (j + 1) ^ 2 := by nlinarith
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
  have hm (x y : ℕ) : max x y ≤ x + y := max_le (by omega) (by omega)
  apply (Nat.add_le_add_right (hm _ _) 1).trans
  nlinarith [Nat.mul_le_mul_left (4 * majorArcBiasExponent n) hj2,
    Nat.mul_le_mul_left (4 * majorArcErrorExponent n) hj,
    Nat.mul_le_mul_left (majorArcLengthExponent n * s) hj]

theorem grid_size_power_bound {M K R D L : ℝ} {s j : ℕ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hMK : M ≤ R * K) (hKL : K ≤ D * L ^ s) :
    M ^ j ≤ (R * D) ^ j * L ^ (s * j) := by
  have hm : M ≤ (R * D) * L ^ s := by
    calc
      _ ≤ R * K := hMK
      _ ≤ R * (D * L ^ s) := mul_le_mul_of_nonneg_left hKL hR
      _ = _ := by ring
  calc
    _ ≤ ((R * D) * L ^ s) ^ j := pow_le_pow_left₀ hM hm j
    _ = _ := by rw [mul_pow, pow_mul]

end Erdos3

end

section

namespace Erdos3

theorem uniformBlockRetainedBias_eq (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε1 : ε ≤ 1) :
    uniformBlockRetainedBias n j t U V W ε =
      ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) := by
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hnonneg : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  apply min_eq_right
  apply (div_le_iff₀ (by linarith)).mpr
  linarith

noncomputable def uniformSpectrumSizeConstant (n j t : ℕ) (U V W : ℝ) : ℝ :=
  (majorArcSpectrumConstant n j U V + W * majorArcLengthConstant n U ^ t) *
    (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) ^
      max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)

theorem uniformBlockSpectrumCardBudget_le_accuracy_power (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    uniformBlockSpectrumCardBudget n j t U V W (uniformBlockRetainedBias n j t U V W ε) ≤
      uniformSpectrumSizeConstant n j t U V W /
        ε ^ max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n j t hU hW hε
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hb : 0 ≤ W * majorArcLengthConstant n U ^ t := by positivity
  have ha := inverse_power_mono hA le_rfl hζ hζ1
    (le_max_left (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t))
  have hp := inverse_power_mono hb le_rfl hζ hζ1
    (le_max_right (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t))
  unfold uniformBlockSpectrumCardBudget
  apply (add_le_add ha hp).trans_eq
  rw [← add_div, uniformBlockRetainedBias_eq n j t hU hW hε1]
  simp only [uniformSpectrumSizeConstant, div_pow, div_div_eq_mul_div]

theorem uniformBlockSpectrumCover_polynomial_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
      uniformSpectrumSizeConstant n (Fintype.card J) t U V W /
        ε ^ max (majorArcSpectrumExponent n (Fintype.card J)) (majorArcLengthExponent n * t) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  exact (uniformBlockSpectrumCover_card J M n t hU hV hW hL hζ hζ1 hsize).trans
    (uniformBlockSpectrumCardBudget_le_accuracy_power n (Fintype.card J) t hU hW hε hε1)

end Erdos3

end

end OAI
