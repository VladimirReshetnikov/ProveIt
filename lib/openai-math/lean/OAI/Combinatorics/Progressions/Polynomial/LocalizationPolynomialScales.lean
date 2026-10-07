import Mathlib

namespace OAI

section

namespace Erdos3

noncomputable def localizationRadius (U ε : ℝ) : ℝ := ε / (8 * U ^ 2)
noncomputable def localizationMesh (U ε : ℝ) : ℝ := ε ^ 2 / (128 * U ^ 5)
noncomputable def localizationLengthBudget (U ε W : ℝ) : ℝ := 256 * U ^ 6 * W / ε ^ 2

theorem localizationRadius_pos {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    0 < localizationRadius U ε := by unfold localizationRadius; positivity

theorem localizationMesh_pos {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    0 < localizationMesh U ε := by unfold localizationMesh; positivity

theorem localizationRadius_le_one {U ε : ℝ} (hU : 1 ≤ U) (hε1 : ε ≤ 1) :
    localizationRadius U ε ≤ 1 := by
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  unfold localizationRadius
  apply (div_le_one (by positivity)).mpr
  linarith

theorem localizationMesh_le_one {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    localizationMesh U ε ≤ 1 := by
  have hp : 1 ≤ U ^ 5 := one_le_pow₀ hU
  unfold localizationMesh
  apply (div_le_one (by positivity)).mpr
  nlinarith

theorem localizationRadius_scale {U ε : ℝ} (hU : 1 ≤ U) :
    U ^ 2 * localizationRadius U ε = ε / 8 := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius
  field_simp

theorem localizationMesh_scale {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    (2 * U ^ 3 / localizationRadius U ε) * localizationMesh U ε = ε / 8 := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius localizationMesh
  field_simp
  ring

theorem localizationMesh_length {U ε W : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    localizationMesh U ε * localizationLengthBudget U ε W = 2 * U * W := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationMesh localizationLengthBudget
  field_simp
  ring

theorem localizationRadius_length {U ε W : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    localizationRadius U ε * localizationLengthBudget U ε W * ε = 32 * U ^ 4 * W := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius localizationLengthBudget
  field_simp
  ring

theorem localizationMesh_margin {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    U * localizationMesh U ε < localizationRadius U ε := by
  have hU0 : 0 < U := by linarith
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have he : U * localizationMesh U ε = localizationRadius U ε * (ε / (16 * U ^ 2)) := by
    unfold localizationRadius localizationMesh
    field_simp
    ring
  rw [he]
  apply mul_lt_of_lt_one_right (localizationRadius_pos hU hε)
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem localizationLengthBudget_ge_square {U ε W : ℝ}
    (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W) :
    U ^ 2 ≤ localizationLengthBudget U ε W := by
  have hp : U ^ 2 ≤ U ^ 6 := pow_le_pow_right₀ hU (by decide : 2 ≤ 6)
  have he : ε ^ 2 ≤ 1 := by nlinarith
  have hU6 : 0 ≤ U ^ 6 := by positivity
  have hprod : U ^ 6 ≤ U ^ 6 * W := le_mul_of_one_le_right hU6 hW
  unfold localizationLengthBudget
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hsmall := mul_le_of_le_one_right (sq_nonneg U) he
  nlinarith

theorem localization_inverse_length_error {U ε W L : ℝ}
    (hU : 1 ≤ U) (hε : 0 < ε) (hW : 1 ≤ W) (hL : 0 < L)
    (hlen : localizationLengthBudget U ε W ≤ L) :
    2 * U ^ 3 / (localizationRadius U ε * L) ≤ ε / 4 := by
  have hr := localizationRadius_pos hU hε
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hr.le) hε.le
  rw [localizationRadius_length hU hε] at hmul
  have hp : U ^ 3 ≤ U ^ 4 := pow_le_pow_right₀ hU (by decide : 3 ≤ 4)
  have hprod : U ^ 4 ≤ U ^ 4 * W := le_mul_of_one_le_right (by positivity) hW
  have hp0 : 0 ≤ U ^ 3 := by positivity
  apply (div_le_iff₀ (mul_pos hr hL)).mpr
  nlinarith

end Erdos3

end

end OAI
