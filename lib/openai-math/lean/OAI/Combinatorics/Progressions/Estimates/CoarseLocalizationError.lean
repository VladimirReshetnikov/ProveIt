import OAI.Combinatorics.Progressions.Polynomial.LocalizationPolynomialScales

namespace OAI

section

namespace Erdos3

theorem coarse_localization_error {U B C D H T M r δ L η : ℝ}
    (hU : 1 ≤ U) (hB0 : 0 ≤ B) (_hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hH0 : 0 ≤ H) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hB : B ≤ U) (hC : C ≤ U) (hD : D ≤ U) (hH : H ≤ U) (hT : T ≤ U) (hM : M ≤ U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hL : 0 < L) (hη : 0 ≤ η)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ U) :
    B * (A * r + (D + H / r) * (M / L)) + C * ((T + B * H / r) * δ + B * η) ≤
      U ^ 2 * r + 2 * U ^ 3 / (r * L) + (2 * U ^ 3 / r) * δ + U ^ 2 * η := by
  have hU0 : 0 < U := by linarith
  have hsum : D + H / r ≤ 2 * U / r := by
    apply (le_div_iff₀ hr).mpr
    have hDr : D * r ≤ U := (mul_le_mul_of_nonneg_right hD hr.le).trans
      (mul_le_of_le_one_right hU0.le hr1)
    have he : (D + H / r) * r = D * r + H := by field_simp
    rw [he]
    linarith
  have hsum' : T + B * H / r ≤ 2 * U ^ 2 / r := by
    apply (le_div_iff₀ hr).mpr
    have hTr : T * r ≤ U := (mul_le_mul_of_nonneg_right hT hr.le).trans
      (mul_le_of_le_one_right hU0.le hr1)
    have hBH : B * H ≤ U ^ 2 := by nlinarith [mul_le_mul hB hH hH0 hU0.le]
    have he : (T + B * H / r) * r = T * r + B * H := by field_simp
    rw [he]
    nlinarith
  calc
    _ ≤ U * (U * r + (2 * U / r) * (U / L)) + U * ((2 * U ^ 2 / r) * δ + U * η) := by
      gcongr
    _ = _ := by field_simp; ring

theorem polynomial_localization_error {U B C D H T M L η ε W : ℝ}
    (hU : 1 ≤ U) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hH0 : 0 ≤ H) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hB : B ≤ U) (hC : C ≤ U) (hD : D ≤ U) (hH : H ≤ U) (hT : T ≤ U) (hM : M ≤ U)
    (hL : 0 < L) (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ L) {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ U) :
    B * (A * localizationRadius U ε + (D + H / localizationRadius U ε) * (M / L)) +
      C * ((T + B * H / localizationRadius U ε) * localizationMesh U ε + B * η) ≤ ε + U ^ 2 * η := by
  have hc := coarse_localization_error hU hB0 hC0 hD0 hH0 hT0 hM0 hB hC hD hH hT hM
    (localizationRadius_pos hU hε) (localizationRadius_le_one hU hε1)
    (localizationMesh_pos hU hε).le hL hη hA0 hA
  rw [localizationRadius_scale hU, localizationMesh_scale hU hε] at hc
  have hi := localization_inverse_length_error hU hε hW hL hlen
  linarith

end Erdos3

end

end OAI
