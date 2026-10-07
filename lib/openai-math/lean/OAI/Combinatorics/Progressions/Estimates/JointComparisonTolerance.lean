import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget

namespace OAI

section

namespace Erdos3

noncomputable def jointQuadratureAccuracy (n : ℕ) (G δ : ℝ) : ℝ :=
  δ / (2*(1+G)^n)

theorem jointQuadratureAccuracy_pos (n : ℕ) {G δ : ℝ} (hG : 0 ≤ G) (hδ : 0 < δ) :
    0 < jointQuadratureAccuracy n G δ := by unfold jointQuadratureAccuracy; positivity

theorem jointComparisonError_le (n : ℕ) {C G ε η δ : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he : ε ≤ vectorSpatialAccuracy n (2+G*C) δ)
    (hη : η ≤ jointQuadratureAccuracy n G δ) :
    n*ε*(1+G*C+ε)^n+G^n*η ≤ δ := by
  have hGC := mul_nonneg hG hC
  have hA : 1 ≤ 2+G*C := by linarith
  have hacc := vectorSpatialAccuracy_pos n (show 0 < 2+G*C by positivity) hδ
  have hε1 := he.trans ((vectorSpatialAccuracy_le n hA hδ.le).trans hδ1)
  have hp : (1+G*C+ε)^n ≤ (2+G*C)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hfirst : n*ε*(1+G*C+ε)^n ≤ δ/2 := by
    have hb : n*ε*(1+G*C+ε)^n ≤ n*vectorSpatialAccuracy n (2+G*C) δ*(2+G*C)^n :=
      mul_le_mul (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n)) hp
        (by positivity) (by positivity)
    have hh := vectorSpatialAccuracy_error n (show 0 < 2+G*C by positivity) hδ.le
    nlinarith
  have hsecond : G^n*η ≤ δ/2 := by
    calc
      _ ≤ G^n*jointQuadratureAccuracy n G δ := mul_le_mul_of_nonneg_left hη (pow_nonneg hG n)
      _ ≤ (1+G)^n*jointQuadratureAccuracy n G δ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hG (by linarith) n) (jointQuadratureAccuracy_pos n hG hδ).le
      _ = δ/2 := by
        unfold jointQuadratureAccuracy
        have hz : (1+G)^n ≠ 0 := by positivity
        field_simp
  linarith

theorem jointQuadratureAccuracy_inverse_le_exp (n : ℕ) {G δ P : ℝ}
    (hG : 0 ≤ G) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hGP : G ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    (jointQuadratureAccuracy n G δ)⁻¹ ≤ Real.exp ((n+1)*(P+1)+n+1) := by
  have hA : 1+G ≤ Real.exp (P+1) := by
    rw [Real.exp_add]
    have hh := Real.one_le_exp_iff.mpr hP
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.exp_pos P]
  have hi := vectorSpatialAccuracy_inverse_le_exp n (show 0 < 1+G by positivity) hδ hA
    (hδP.trans (Real.exp_le_exp.mpr (by linarith : P ≤ P+1)))
  apply le_trans _ hi
  unfold jointQuadratureAccuracy vectorSpatialAccuracy
  rw [inv_div, inv_div]
  apply div_le_div_of_nonneg_right _ hδ.le
  have hp : 0 ≤ (1+G)^n := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Erdos3

end

end OAI
