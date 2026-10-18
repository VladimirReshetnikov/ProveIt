import GowersSzemeredi.Proofs18QuadraticIterationParameters

/-! Declarations of `Proofs18QuadraticIterationParameters` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- All density dependence of the fixed uniformity parameter is polynomial. -/
theorem intervalQuadraticUniformityParameter_inv_upper {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (intervalQuadraticUniformityParameter delta)⁻¹ ≤ (2 / delta) ^ (120 : Nat) ∧
      2 / intervalQuadraticUniformityParameter delta ≤ (2 / delta) ^ (121 : Nat) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hd : 1 ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by simpa using hδone)
  have hbase : (delta ^ 4 / 32768)⁻¹ ≤ (2 / delta) ^ (15 : Nat) := by
    calc
      _ = 32768 * (delta⁻¹) ^ (4 : Nat) := by rw [inv_div, div_eq_mul_inv, inv_pow]
      _ ≤ 32768 * (delta⁻¹) ^ (15 : Nat) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by norm_num : 4 ≤ 15)) (by norm_num)
      _ = _ := by rw [div_pow, div_eq_mul_inv, inv_pow]; norm_num
  have hinv : (intervalQuadraticUniformityParameter delta)⁻¹ ≤ (2 / delta) ^ (120 : Nat) := by
    unfold intervalQuadraticUniformityParameter
    rw [← inv_pow]
    calc
      _ ≤ ((2 / delta) ^ (15 : Nat)) ^ (8 : Nat) := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [← pow_mul]
  refine ⟨hinv, ?_⟩
  have hu : 2 ≤ 2 / delta := (le_div_iff₀ hδ).mpr (by linarith)
  calc
    _ = 2 * (intervalQuadraticUniformityParameter delta)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (2 / delta) * (2 / delta) ^ (120 : Nat) :=
      mul_le_mul hu hinv (by positivity) (by positivity)
    _ = _ := (pow_succ' _ 120).symm

end LeanProofs.GowersSzemeredi
