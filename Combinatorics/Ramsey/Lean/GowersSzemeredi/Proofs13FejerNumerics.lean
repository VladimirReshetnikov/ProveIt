import GowersSzemeredi.Proofs13FejerSignal

/-! Choosing an even kernel length avoids rounding loss in the elementary
32-label signal estimate. These identities retain its precise constants. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejer_signal_32_even {M : Nat} (hM : 0 < M) :
    ((((2 * M : Nat) : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33 =
      ((2 : Real) ^ 64)⁻¹ * ((M : Real) ^ 31)⁻¹ := by
  have hm : (M : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  push_cast
  field_simp

theorem fejer_signal_32_baseline_ratio {M : Nat} (hM : 0 < M) :
    ((((2 * M : Nat) : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33 =
      ((M : Real) / (2 : Real) ^ 32) * ((((2 * M : Nat) : Real))⁻¹) ^ 32 := by
  have hm : (M : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  push_cast
  field_simp

theorem fejer_baseline_32_le_signal {M : Nat} (hM : 0 < M) (t : Real)
    (hscale : (2 : Real) ^ 32 ≤ t * (M : Real)) :
    ((((2 * M : Nat) : Real))⁻¹) ^ 32 ≤
      t * (((((2 * M : Nat) : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33) := by
  rw [fejer_signal_32_baseline_ratio hM]
  have hs : 1 ≤ t * ((M : Real) / (2 : Real) ^ 32) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (by positivity : (0 : Real) < 2 ^ 32)).mpr (by simpa using hscale)
  have hb : (0 : Real) ≤ ((((2 * M : Nat) : Real))⁻¹) ^ 32 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hs hb]

end LeanProofs.GowersSzemeredi
