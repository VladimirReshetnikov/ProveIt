import GowersSzemeredi.Proofs05AffineLocalizationScale
import GowersSzemeredi.Proofs05QuadraticRecurrenceBudget

/-! The quadratic phase partition's finite budget. The square in the
chunking threshold pays for the existing exact-target residue partition.
The recurrence input itself remains a separate proof obligation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticLocalizationChunk (L : Nat) : Nat := 1024 * (2 * L) ^ 3
def quadraticLocalizationPrecision (L : Nat) : Nat :=
  256 * L * quadraticLocalizationChunk L ^ 2

theorem quadraticLocalizationChunk_formula (L : Nat) :
    quadraticLocalizationChunk L = 2 ^ 13 * L ^ 3 := by
  unfold quadraticLocalizationChunk
  ring

theorem quadraticLocalizationPrecision_formula (L : Nat) :
    quadraticLocalizationPrecision L = 2 ^ 34 * L ^ 7 := by
  unfold quadraticLocalizationPrecision
  rw [quadraticLocalizationChunk_formula]
  ring

set_option exponentiation.threshold 1024 in
theorem quadraticLocalization_sample_formula (L : Nat) :
    2 ^ 256 * quadraticLocalizationPrecision L ^ 16 = 2 ^ 800 * L ^ 112 := by
  rw [quadraticLocalizationPrecision_formula]
  ring

theorem quadraticLocalization_precision_ge_two {L : Nat} (hL : 2 ≤ L) :
    2 ≤ quadraticLocalizationPrecision L := by
  have hpow : 1 ≤ L ^ 7 := one_le_pow₀ (by omega)
  rw [quadraticLocalizationPrecision_formula]
  have h := Nat.mul_le_mul_left (2 ^ 34) hpow
  norm_num only [mul_one] at h
  omega

set_option exponentiation.threshold 1024 in
theorem quadraticLocalization_chunk_budget {L : Nat} (hL : 2 ≤ L) :
    (2 ^ 256 * quadraticLocalizationPrecision L ^ 16) *
        (quadraticLocalizationChunk L + 1) ^ 2 ≤ (2 * L) ^ (polynomialPartitionConstant 2 / 2) := by
  have hL1 : 1 ≤ L := by omega
  have hH : 1 ≤ quadraticLocalizationChunk L := by
    rw [quadraticLocalizationChunk_formula]
    have hpow : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    nlinarith
  have hround : quadraticLocalizationChunk L + 1 ≤ 2 * quadraticLocalizationChunk L := by omega
  have hK : polynomialPartitionConstant 2 / 2 = 1024 := by norm_num [polynomialPartitionConstant]
  rw [hK]
  calc
    _ ≤ (2 ^ 256 * quadraticLocalizationPrecision L ^ 16) *
        (2 * quadraticLocalizationChunk L) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hround 2)
    _ = 2 ^ 828 * L ^ 118 := by
      rw [quadraticLocalization_sample_formula, quadraticLocalizationChunk_formula]
      ring
    _ ≤ 2 ^ 946 * L ^ 946 := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by omega) (by omega))
      (Nat.pow_le_pow_right hL1 (by omega))
    _ = (2 * L) ^ 946 := (mul_pow _ _ _).symm
    _ ≤ (2 * L) ^ 1024 := Nat.pow_le_pow_right (by omega) (by omega)

theorem quadraticLocalization_leading_error {L : Nat} (hL : 2 ≤ L) :
    2 * Real.pi * (2 * (quadraticLocalizationChunk L : Real)) ^ 2 /
        quadraticLocalizationPrecision L ≤ 1 / (8 * L) := by
  have hL0 : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hH : (0 : Real) < quadraticLocalizationChunk L := by
    unfold quadraticLocalizationChunk
    positivity
  have hR : (0 : Real) < quadraticLocalizationPrecision L := by
    exact_mod_cast (show 0 < quadraticLocalizationPrecision L from
      lt_of_lt_of_le (by omega) (quadraticLocalization_precision_ge_two hL))
  apply (div_le_div_iff₀ hR (by positivity)).mpr
  have hpi := mul_le_mul_of_nonneg_right Real.pi_le_four
    (show 0 ≤ (64 : Real) * L * (quadraticLocalizationChunk L : Real) ^ 2 by positivity)
  simp only [quadraticLocalizationPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, one_mul]
  nlinarith [hpi]

end LeanProofs.GowersSzemeredi
