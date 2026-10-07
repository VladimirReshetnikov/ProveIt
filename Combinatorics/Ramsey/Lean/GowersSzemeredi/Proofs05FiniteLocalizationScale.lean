import GowersSzemeredi.Proofs05FiniteLocalizationExponentBudget

/-! The exact-target residue chunking budget for threshold-free localization. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

def finiteLocalizationChunk (k L : Nat) : Nat :=
  (2 * (2 * L)) ^ (polynomialPartitionConstant k / 2)

def finiteLocalizationPrecision (k L H : Nat) : Nat := 2 ^ (k + 6) * L * H ^ k

theorem finiteLocalizationChunk_bounds {k L : Nat} (hL : 2 ≤ L) :
    1 ≤ finiteLocalizationChunk k L ∧
      finiteLocalizationChunk k L ≤ (2 * L) ^ polynomialPartitionConstant k := by
  constructor
  · exact one_le_pow₀ (by omega)
  · unfold finiteLocalizationChunk
    calc
      _ ≤ ((2 * L) ^ 2) ^ (polynomialPartitionConstant k / 2) := by gcongr; nlinarith
      _ = (2 * L) ^ (2 * (polynomialPartitionConstant k / 2)) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem finiteLocalizationPrecision_ge_two {k L H : Nat} (hL : 2 ≤ L) (hH : 1 ≤ H) :
    2 ≤ finiteLocalizationPrecision k L H := by
  have hpow : 1 ≤ H ^ k := one_le_pow₀ hH
  have htwo : 1 ≤ 2 ^ (k + 6) := one_le_pow₀ (by omega)
  unfold finiteLocalizationPrecision
  nlinarith [Nat.mul_le_mul htwo hL]

theorem finiteLocalization_chunk_budget {k L : Nat} (hk : 2 ≤ k) (hL : 2 ≤ L) :
    let H := finiteLocalizationChunk k L
    let R := finiteLocalizationPrecision (k + 1) L H
    finiteRecurrenceSample (k + 1) R * (H + 1) ^ 2 ≤
      (2 * L) ^ (polynomialPartitionConstant (k + 1) / 2) := by
  let H := finiteLocalizationChunk k L
  let R := finiteLocalizationPrecision (k + 1) L H
  let K := polynomialPartitionConstant k
  let A := finiteRecurrenceConstantExponent (k + 1)
  let B := finiteRecurrenceRadiusExponent (k + 1)
  have hH := finiteLocalizationChunk_bounds (k := k) hL
  have hb : 1 ≤ 2 * L := by omega
  have hR : R ≤ (2 * L) ^ ((k + 1) + 7 + (k + 1) * K) := by
    calc
      _ ≤ (2 * L) ^ ((k + 1) + 6) * (2 * L) * ((2 * L) ^ K) ^ (k + 1) := by
        dsimp [R, finiteLocalizationPrecision]
        gcongr
        · omega
        · omega
        · exact hH.2
      _ = _ := by
        rw [← pow_mul, ← pow_succ, ← pow_add]
        congr 1
        dsimp [K]
        ring
  have hround : H + 1 ≤ (2 * L) ^ (K + 1) := by
    calc
      _ ≤ 2 * H := by have := hH.1; change 1 ≤ H at this; omega
      _ ≤ (2 * L) * (2 * L) ^ K := Nat.mul_le_mul (by omega) hH.2
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ (2 ^ A * R ^ B) * ((2 * L) ^ (K + 1)) ^ 2 :=
      Nat.mul_le_mul (finiteRecurrenceSample_le_power _ _) (Nat.pow_le_pow_left hround 2)
    _ ≤ ((2 * L) ^ A * ((2 * L) ^ ((k + 1) + 7 + (k + 1) * K)) ^ B) *
        ((2 * L) ^ (K + 1)) ^ 2 := by gcongr; omega
    _ = (2 * L) ^ (A + ((k + 1) + 7) * B + ((k + 1) * B + 2) * K + 2) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right hb (finiteLocalization_exponent_budget hk)

end LeanProofs.GowersSzemeredi
