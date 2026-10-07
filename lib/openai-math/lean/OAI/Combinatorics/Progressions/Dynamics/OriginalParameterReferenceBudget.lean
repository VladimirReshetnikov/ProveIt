import OAI.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget

namespace OAI

section

namespace Erdos3

theorem affineReferenceInput_le_original_power (epsilon : ℝ) {U p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hU : 0 ≤ U) (hUp : U ≤ (p + 2) ^ d) :
    affineReferenceInput epsilon U ≤ (p + 2) ^ ((d + 4) * (affineReferencePower epsilon + 1)) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ d := one_le_pow₀ hbase
  have h80 : (80 : ℝ) ≤ (p + 2) ^ 4 := by
    calc
      80 ≤ (4 : ℝ) ^ 4 := by norm_num
      _ ≤ (p + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hscale : 20 * (U + 3) ≤ (p + 2) ^ (d + 4) := by
    calc
      _ ≤ 80 * (p + 2) ^ d := by nlinarith
      _ ≤ (p + 2) ^ 4 * (p + 2) ^ d :=
        mul_le_mul_of_nonneg_right h80 (by positivity)
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ (20 * (U + 3)) ^ (affineReferencePower epsilon + 1) :=
      affineReferenceInput_le_envelope epsilon hU
    _ ≤ ((p + 2) ^ (d + 4)) ^ (affineReferencePower epsilon + 1) :=
      pow_le_pow_left₀ (by positivity) hscale _
    _ = _ := by rw [pow_mul]

theorem affineCommonReferenceBudget_le_original_power (E : ℕ) (epsilon : ℝ) {U p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hU : 0 ≤ U) (hUp : U ≤ (p + 2) ^ d) :
    affineCommonReferenceBudget E epsilon U ≤
      (p + 2) ^ (((d + 4) * (affineReferencePower epsilon + 1) + 1) * E + 1) := by
  let k := (d + 4) * (affineReferencePower epsilon + 1)
  have href : affineReferenceInput epsilon U ≤ (p + 2) ^ k :=
    affineReferenceInput_le_original_power epsilon hp hU hUp
  have hbase : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ k := one_le_pow₀ hbase
  have hsum : affineReferenceInput epsilon U + 2 ≤ (p + 2) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith
  have hnonneg : 0 ≤ affineReferenceInput epsilon U + 2 := by
    linarith [(affineReferenceInput_bounds epsilon hU).1]
  change 2 * (affineReferenceInput epsilon U + 2) ^ E ≤ (p + 2) ^ ((k + 1) * E + 1)
  calc
    _ ≤ 2 * ((p + 2) ^ (k + 1)) ^ E :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hsum E) (by norm_num)
    _ = 2 * (p + 2) ^ ((k + 1) * E) := by rw [pow_mul]
    _ ≤ (p + 2) ^ ((k + 1) * E) * (p + 2) := by
      nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) ((k + 1) * E)]
    _ = _ := by rw [pow_succ]

end Erdos3

end

end OAI
