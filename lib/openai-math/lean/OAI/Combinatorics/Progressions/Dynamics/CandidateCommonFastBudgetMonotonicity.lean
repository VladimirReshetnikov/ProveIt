import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry

namespace OAI

section

namespace Erdos3

theorem allocatedCandidateCommonFastSectionInput_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastSectionInput p ≤ allocatedCandidateCommonFastSectionInput q := by
  unfold allocatedCandidateCommonFastSectionInput
  exact add_le_add
    (pow_le_pow_left₀ (by positivity : 0 ≤ p + 2) (add_le_add hpq (le_refl 2)) 4) (le_refl 1)

theorem allocatedCandidateCommonFastGeometryLog_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastGeometryLog p ≤ allocatedCandidateCommonFastGeometryLog q := by
  have hinput := allocatedCandidateCommonFastSectionInput_mono hp hpq
  have hnonneg := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  unfold allocatedCandidateCommonFastGeometryLog
  exact add_le_add
    (pow_le_pow_left₀ (by positivity : 0 ≤ allocatedCandidateCommonFastSectionInput p + 2)
      (add_le_add hinput (le_refl 2)) 47) (le_refl 1)

theorem NilpotentLieFiltration.pointwiseFastSectionInput_mono (s : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    NilpotentLieFiltration.pointwiseFastSectionInput s p ≤
      NilpotentLieFiltration.pointwiseFastSectionInput s q := by
  have hbase : p + ((s : ℝ) + 3) ≤ q + ((s : ℝ) + 3) := add_le_add hpq le_rfl
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ p + ((s : ℝ) + 3)) hbase (s + 3)
  have hsquare := pow_le_pow_left₀
    (by positivity : 0 ≤ (p + ((s : ℝ) + 3)) ^ (s + 3)) hpow 2
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hpow (by norm_num)) hsquare) hpq

theorem allocatedCandidateCommonFastBudget_mono (s : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastBudget s p ≤ allocatedCandidateCommonFastBudget s q := by
  exact add_le_add (allocatedCandidateCommonFastGeometryLog_mono hp hpq)
    (NilpotentLieFiltration.pointwiseFastSectionInput_mono s hp hpq)

theorem quotientInducedMarkHeightBudget_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    quotientInducedMarkHeightBudget p ≤ quotientInducedMarkHeightBudget q := by
  have hseven := pow_le_pow_left₀ (by positivity : 0 ≤ p + 3) (add_le_add hpq (le_refl 3)) 7
  unfold quotientInducedMarkHeightBudget
  exact pow_le_pow_left₀ (by positivity : 0 ≤ p + (p + 3) ^ 7 + 3)
    (add_le_add (add_le_add hpq hseven) (le_refl 3)) 4

end Erdos3

end

end OAI
