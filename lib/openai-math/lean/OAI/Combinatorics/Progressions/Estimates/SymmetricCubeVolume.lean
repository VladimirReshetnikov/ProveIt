import OAI.Combinatorics.Progressions.Probability.SymmetricCubeMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal BigOperators

def symmetricUnitBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)

theorem symmetricUnitBox_mem (n : ℕ) (x : Fin n → ℝ) :
    x ∈ symmetricUnitBox n ↔ ∀ i, |x i| ≤ 1 := by
  simp only [symmetricUnitBox, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc, abs_le]

theorem symmetricCubeMeasure_eq_smul_restrict (n : ℕ) :
    symmetricCubeMeasure n = (1 / 2 : ℝ≥0∞) ^ n • volume.restrict (symmetricUnitBox n) := by
  unfold symmetricCubeMeasure
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  change (1 / 2 : ℝ≥0∞) ^ n * volume ((Set.pi Set.univ s) ∩
    (Set.pi Set.univ fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) = _
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [symmetricScalarMeasure, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem symmetricUnitBox_volume_inter (n : ℕ) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    volume.real (symmetricUnitBox n ∩ s) = (2 : ℝ) ^ n * (symmetricCubeMeasure n).real s := by
  rw [symmetricCubeMeasure_eq_smul_restrict, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs, ENNReal.toReal_pow]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [← mul_assoc, ← mul_pow]
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]
  rw [Set.inter_comm]

end Erdos3

end

end OAI
