import OAI.Combinatorics.Progressions.Estimates.ArrayFunctionalSection
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem clearedMatrix_real_entry {I S : Type*} [Fintype I] [Fintype S]
    [DecidableEq I] [DecidableEq S] (T : Matrix I S ℚ) (i : I) (s : S) :
    ((clearedMatrix T i s : ℤ) : ℝ) = (matrixDenominator T : ℝ) * (T i s : ℝ) := by
  have h : ((clearedMatrix T i s : ℤ) : ℚ) = (matrixDenominator T : ℚ) * T i s :=
    congrFun (congrFun (clearedMatrix_cast T) i) s
  exact_mod_cast h

noncomputable def sectionIntegerFrequency {I S J : Type*} [Fintype I] [Fintype S]
    [DecidableEq I] [DecidableEq S] (T : Matrix I S ℚ) (frequency : Matrix I J ℤ) :
    Matrix S J ℤ := (clearedMatrix T)ᵀ * frequency

theorem sectionIntegerFrequency_real {I S J : Type*} [Fintype I] [Fintype S]
    [DecidableEq I] [DecidableEq S] (T : Matrix I S ℚ) (frequency : Matrix I J ℤ) :
    Matrix.of (fun s a => ((sectionIntegerFrequency T frequency s a : ℤ) : ℝ)) =
      (matrixDenominator T : ℝ) •
        ((Matrix.of (fun i s => (T i s : ℝ)))ᵀ * Matrix.of (fun i a => (frequency i a : ℝ))) := by
  funext s a
  change ((∑ i, clearedMatrix T i s * frequency i a : ℤ) : ℝ) =
    (matrixDenominator T : ℝ) * (∑ i, (T i s : ℝ) * (frequency i a : ℝ))
  simp only [Int.cast_sum, Int.cast_mul, clearedMatrix_real_entry, Finset.mul_sum, mul_assoc]

theorem sectionIntegerFrequency_bound {I S J : Type*} [Fintype I] [Fintype S]
    [DecidableEq I] [DecidableEq S] (T : Matrix I S ℚ) (frequency : Matrix I J ℤ)
    {C H : ℝ} (hH : 0 ≤ H)
    (hfrequency : ∀ i a, |(frequency i a : ℝ)| ≤ C)
    (hT : ∀ i s, |(T i s : ℝ)| ≤ H) (s : S) (a : J) :
    |(sectionIntegerFrequency T frequency s a : ℝ)| ≤
      (Fintype.card I : ℝ) * C * (matrixDenominator T : ℝ) * H := by
  change |((∑ i, clearedMatrix T i s * frequency i a : ℤ) : ℝ)| ≤ _
  rw [Int.cast_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : I, (matrixDenominator T : ℝ) * H * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.cast_mul, abs_mul, clearedMatrix_real_entry, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ matrixDenominator T from Nat.cast_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hT i s) (Nat.cast_nonneg _))
        (hfrequency i a) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hH)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
