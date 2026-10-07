import OAI.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates

namespace OAI

section

namespace Erdos3

open scoped Matrix

def realSpanIntegerRowBound (n m H : ℕ) : ℕ :=
  imageDefiningHeight n m H ^ (m * m) * imageDefiningHeight n m H

theorem exists_real_span_integer_defining_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ C : Matrix ι ι ℤ,
      (∀ i j, |(C i j : ℝ)| ≤
        (realSpanIntegerRowBound (Fintype.card κ) (Fintype.card ι) H : ℝ)) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (C i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨Q, hQ, hker⟩ := exists_real_span_defining_matrix A hH hA
  have hcast (i j : ι) :
      (clearedMatrix Q i j : ℝ) = (matrixDenominator Q : ℝ) * (Q i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast Q) i) j
    change (clearedMatrix Q i j : ℚ) = (matrixDenominator Q : ℚ) * Q i j at h
    exact_mod_cast h
  refine ⟨clearedMatrix Q, ?_, ?_⟩
  · intro i j
    rw [hcast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hd := Nat.cast_le (α := ℝ).mpr (matrixDenominator_le Q hQ)
    have hentry := (hQ i j).abs_real_le
    exact (mul_le_mul hd hentry (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq
      (by simp only [realSpanIntegerRowBound, Nat.cast_mul])
  · have hden : (matrixDenominator Q : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (matrixDenominator_pos Q)).ne'
    have hmatrix : Matrix.of (fun i j => (clearedMatrix Q i j : ℝ)) =
        (matrixDenominator Q : ℝ) • Matrix.of (fun i j => (Q i j : ℝ)) := by
      ext i j
      exact hcast i j
    calc
      LinearMap.ker (Matrix.mulVecLin (fun i j => (clearedMatrix Q i j : ℝ))) =
          LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) := by
        ext x
        change (Matrix.of (fun i j => (clearedMatrix Q i j : ℝ)) *ᵥ x = 0) ↔
          (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0)
        rw [hmatrix, Matrix.smul_mulVec]
        simp [hden]
      _ = _ := hker

end Erdos3

end

end OAI
