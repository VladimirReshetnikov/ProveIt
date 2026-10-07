import OAI.Combinatorics.Progressions.Linear.RationalMatrixSeparation

namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem real_matrix_specified_denominator_grid (M : Matrix ι κ ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : κ → ℝ) (hx : x ∈ realDenominatorGrid l) :
    M *ᵥ x ∈ realDenominatorGrid (D * l) := by
  classical
  choose A hA using hM
  obtain ⟨z, hz⟩ := hx
  refine ⟨A *ᵥ z, funext fun i => ?_⟩
  change (((A *ᵥ z) i : ℤ) : ℝ) = ((D * l : ℕ) : ℝ) * (M *ᵥ x) i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z j : ℝ) = (l : ℝ) * x j := congrFun hz j
  rw [← hA i j, hj]
  ring

theorem real_matrix_complement_specified_denominator_grid
    (M : Matrix ι ι ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    x - M *ᵥ x ∈ realDenominatorGrid (D * l) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := real_matrix_specified_denominator_grid M D l hM x ⟨z, hz⟩
  refine ⟨fun i => (D : ℤ) * z i - w i, funext fun i => ?_⟩
  have hzi : (z i : ℝ) = (l : ℝ) * x i := congrFun hz i
  have hwi : (w i : ℝ) = ((D * l : ℕ) : ℝ) * (M *ᵥ x) i := congrFun hw i
  change (((D : ℤ) * z i - w i : ℤ) : ℝ) =
    ((D * l : ℕ) : ℝ) * (x i - (M *ᵥ x) i)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, hzi, hwi]
  ring

theorem real_matrix_complement_linearMap_specified_denominator_grid
    (M : Matrix ι ι ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) - M.mulVecLin) x ∈ realDenominatorGrid (D * l) := by
  exact real_matrix_complement_specified_denominator_grid M D l hM x hx

end Erdos3

end

end OAI
