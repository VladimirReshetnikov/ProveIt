import OAI.Combinatorics.Progressions.Probability.SelectedDensityNormalization

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem selectedKernel_matrix_reconstruct {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (M : Matrix I J R) (s : I ↪ J) (a : J → R) :
    M *ᵥ a = M.submatrix id s *ᵥ (fun i => a (s i)) +
      remainingMatrixColumns M s *ᵥ (fun j => a j.val) := by
  have h := Matrix.submatrix_mulVec_equiv M (a ∘ selectedColumnEquiv s) id (selectedColumnEquiv s)
  rw [← selectedMatrix_fromCols, Matrix.fromCols_mulVec] at h
  have hl (i : I) : selectedColumnEquiv s (Sum.inl i) = s i := rfl
  have hr (j : UnselectedColumn s) : selectedColumnEquiv s (Sum.inr j) = j.val := rfl
  simpa only [Function.comp_def, Equiv.apply_symm_apply, id_eq, hl, hr] using h.symm

theorem normalizedKernel_reconstruct {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (a : J → ℝ) :
    matrixSupCLM (normalizedIntegerColumns M S P) a =
      normalizedPivotEquiv (M.submatrix id s) hM (fun i => S (s i)) P (fun i => hS (s i)) hP
        (fun i => a (s i)) +
      matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) P)
        (fun j => a j.val) := by
  change _ =
    (normalizedPivotEquiv (M.submatrix id s) hM (fun i => S (s i)) P (fun i => hS (s i)) hP).toContinuousLinearMap
      (fun i => a (s i)) + _
  rw [normalizedPivotEquiv_coe, normalized_remainingMatrixColumns]
  simpa only [matrixSupCLM_apply, normalizedIntegerColumns_submatrix] using
    selectedKernel_matrix_reconstruct (normalizedIntegerColumns M S P) s a

end Erdos3

end

end OAI
