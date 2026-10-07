import Mathlib.Data.Matrix.ColumnRowPartitioned
import OAI.Combinatorics.Progressions.Estimates.SmoothProfileReindexing

namespace OAI

section

namespace Erdos3

open scoped Matrix

noncomputable def smoothMatrixImagePMF {O J : Type*} [Fintype J]
    (A : Matrix O J ℤ) (S : J → ℝ) (hS : ∀ j, 0 < S j) : PMF (O → ℤ) :=
  (smoothProductPMF S hS).map (fun z => A *ᵥ z)

noncomputable def smoothIntegerImagePMF {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) : PMF (I → ℤ) :=
  integerImagePMF A B (smoothSplitProfile J I)
    (fun p => (smoothSplitProfile_range J I p).1) S T hS hT
    (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT)

theorem smoothIntegerImagePMF_eq_matrix {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    smoothIntegerImagePMF A B S T hS hT =
      smoothMatrixImagePMF (Matrix.fromCols A B) (Sum.elim S T) (fun k => Sum.rec hS hT k) := by
  unfold smoothIntegerImagePMF integerImagePMF smoothMatrixImagePMF
  rw [← smoothSplit_inputPMF_join S T hS hT, PMF.map_comp]
  congr 1
  funext p
  simp only [Function.comp_def, Matrix.fromCols_mulVec, Sum.elim_inl, Sum.elim_inr]

theorem smoothMatrixImagePMF_reindex {O I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix O J ℤ) (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    smoothMatrixImagePMF (A.submatrix id e) (S ∘ e) (fun i => hS (e i)) =
      smoothMatrixImagePMF A S hS := by
  unfold smoothMatrixImagePMF
  rw [← smoothProductPMF_reindex e S hS, PMF.map_comp]
  congr 1
  funext z
  exact Matrix.submatrix_mulVec_equiv A z id e

end Erdos3

end

end OAI
