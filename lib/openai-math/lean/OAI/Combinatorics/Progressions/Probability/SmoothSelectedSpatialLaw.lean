import OAI.Combinatorics.Progressions.Lattices.SmoothIntegerImage

namespace OAI

section

namespace Erdos3

noncomputable def selectedFullSpatialColumnEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) (N : Type*) :
    (Unit ⊕ I) ⊕ (UnselectedColumn s ⊕ N) ≃ (Unit ⊕ J) ⊕ N :=
  (Equiv.sumAssoc (Unit ⊕ I) (UnselectedColumn s) N).symm.trans
    (Equiv.sumCongr (selectedSpatialColumnEquiv s) (Equiv.refl N))

theorem selectedFullSpatial_fromCols {I J N : Type*} [Fintype I]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ) :
    Matrix.fromCols (selectedSpatialPivot root D s)
        (Matrix.fromCols (selectedSpatialFreeColumns root D s) C) =
      (Matrix.fromCols (rootDifferenceMatrix root D) C).submatrix id
        (selectedFullSpatialColumnEquiv s N) := by
  ext i k
  cases k with
  | inl k => cases k <;> cases i <;> rfl
  | inr k => cases k <;> cases i <;> rfl

theorem selectedFullSpatial_scale {I J N : Type*} [Fintype I]
    (s : I ↪ J) (H L : ℝ) (Q : N → ℝ) :
    Sum.elim (spatialPivotScale I H L) (Sum.elim (fun _ : UnselectedColumn s => H / L) Q) =
      (Sum.elim (spatialPivotScale J H L) Q) ∘ selectedFullSpatialColumnEquiv s N := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem smoothSelectedSpatial_original_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {H L : ℝ} (hH : 0 < H) (hL : 0 < L) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) :
    smoothIntegerImagePMF (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (spatialPivotScale I H L) (Sum.elim (fun _ : UnselectedColumn s => H / L) Q)
      (spatialPivotScale_pos I hH hL) (fun k => Sum.rec (fun _ => div_pos hH hL) hQ k) =
    smoothMatrixImagePMF (Matrix.fromCols (rootDifferenceMatrix root D) C)
      (Sum.elim (spatialPivotScale J H L) Q)
      (fun k => Sum.rec (spatialPivotScale_pos J hH hL) hQ k) := by
  rw [smoothIntegerImagePMF_eq_matrix, selectedFullSpatial_fromCols]
  simpa only [← selectedFullSpatial_scale s H L Q] using
    smoothMatrixImagePMF_reindex (Matrix.fromCols (rootDifferenceMatrix root D) C)
      (selectedFullSpatialColumnEquiv s N) (Sum.elim (spatialPivotScale J H L) Q)
      (fun k => Sum.rec (spatialPivotScale_pos J hH hL) hQ k)

end Erdos3

end

end OAI
