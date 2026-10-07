import OAI.Combinatorics.Progressions.Geometry.PhysicalSpatialScales

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def anisotropicSpatialScale (I : Type*) (A R : ℝ) : Unit ⊕ I → ℝ :=
  Sum.elim (fun _ => A) (fun _ => R)

theorem anisotropicSpatialScale_pos (I : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ i, 0 < anisotropicSpatialScale I A R i := by
  rintro (i | i)
  · exact hA
  · exact hR

theorem anisotropicSpatialScale_physicalPivot {I J : Type*} (s : I ↪ J) (A R : ℝ) :
    (fun i => physicalSpatialInputScale J A R (physicalCubePivotIndex s i)) =
      anisotropicSpatialScale I A R := by
  funext i
  cases i <;> rfl

theorem selectedFullSpatial_anisotropic_scale {I J N : Type*} [Fintype I]
    (s : I ↪ J) (A R : ℝ) (Q : N → ℝ) :
    Sum.elim (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q) =
      Sum.elim (anisotropicSpatialScale J A R) Q ∘ selectedFullSpatialColumnEquiv s N := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k <;> rfl

noncomputable def anisotropicSpatialOutputLaw {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (C : Matrix (Unit ⊕ I) N ℤ)
    (A R : ℝ) (Q : N → ℝ) (hA : 0 < A) (hR : 0 < R) (hQ : ∀ j, 0 < Q j) :
    PMF ((Unit ⊕ I) → ℤ) :=
  smoothMatrixImagePMF (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (Sum.elim (anisotropicSpatialScale J A R) Q)
    (fun j => Sum.rec (anisotropicSpatialScale_pos J hA hR) hQ j)

theorem smoothSelectedSpatial_anisotropic_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) :
    smoothIntegerImagePMF (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q)
      (anisotropicSpatialScale_pos I hA hR) (fun j => Sum.rec (fun _ => hR) hQ j) =
      anisotropicSpatialOutputLaw root D C A R Q hA hR hQ := by
  rw [smoothIntegerImagePMF_eq_matrix, selectedFullSpatial_fromCols]
  simpa only [← selectedFullSpatial_anisotropic_scale s A R Q, anisotropicSpatialOutputLaw] using
    (smoothMatrixImagePMF_reindex (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (selectedFullSpatialColumnEquiv s N) (Sum.elim (anisotropicSpatialScale J A R) Q)
    (fun j => Sum.rec (anisotropicSpatialScale_pos J hA hR) hQ j))

noncomputable def anisotropicSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (A R L : ℝ) (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  normalizedFiberDensity (selectedSpatialPivot root D s) hp (selectedSpatialFreeColumns root D s)
    (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L) (fun _ => R)
    (anisotropicSpatialScale_pos I hA hR) (physicalSpatialOutputScale_pos I hA hR hL)
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))

end Erdos3

end

end OAI
