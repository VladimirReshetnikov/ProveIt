import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Equiv.Set
import OAI.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
import OAI.Combinatorics.Progressions.Linear.RootDifferenceMatrix

namespace OAI

section

namespace Erdos3

open scoped Matrix

abbrev UnselectedColumn {I J : Type*} (s : I ↪ J) := {j : J // j ∉ Set.range s}

noncomputable instance unselectedColumnFintype {I J : Type*} [Fintype J] (s : I ↪ J) :
    Fintype (UnselectedColumn s) := Fintype.ofFinite _

noncomputable def selectedColumnEquiv {I J : Type*} [Fintype I] (s : I ↪ J) : I ⊕ UnselectedColumn s ≃ J := by
  classical
  exact (Equiv.sumCongr s.toEquivRange (Equiv.refl (UnselectedColumn s))).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range s))

noncomputable def selectedSpatialColumnEquiv {I J : Type*} [Fintype I] (s : I ↪ J) :
    (Unit ⊕ I) ⊕ UnselectedColumn s ≃ Unit ⊕ J :=
  (Equiv.sumAssoc Unit I (UnselectedColumn s)).trans
    (Equiv.sumCongr (Equiv.refl Unit) (selectedColumnEquiv s))

def selectedSpatialPivot {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) : Matrix (Unit ⊕ I) (Unit ⊕ I) R :=
  rootDifferenceMatrix (fun i => root (s i)) (D.submatrix id s)

def selectedSpatialFreeColumns {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) : Matrix (Unit ⊕ I) (UnselectedColumn s) R :=
  Matrix.of (fun i j => Sum.elim (fun _ : Unit => root j.val) (fun i => D i j.val) i)

theorem selectedSpatial_fromCols {I J R : Type*} [Fintype I] [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).submatrix id (selectedSpatialColumnEquiv s) := by
  ext i j
  cases j with
  | inl j => cases j <;> cases i <;> rfl
  | inr j => cases i <;> rfl

theorem selectedSpatial_mulVec {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J)
    (v : (Unit ⊕ I) ⊕ UnselectedColumn s → R) :
    rootDifferenceMatrix root D *ᵥ (v ∘ (selectedSpatialColumnEquiv s).symm) =
      selectedSpatialPivot root D s *ᵥ (v ∘ Sum.inl) +
        selectedSpatialFreeColumns root D s *ᵥ (v ∘ Sum.inr) := by
  have h := Matrix.submatrix_mulVec_equiv (rootDifferenceMatrix root D) v id (selectedSpatialColumnEquiv s)
  rw [← selectedSpatial_fromCols, Matrix.fromCols_mulVec] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialPivotScale (I : Type*) (H L : ℝ) : Unit ⊕ I → ℝ :=
  Sum.elim (fun _ : Unit => H) (fun _ : I => H / L)

theorem spatialPivotScale_pos (I : Type*) {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ i, 0 < spatialPivotScale I H L i := by
  intro i
  cases i
  · exact hH
  · exact div_pos hH hL

theorem normalized_selectedSpatialPivot {I J : Type*} [Fintype I] [DecidableEq I]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot (selectedSpatialPivot root D s) (spatialPivotScale I H L) (fun _ => H) =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) / L)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  cases i with
  | inl i =>
    cases i
    cases j with
    | inl j =>
      cases j
      simp [selectedSpatialPivot, rootDifferenceMatrix, spatialPivotScale, Matrix.fromBlocks, hH]
    | inr j =>
      simp only [selectedSpatialPivot, rootDifferenceMatrix, spatialPivotScale, Matrix.fromBlocks,
        Matrix.of_apply, Sum.elim_inr, Sum.elim_inl]
      field_simp
  | inr i =>
    cases j with
    | inl j => simp [selectedSpatialPivot, rootDifferenceMatrix, spatialPivotScale, Matrix.fromBlocks]
    | inr j =>
      simp only [selectedSpatialPivot, rootDifferenceMatrix, spatialPivotScale, Matrix.fromBlocks,
        Matrix.of_apply, Sum.elim_inr, Matrix.submatrix_apply, id_eq]
      field_simp

theorem rootDifferenceMatrix_real_bound {I J : Type*}
    (root : J → ℝ) (D : Matrix I J ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hr : ∀ j, |root j| ≤ C) (hD : ∀ i j, |D i j| ≤ C) :
    ∀ i j, |rootDifferenceMatrix root D i j| ≤ C := by
  rintro (i | i) (j | j)
  · cases i; cases j
    simpa [rootDifferenceMatrix, Matrix.fromBlocks] using hC
  · exact hr j
  · change |(0 : ℝ)| ≤ C
    simpa using (zero_le_one.trans hC)
  · exact hD i j

theorem normalizedPivotEquiv_inverse_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap =
      (matrixSupCLM (normalizedIntegerPivot A S P)).inverse := by
  rw [← normalizedPivotEquiv_coe A hA S P hS hP, ContinuousLinearMap.inverse_equiv]

end Erdos3

end

end OAI
