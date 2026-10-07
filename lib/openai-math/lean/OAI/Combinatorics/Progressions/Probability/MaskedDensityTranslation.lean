import OAI.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem maskedIntegerImageDensity_shift_error {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ)
    (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : I → ℤ) (hs : s ∈ pivotFullImage A B) {G : ℝ}
    (hi : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f (v + s) - maskedIntegerImageDensity A B P f v| ≤
      G * K * ‖fun i => (s i : ℝ) / P i‖ := by
  classical
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hi
  have hm : v + s ∈ pivotFullImage A B ↔ v ∈ pivotFullImage A B := by
    constructor
    · intro h
      simpa only [add_sub_cancel_right] using (pivotFullImage A B).sub_mem h hs
    · intro h
      exact (pivotFullImage A B).add_mem h hs
  have hd : (fun i => ((v + s) i : ℝ) / P i) - (fun i => (v i : ℝ) / P i) =
      (fun i => (s i : ℝ) / P i) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_add, add_div, add_sub_cancel_left]
  have hf' := hf.dist_le_mul (fun i => ((v + s) i : ℝ) / P i) (fun i => (v i : ℝ) / P i)
  rw [Real.dist_eq, dist_eq_norm, hd] at hf'
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hm.mpr hv, hv, ite_true, ← mul_sub, abs_mul]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul hi hf' (abs_nonneg _) hG).trans_eq (mul_assoc _ _ _).symm
  · have hvs : v + s ∉ pivotFullImage A B := fun h => hv (hm.mp h)
    simp only [maskedIntegerImageDensity, hvs, hv, ite_false, sub_self, abs_zero]
    positivity

theorem residueMaskedDensity_shift_error {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ)
    (m : ℕ) (hp : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : I → ℤ) (hs : s ∈ integerScalarLattice I (m : ℤ)) {G : ℝ}
    (hi : ((pivotFullImage A (Matrix.fromCols B D)).toAddSubgroup.index : ℝ) ≤ G)
    (v : I → ℤ) :
    |maskedIntegerImageDensity A (Matrix.fromCols B C) P f (v + s) -
      maskedIntegerImageDensity A (Matrix.fromCols B D) P f v| ≤
      G * K * ‖fun i => (s i : ℝ) / P i‖ := by
  rw [maskedIntegerImageDensity_eq_of_kernel_residues A B C D m hp hCD]
  apply maskedIntegerImageDensity_shift_error A (Matrix.fromCols B D) P f hf s _ hi v
  rw [pivotFullImage_split]
  exact (show pivotFullImage A B ≤ _ from le_sup_left) (hp hs)

theorem shiftedMass_residueMask_error {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ)
    (m : ℕ) (hp : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : I → ℤ) (hs : s ∈ integerScalarLattice I (m : ℤ)) {G E : ℝ}
    (hi : ((pivotFullImage A (Matrix.fromCols B D)).toAddSubgroup.index : ℝ) ≤ G)
    (mass : (I → ℤ) → ℝ)
    (he : ∀ v, |mass v - maskedIntegerImageDensity A (Matrix.fromCols B C) P f v| ≤ E)
    (v : I → ℤ) :
    |mass (v + s) - maskedIntegerImageDensity A (Matrix.fromCols B D) P f v| ≤
      E + G * K * ‖fun i => (s i : ℝ) / P i‖ :=
  (abs_sub_le _ _ _).trans (add_le_add (he (v + s))
    (residueMaskedDensity_shift_error A B C D m hp hCD P f hf s hs hi v))

end Erdos3

end

end OAI
