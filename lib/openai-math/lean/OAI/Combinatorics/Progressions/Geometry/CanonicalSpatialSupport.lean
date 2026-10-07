import OAI.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedFiber_output_row
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (z : I → ℝ) (y : J → ℝ) (i : I) :
    P i * ((normalizedPivotEquiv A hA S P hS hP z) i +
      (matrixSupCLM (normalizedIntegerColumns B T P) y) i) =
      (∑ j, (A i j : ℝ) * S j * z j) + ∑ j, (B i j : ℝ) * T j * y j := by
  change P i * (((normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap z) i + _) = _
  rw [normalizedPivotEquiv_coe, matrixSupCLM_apply, matrixSupCLM_apply]
  simp only [Matrix.mulVec, dotProduct, normalizedIntegerPivot_entry, normalizedIntegerColumns_entry_div]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> field_simp [(hP i).ne']

theorem normalizedFiberDensity_zero_of_row
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 ≤ T j) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (hsupport : ∀ p, 1 < ‖p‖ → f p = 0) (v : I → ℝ) (i : I)
    (hfar : (∑ j, |(A i j : ℝ)| * S j) + (∑ j, |(B i j : ℝ)| * T j) < |P i * v i|) :
    normalizedFiberDensity A hA B S P T hS hP f v = 0 := by
  let E := normalizedPivotEquiv A hA S P hS hP
  let C := matrixSupCLM (normalizedIntegerColumns B T P)
  have hzero (y : J → ℝ) : f (y, E.symm (v - C y)) = 0 := by
    by_contra hn
    let z := E.symm (v - C y)
    have hnorm : ‖(y, z)‖ ≤ 1 := le_of_not_gt (fun h => hn (hsupport _ h))
    have hy (j) : |y j| ≤ 1 := by
      exact (show |y j| ≤ ‖y‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j).trans
        ((norm_fst_le (y,z)).trans hnorm)
    have hz (j) : |z j| ≤ 1 := by
      exact (show |z j| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j).trans
        ((norm_snd_le (y,z)).trans hnorm)
    have heq : (E z) i + (C y) i = v i := by
      dsimp only [z]
      rw [E.apply_symm_apply]
      simp only [Pi.sub_apply, sub_add_cancel]
    have hrow := normalizedFiber_output_row A hA B S P T hS hP z y i
    change P i * ((E z) i + (C y) i) = _ at hrow
    rw [heq] at hrow
    have hbound : |P i * v i| ≤
        (∑ j, |(A i j : ℝ)| * S j) + ∑ j, |(B i j : ℝ)| * T j := by
      rw [hrow]
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_pos (hS j)]
        exact (mul_le_mul_of_nonneg_left (hz j) (mul_nonneg (abs_nonneg _) (hS j).le)).trans_eq (mul_one _)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hT j)]
        exact (mul_le_mul_of_nonneg_left (hy j) (mul_nonneg (abs_nonneg _) (hT j))).trans_eq (mul_one _)
    exact (not_le_of_gt hfar) hbound
  change pivotOutputDensity E C f v = 0
  rw [pivotOutputDensity_formula]
  simp only [hzero, integral_zero, mul_zero]

theorem normalizedFiberDensity_row_bound
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 ≤ T j) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (hsupport : ∀ p, 1 < ‖p‖ → f p = 0) (v : I → ℝ)
    (hne : normalizedFiberDensity A hA B S P T hS hP f v ≠ 0) (i : I) :
    |P i * v i| ≤ (∑ j, |(A i j : ℝ)| * S j) + ∑ j, |(B i j : ℝ)| * T j := by
  by_contra h
  exact hne (normalizedFiberDensity_zero_of_row A hA B S P T hS hP hT f hsupport v i (lt_of_not_ge h))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem selectedColumn_sum (s : I ↪ J) (f : J → ℝ) :
    (∑ i, f (s i)) + (∑ j : UnselectedColumn s, f j.val) = ∑ j, f j := by
  calc
    _ = ∑ j : I ⊕ UnselectedColumn s, f (selectedColumnEquiv s j) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Equiv.sum_comp (selectedColumnEquiv s) f

omit [DecidableEq I] [DecidableEq J] in
theorem selectedSpatial_root_row_mass (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ) (H : ℝ) :
    (∑ j, |((selectedSpatialPivot root D s (.inl ()) j : ℤ) : ℝ)| * anisotropicSpatialScale I H 1 j) +
      (∑ j : UnselectedColumn s, |((selectedSpatialFreeColumns root D s (.inl ()) j : ℤ) : ℝ)| * 1) =
      H + ∑ j, |(root j : ℝ)| := by
  simpa [selectedSpatialPivot, rootDifferenceMatrix, selectedSpatialFreeColumns,
    anisotropicSpatialScale, Fintype.sum_sum_type, add_assoc] using
    congrArg (fun t : ℝ => H + t) (selectedColumn_sum s (fun j => |(root j : ℝ)|))

omit [DecidableEq I] [DecidableEq J] in
theorem selectedSpatial_slope_row_mass (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ) (H : ℝ) (i : I) :
    (∑ j, |((selectedSpatialPivot root D s (.inr i) j : ℤ) : ℝ)| * anisotropicSpatialScale I H 1 j) +
      (∑ j : UnselectedColumn s, |((selectedSpatialFreeColumns root D s (.inr i) j : ℤ) : ℝ)| * 1) =
      ∑ j, |(D i j : ℝ)| := by
  simpa [selectedSpatialPivot, rootDifferenceMatrix, selectedSpatialFreeColumns,
    anisotropicSpatialScale, Fintype.sum_sum_type] using
    selectedColumn_sum s (fun j => |(D i j : ℝ)|)

theorem canonicalSpatialSiteDensity_star_bound (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ j, |(D i j : ℝ)|) ≤ 1 + W)
    (v : (Unit ⊕ I) → ℝ) (hne : canonicalSpatialSiteDensity s root D hp W L hW hL v ≠ 0) :
    ∀ i, |spatialStar v i| ≤ 3 := by
  let H := 1 + W
  have hH : 0 < H := by dsimp only [H]; linarith
  let P := physicalSpatialOutputScale I H 1 L
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos I hH zero_lt_one hL
  let w := fun i => H / P i * v i
  have hn : normalizedFiberDensity (selectedSpatialPivot root D s) hp
      (selectedSpatialFreeColumns root D s) (anisotropicSpatialScale I H 1) P (fun _ => 1)
      (anisotropicSpatialScale_pos I hH zero_lt_one) hP
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) w ≠ 0 := hne
  have hrow := normalizedFiberDensity_row_bound (selectedSpatialPivot root D s) hp
    (selectedSpatialFreeColumns root D s) (anisotropicSpatialScale I H 1) P (fun _ => 1)
    (anisotropicSpatialScale_pos I hH zero_lt_one) hP (fun _ => zero_le_one)
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))
    (smoothSplitProfile_zero_outside (UnselectedColumn s) (Unit ⊕ I)) w hn
  have hscale (i) : P i * w i = H * v i := by
    dsimp only [w]
    field_simp [(hP i).ne']
  have hr : |H * v (.inl ())| ≤ H + W := by
    have h := hrow (.inl ())
    rw [hscale, selectedSpatial_root_row_mass] at h
    exact h.trans (add_le_add le_rfl hroot)
  have hd (i) : |H * v (.inr i)| ≤ H := by
    have h := hrow (.inr i)
    rw [hscale, selectedSpatial_slope_row_mass] at h
    exact h.trans (hD i)
  have hvroot : |v (.inl ())| ≤ 2 := by
    rw [abs_mul, abs_of_pos hH] at hr
    dsimp only [H] at hr hH
    nlinarith
  have hvdiff (i) : |v (.inr i)| ≤ 1 := by
    have h := hd i
    rw [abs_mul, abs_of_pos hH] at h
    nlinarith
  intro i
  cases i with
  | inl i => exact hvroot.trans (by norm_num)
  | inr i =>
    change |v (.inl ()) + v (.inr i)| ≤ 3
    exact (abs_add_le _ _).trans (by linarith [hvdiff i])

theorem canonicalSpatialSiteDensity_zero_outside (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ j, |(D i j : ℝ)|) ≤ 1 + W)
    (v : (Unit ⊕ I) → ℝ) (hv : ∃ i, 3 < |spatialStar v i|) :
    canonicalSpatialSiteDensity s root D hp W L hW hL v = 0 := by
  by_contra hn
  obtain ⟨i, hi⟩ := hv
  exact (not_lt_of_ge (canonicalSpatialSiteDensity_star_bound s root D hp hW hL hroot hD v hn i)) hi

end Erdos3

end

end OAI
