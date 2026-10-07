import OAI.Combinatorics.Progressions.Probability.CanonicalZeroSpatialDensity

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Matrix

theorem canonicalSpatialSiteDensity_root_bound_two
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (v : (Unit ⊕ I) → ℝ)
    (hne : canonicalSpatialSiteDensity s root D hp W L hW hL v ≠ 0) :
    |v (.inl ())| ≤ 2 := by
  let H := 1 + W
  have hH : 0 < H := by dsimp [H]; linarith
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
  rw [abs_mul, abs_of_pos hH] at hr
  dsimp only [H] at hr hH
  nlinarith

theorem canonicalZeroSpatialJointDensity_coordinate_bound_two
    {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]
    (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (v : (Σ _ : X, Unit ⊕ Empty) → ℝ)
    (hne : canonicalZeroSpatialJointDensity s root D hp hW hL v ≠ 0) :
    ∀ i : X, |v ⟨i, .inl ()⟩| ≤ 2 := by
  intro i
  apply canonicalSpatialSiteDensity_root_bound_two s root D hp hW hL hroot
    (fun a => v ⟨i, a⟩)
  change (∏ j : X, canonicalSpatialSiteDensity s root D hp W L hW hL
    (fun a => v ⟨j, a⟩)) ≠ 0 at hne
  exact (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ _)

end Erdos3

end

end OAI
