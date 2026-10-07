import OAI.Combinatorics.Progressions.Estimates.RootDifferencePeriod
import OAI.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw

namespace OAI


namespace Erdos3

theorem integerColumnEquiv_range {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (e : K ≃ J) : (A.submatrix id e).mulVecLin.range = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  change Submodule.span ℤ (Set.range (fun k => fun i => A i (e k))) =
    Submodule.span ℤ (Set.range (fun j => fun i => A i j))
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, by simpa only [e.apply_symm_apply] using hj⟩

theorem selectedSpatial_full_image {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) :
    pivotFullImage (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).mulVecLin.range := by
  rw [pivotFullImage_eq_range, selectedSpatial_fromCols]
  exact integerColumnEquiv_range _ _

theorem selectedSpatial_extended_period {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    HasBoundedScalarPeriod
      (pivotFullImage (selectedSpatialPivot root D s) (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)) B := by
  obtain ⟨a, ha, haB, hp⟩ := rootDifferenceMatrix_bounded_period root D hperiod
  refine ⟨a, ha, haB, ?_⟩
  rw [pivotFullImage_split, selectedSpatial_full_image]
  exact hp.trans le_sup_left

theorem selectedSpatial_extended_index {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    (pivotFullImage (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)).toAddSubgroup.index ≤
        B^(Fintype.card I + 1) := by
  simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_comm] using
    hasBoundedScalarPeriod_index_le _ B (selectedSpatial_extended_period root D s C hperiod)


theorem goodScalarKernelTuple_spatial_det_ne_zero {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L B : ℕ} {κ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hκ : 0 < κ) (hx : GoodScalarKernelTuple s κ B x) :
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
  rw [selectedSpatialPivot, rootDifferenceMatrix_det]
  intro hz
  have h := hx.1
  rw [normalizedScalarCubeMinor, hz, Int.cast_zero, zero_div, abs_zero] at h
  exact (not_lt_of_ge hκ.le) h

theorem scalarSpatialPivot_normalized {I J : Type*}
    [Fintype I] [DecidableEq I] {L : ℕ} {H : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hH : H ≠ 0) (hL : 0 < L) :
    normalizedIntegerPivot (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
      (spatialPivotScale I H L) (fun _ => H) =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) / L) (normalizedScalarCubePivot s x) := by
  exact normalized_selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s hH (by exact_mod_cast hL.ne')

theorem scalarSpatialPivot_coeff_bound {I J : Type*} {L : ℕ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hL : 0 < L) (hroot : ∀ j, |root j| ≤ (L : ℤ)) :
    ∀ i j, |(selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s i j : ℤ)| ≤ L := by
  rintro (i | i) (j | j)
  · cases i; cases j
    simpa [selectedSpatialPivot, rootDifferenceMatrix, Matrix.fromBlocks] using
      (show (1 : ℤ) ≤ L by exact_mod_cast hL)
  · exact hroot (s j)
  · change |(0 : ℤ)| ≤ L
    simp
  · change |(x (s j) (some i) : ℤ)| ≤ L
    have hi := Finset.mem_Ico.mp (x (s j) (some i)).property
    exact abs_le.mpr ⟨hi.1, hi.2.le⟩

theorem scalarSpatialPivot_inverse_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L B : ℕ} {κ H : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hκ : 0 < κ) (hx : GoodScalarKernelTuple s κ B x) (hH : 0 < H) (hL : 0 < L)
    (hroot : ∀ j, |root j| ≤ (L : ℤ)) :
    ‖(normalizedPivotEquiv (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
      (goodScalarKernelTuple_spatial_det_ne_zero s x root hκ hx)
      (spatialPivotScale I H L) (fun _ => H) (spatialPivotScale_pos I hH (by exact_mod_cast hL))
      (fun _ => hH)).symm.toContinuousLinearMap‖ ≤
        (Fintype.card I + 1 : ℝ) * ((Fintype.card I + 1).factorial : ℝ) / κ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : ∀ i, |(root (s i) : ℝ) / L| ≤ 1 := by
    intro i
    rw [abs_div, abs_of_pos hL']
    apply (div_le_one hL').mpr
    exact_mod_cast hroot (s i)
  let A := normalizedIntegerPivot (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
    (spatialPivotScale I H L) (fun _ => H)
  have ha : ∀ i j, |A i j| ≤ 1 := by
    rw [show A = rootDifferenceMatrix (fun i => (root (s i) : ℝ) / L) (normalizedScalarCubePivot s x) from
      scalarSpatialPivot_normalized s x root hH.ne' hL]
    exact rootDifferenceMatrix_real_bound _ _ le_rfl hr (normalizedScalarCubePivot_entry_bound hL s x)
  have hd : κ ≤ |A.det| := by
    rw [show A = rootDifferenceMatrix (fun i => (root (s i) : ℝ) / L) (normalizedScalarCubePivot s x) from
      scalarSpatialPivot_normalized s x root hH.ne' hL,
      rootDifferenceMatrix_det, normalizedScalarCubePivot_det]
    exact hx.1.le
  have hi := (matrixSupCLM_inverse_norm_le A zero_le_one ha hκ hd).2
  rw [normalizedPivotEquiv_inverse_eq]
  simpa only [A, Fintype.card_sum, Fintype.card_unit, Nat.add_comm, Nat.cast_add, Nat.cast_one,
    one_pow, mul_one, mul_div_assoc] using hi


theorem scalarSpatialFree_scaled_bound {I J : Type*} {L : ℕ} {H : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hL : 0 < L) (hH : 0 < H) (hroot : ∀ j, |root j| ≤ (L : ℤ)) :
    ∀ i j, |(selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s i j : ℝ)| *
      (H / L) ≤ H := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  intro i j
  have hc : |(selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s i j : ℝ)| ≤ L := by
    cases i with
    | inl i => exact_mod_cast hroot j.val
    | inr i =>
      have hi := Finset.mem_Ico.mp (x j.val (some i)).property
      have hb := abs_le.mpr ⟨hi.1, hi.2.le⟩
      exact_mod_cast hb
  have h := mul_le_mul_of_nonneg_right hc (div_nonneg hH.le hL'.le)
  simpa only [mul_div_cancel₀ _ hL'.ne'] using h

theorem scalarSpatial_free_norm_bound {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L : ℕ} {H ξ : ℝ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    (hL : 0 < L) (hH : 0 < H) (hξ : ξ ≤ 1) (hQ : ∀ j, 0 ≤ Q j)
    (hroot : ∀ j, |root j| ≤ (L : ℤ)) (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * H) :
    ‖matrixSupCLM (normalizedIntegerColumns
      (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)
      (Sum.elim (fun _ : UnselectedColumn s => H / L) Q) (fun _ => H))‖ ≤
        Fintype.card (UnselectedColumn s ⊕ N) := by
  have hscale : ∀ j, 0 ≤ Sum.elim (fun _ : UnselectedColumn s => H / L) Q j := by
    intro j
    cases j with
    | inl j => exact div_nonneg hH.le (Nat.cast_nonneg _)
    | inr j => exact hQ j
  have hcolumns : ∀ i j,
      |((Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C) i j : ℝ)| *
        Sum.elim (fun _ : UnselectedColumn s => H / L) Q j ≤ 1 * H := by
    intro i j
    cases j with
    | inl j =>
      change |(selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s i j : ℝ)| * (H / L) ≤ 1 * H
      simpa only [one_mul] using scalarSpatialFree_scaled_bound s x root hL hH hroot i j
    | inr j => exact (hC i j).trans (mul_le_mul_of_nonneg_right hξ hH.le)
  simpa only [mul_one] using normalizedIntegerColumns_norm_bound _ _ hH zero_le_one hscale hcolumns


theorem scalarSpatialPivot_det_bound {I J : Type*} [Fintype I] [DecidableEq I] {L : ℕ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ) :
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s).det.natAbs ≤
      (Fintype.card I).factorial * L^Fintype.card I := by
  rw [selectedSpatialPivot, rootDifferenceMatrix_det]
  apply integerColumnMinor_det_bound (scalarCubeDifferenceMatrix x) s L
  intro i j
  have hi := Finset.mem_Ico.mp (x j (some i)).property
  have hb := abs_le.mpr ⟨hi.1, hi.2.le⟩
  have hn : (((x j (some i) : ℤ).natAbs : ℕ) : ℤ) ≤ L := by
    simpa only [Int.natCast_natAbs] using hb
  exact_mod_cast hn

theorem spatialPivotScale_lower (I : Type*) {H ρ : ℝ} {L : ℕ}
    (hH : 0 ≤ H) (hL : 0 < L) (hρ : ρ ≤ H / L) :
    ∀ i, ρ ≤ spatialPivotScale I H L i := by
  intro i
  cases i with
  | inl i =>
    exact hρ.trans (div_le_self hH (by exact_mod_cast hL))
  | inr i => exact hρ

end Erdos3

end OAI
