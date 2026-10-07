import OAI.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
import OAI.Combinatorics.Progressions.Probability.SmoothSelectedSpatialLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def smoothSpatialOutputLaw {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (C : Matrix (Unit ⊕ I) N ℤ)
    (H L : ℝ) (Q : N → ℝ) (hH : 0 < H) (hL : 0 < L) (hQ : ∀ j, 0 < Q j) :
    PMF ((Unit ⊕ I) → ℤ) :=
  smoothMatrixImagePMF (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (Sum.elim (spatialPivotScale J H L) Q)
    (fun k => Sum.rec (spatialPivotScale_pos J hH hL) hQ k)

noncomputable def smoothSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hA : (selectedSpatialPivot root D s).det ≠ 0)
    (H L : ℝ) (hH : 0 < H) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  normalizedFiberDensity (selectedSpatialPivot root D s) hA (selectedSpatialFreeColumns root D s)
    (spatialPivotScale I H L) (fun _ => H) (fun _ => H / L)
    (spatialPivotScale_pos I hH hL) (fun _ => hH) (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))

theorem goodScalarKernelTuple_selected_period {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {L B : ℕ} {κ : ℝ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L)
    (root : J → ℤ) (hx : GoodScalarKernelTuple s κ B x) :
    ∃ m : ℕ, 0 < m ∧ m ≤ B ∧
      integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) := by
  obtain ⟨m, hm, hmB, hp⟩ := rootDifferenceMatrix_bounded_period root (scalarCubeDifferenceMatrix x) hx.2
  exact ⟨m, hm, hmB, by rwa [selectedSpatial_full_image]⟩

theorem smoothSpatial_original_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} {H ρ ξ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ))
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * H)
    (hρ : 0 < ρ) (hscale : ρ ≤ H / L) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ) :
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    ∀ v, |(∏ _i : Unit ⊕ I, H) *
        (smoothSpatialOutputLaw root (scalarCubeDifferenceMatrix x) C H L Q hH
          (by exact_mod_cast hL) hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)
        (fun _ => H) (smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA
          H L hH (by exact_mod_cast hL)) v| ≤ smoothSpatialError N s B L ρ ξ := by
  obtain ⟨hsmall, hsmallMass⟩ := smoothSpatial_mesh_conditions s hρ hlarge
  have h := (smoothSpatial_probability_comparison s x root hB hL hH hx hroot C Q hQ
    hξ0 hξ1 hC hρ hscale hscaleQ hsmall hsmallMass).1
  rw [smoothSelectedSpatial_original_law root (scalarCubeDifferenceMatrix x) s C
    hH (by exact_mod_cast hL) Q hQ] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def smoothSpatialDensityCap {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B : ℕ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial *
    (scalarSpatialInverseAllowance I B)^Fintype.card (Unit ⊕ I) * 2^Fintype.card (UnselectedColumn s)

noncomputable def smoothSpatialDensityLip {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B : ℕ) : ℝ :=
  smoothSpatialDensityCap s B *
    ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz) *
      scalarSpatialInverseAllowance I B

theorem smoothSpatialDensityCap_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B : ℕ) : 0 ≤ smoothSpatialDensityCap s B := by
  unfold smoothSpatialDensityCap scalarSpatialInverseAllowance
  positivity

theorem smoothSpatialDensityLip_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B : ℕ) : 0 ≤ smoothSpatialDensityLip s B := by
  unfold smoothSpatialDensityLip
  have h := smoothSpatialDensityCap_nonneg s B
  unfold scalarSpatialInverseAllowance
  positivity

theorem smoothSpatialKernelDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {L B : ℕ} {H : ℝ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ)) :
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA H L hH (by exact_mod_cast hL)
    (∀ y, |f y| ≤ smoothSpatialDensityCap s B) ∧
      LipschitzWith (Real.toNNReal (smoothSpatialDensityLip s B)) f := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
  have hA : A.det ≠ 0 := goodScalarKernelTuple_spatial_det_ne_zero s x root (one_div_pos.mpr hBp) hx
  let E := normalizedPivotEquiv A hA (spatialPivotScale I H L) (fun _ => H)
    (spatialPivotScale_pos I hH hLp) (fun _ => hH)
  have hi : ‖E.symm.toContinuousLinearMap‖ ≤ scalarSpatialInverseAllowance I B := by
    simpa only [E, A, scalarSpatialInverseAllowance, one_div, div_inv_eq_mul] using
      scalarSpatialPivot_inverse_bound s x root (one_div_pos.mpr hBp) hx hH hL hroot
  constructor
  · intro y
    have h := pivotOutputDensity_abs_le_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s)
        (fun _ => H / L) (fun _ => H))) (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))
      zero_le_one zero_le_one (smoothSplitProfile_zero_outside _ _) (smoothSplitProfile_norm_le _ _) hi y
    simpa only [smoothSpatialKernelDensity, normalizedFiberDensity, smoothSpatialDensityCap,
      E, A, mul_one] using h
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, Real.coe_toNNReal _ (smoothSpatialDensityLip_nonneg s B)]
    have h := pivotOutputDensity_output_bound_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s)
        (fun _ => H / L) (fun _ => H))) (smoothSplitProfile_lipschitz (UnselectedColumn s) (Unit ⊕ I))
      zero_le_one (smoothSplitProfile_zero_outside _ _) hi v w
    simpa only [smoothSpatialKernelDensity, normalizedFiberDensity, smoothSpatialDensityLip,
      smoothSpatialDensityCap, E, A, mul_one, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
      dist_eq_norm, mul_assoc] using h

end Erdos3

end

end OAI
