import OAI.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal

noncomputable def anisotropicSpatialDetAllowance (I : Type*) [Fintype I] (C : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial * C ^ Fintype.card (Unit ⊕ I)

noncomputable def anisotropicSpatialMeshThreshold {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (C : ℝ) : ℝ :=
  2 * (1 + 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz)) *
      anisotropicSpatialDetAllowance I C

noncomputable def anisotropicSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) (κ C ρ ξ : ℝ) : ℝ :=
  normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    ((B : ℝ) ^ (Fintype.card I + 1)) (physicalSpatialInverseBound I κ)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
      anisotropicSpatialDetAllowance I C / ρ +
  (B : ℝ) ^ (Fintype.card I + 1) *
    (spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
      (physicalSpatialInverseBound I κ) 1
      ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
        (Fintype.card N * ξ))

theorem anisotropicSpatial_original_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R L κ C₀ ρ ξ : ℝ} {B : ℕ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hC₀ : 1 ≤ C₀) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hrC : ∀ j, |(root j : ℝ)| ≤ C₀) (hDC : ∀ i j, |(D i j : ℝ)| ≤ C₀)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).1
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root D C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root D s)
        (Matrix.fromCols (selectedSpatialFreeColumns root D s) C) (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root D hp A R L hA hR hL) v| ≤
      anisotropicSpatialError s N B κ C₀ ρ ξ := by
  intro hp
  let M := selectedSpatialPivot root D s
  let M' := selectedSpatialFreeColumns root D s
  let S := anisotropicSpatialScale I A R
  let P := physicalSpatialOutputScale I A R L
  let lip : ℝ≥0 := (Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz
  have hS := anisotropicSpatialScale_pos I hA hR
  have hP := physicalSpatialOutputScale_pos I hA hR hL
  have hFree : ∀ j, 0 < Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hR
    · exact hQ j
  have hscaleS : ∀ i, ρ ≤ S i := by
    rintro (i | i)
    · exact hscaleA
    · exact hscaleR
  have hscaleFree : ∀ j, ρ ≤ Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hscaleR
    · exact hscaleQ j
  have hcoeff : ∀ i j, |(M i j : ℝ)| ≤ C₀ * (1 : ℝ) ^ 0 := by
    intro i j
    have heq : M = (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) :=
      (physicalCubeCoefficient_pivot root D s).symm
    rw [heq]
    simpa only [Matrix.submatrix_apply, id_eq, pow_zero, mul_one] using
      physicalCube_coefficient_bound root D hC₀ hrC hDC i (physicalCubePivotIndex s j)
  have hdet : (M.det.natAbs : ℝ) ≤ anisotropicSpatialDetAllowance I C₀ := by
    simpa only [anisotropicSpatialDetAllowance, one_pow, mul_one] using
      integerPivot_polynomial_period_bound M 0 hcoeff
  have hm := enormousCoefficient_mesh_conditions (j := Fintype.card (Unit ⊕ I)) (h := 0)
    (D := anisotropicSpatialDetAllowance I C₀)
    (Z := 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) * (lip : ℝ))
    (L := 1) (H := ρ) (by unfold anisotropicSpatialDetAllowance; positivity) (by positivity)
    (by norm_num) hρ (by
      simpa only [anisotropicSpatialMeshThreshold, lip, NNReal.coe_mul, NNReal.coe_add,
        NNReal.coe_natCast, one_pow, mul_one] using hmesh)
  simp only [one_pow, mul_one, div_one] at hm
  have hsmallMass : 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
      (lip : ℝ) * ((M.det.natAbs : ℝ) / ρ) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) (by positivity)).trans hm.2
  have hindex : ((pivotFullImage M (Matrix.fromCols M' C)).toAddSubgroup.index : ℝ) ≤
      (B : ℝ) ^ (Fintype.card I + 1) := by
    exact_mod_cast selectedSpatial_extended_index root D s C hperiod
  have hinv : ‖(normalizedPivotEquiv M hp S P hS hP).symm.toContinuousLinearMap‖ ≤
      physicalSpatialInverseBound I κ := by
    rw [normalizedPivotEquiv_inverse_eq]
    exact (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).2
  have hcol := anisotropicSpatial_free_norm_bound root D s C Q hA hR hL hξ1
    (fun j => (hQ j).le) hr hD hC
  have hmove : ∀ n, smoothProductProfile N n ≠ 0 →
      ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ Fintype.card N * ξ := by
    apply supported_column_displacement _ _ (smoothProductProfile_zero_outside N)
    simpa only [mul_one] using normalizedIntegerColumns_variable_norm_bound C Q P hP hξ0
      (fun j => (hQ j).le) hC
  have hfull : LipschitzWith lip
      (splitFreeProfile (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)) := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_lipschitz _ _
  have hbound : ∀ p, ‖splitFreeProfile
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N) p‖ ≤ 1 := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_norm_le _ _
  obtain ⟨hM, hpoint, _⟩ := normalizedSpatial_probability_comparison M hp M' C S P
    (fun _ : UnselectedColumn s => R) Q hS hP hFree
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)
    (fun p => (smoothSplitProfile_range _ _ p).1) (fun n => (smoothProductProfile_range _ n).1)
    (smoothSplitProfile_lipschitz _ _) (smoothProductProfile_contDiff N).continuous hfull
    0 zero_le_one (mul_nonneg (Nat.cast_nonneg _) hξ0) hρ zero_le_one hscaleS hscaleFree
    (hdet.trans hm.1) hcoeff (smoothSplitProfile_zero_outside _ _) (smoothProductProfile_zero_outside N)
    (smoothSplitProfile_integral _ _) (smoothProductProfile_integral N)
    (by simpa only [max_self, show (2 : ℝ) * 1 + 2 = 4 by norm_num] using hsmallMass)
    hbound hindex hinv hcol hmove
  rw [← smoothSelectedSpatial_anisotropic_law root D s C hA hR Q hQ]
  simpa only [splitFreeProfile_smooth, max_self, one_pow, mul_one, lip, M, M', S, P,
    smoothIntegerImagePMF, anisotropicSpatialError, anisotropicSpatialDetAllowance,
    anisotropicSpatialKernelDensity] using hpoint

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem goodScalarKernelTuple_anisotropic_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} (hL : 0 < L) (s : I ↪ J) (x : J → IntegerScalarCubeBox I L)
    (root : J → ℤ) (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R κ C₀ ρ ξ : ℝ} (hA : 0 < A) (hR : 0 < R) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple s κ B x) (hC₀ : 1 ≤ C₀) (hLC : (L : ℝ) ≤ C₀)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hrC : ∀ j, |(root j : ℝ)| ≤ C₀)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero s x root hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root (scalarCubeDifferenceMatrix x) C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)
        (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hp A R L
          hA hR (Nat.cast_pos.mpr hL)) v| ≤ anisotropicSpatialError s N B κ C₀ ρ ξ := by
  intro hp
  have hD : ∀ i j, |(scalarCubeDifferenceMatrix x i j : ℝ)| ≤ L := by
    intro i j
    have hi := Finset.mem_Ico.mp (x j (some i)).property
    exact_mod_cast (abs_le.mpr ⟨hi.1, hi.2.le⟩)
  have hminor : κ ≤ |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (s j) : ℝ) / (L : ℝ))).det| := by
    change κ ≤ |(normalizedScalarCubePivot s x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  exact anisotropicSpatial_original_error root (scalarCubeDifferenceMatrix x) s C Q
    hA hR (Nat.cast_pos.mpr hL) hκ hρ hC₀ hr hD hrC (fun i j => (hD i j).trans hLC)
    hminor hx.2 hQ hξ0 hξ1 hC hscaleA hscaleR hscaleQ hmesh

end Erdos3

end

end OAI
