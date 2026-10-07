import OAI.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
import OAI.Combinatorics.Progressions.Lattices.SmoothIntegerImage

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarSpatialIndexAllowance (I : Type*) [Fintype I] (B : ℕ) : ℝ :=
  (B : ℝ)^(Fintype.card I + 1)

noncomputable def scalarSpatialInverseAllowance (I : Type*) [Fintype I] (B : ℕ) : ℝ :=
  (Fintype.card I + 1 : ℝ) * ((Fintype.card I + 1).factorial : ℝ) * B

theorem scalarSpatial_probability_comparison {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} {H R Rn ρ ξ F : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ))
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * H)
    (f : (UnselectedColumn s → ℝ) × ((Unit ⊕ I) → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ n, 0 ≤ g n)
    {K Kfull : ℝ≥0} (hf : LipschitzWith K f) (hg : Continuous g)
    (hfull : LipschitzWith Kfull (splitFreeProfile f g))
    (hR : 0 ≤ R) (hRn : 0 ≤ Rn) (hρ : 0 < ρ) (hF : 0 ≤ F)
    (hscale : ρ ≤ H / L) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hsmall : ((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I ≤ ρ)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hfmass : (∫ p, f p) = 1) (hgmass : (∫ n, g n) = 1)
    (hsmallMass : (2 * max R Rn + 2) ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) * Kfull *
      ((((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖splitFreeProfile f g p‖ ≤ F) :
    ∃ hM : 0 < scaledInputMass (splitFreeProfile f g) (spatialPivotScale I H L)
        (Sum.elim (fun _ : UnselectedColumn s => H / L) Q),
      let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
      let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
      let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
        (one_div_pos.mpr (by exact_mod_cast hB)) hx
      let hS := spatialPivotScale_pos I hH (by exact_mod_cast hL)
      let hFree : ∀ j, 0 < Sum.elim (fun _ : UnselectedColumn s => H / L) Q j :=
        fun j => Sum.rec (fun _ => div_pos hH (by exact_mod_cast hL)) (fun j => hQ j) j
      let p := integerImagePMF A (Matrix.fromCols A' C) (splitFreeProfile f g)
        (splitFreeProfile_nonneg hf0 hg0) (spatialPivotScale I H L)
        (Sum.elim (fun _ : UnselectedColumn s => H / L) Q) hS hFree
        (splitFreeProfile_zero_outside hfs hgs) hM
      let w := maskedIntegerImageDensity A (Matrix.fromCols A' C) (fun _ => H)
        (normalizedFiberDensity A hA A' (spatialPivotScale I H L) (fun _ => H)
          (fun _ => H / L) hS (fun _ => hH) f)
      let E := (normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
          (scalarSpatialIndexAllowance I B) (scalarSpatialInverseAllowance I B)
          (Fintype.card (UnselectedColumn s ⊕ N)) (max R Rn) F Kfull * (Fintype.card (Unit ⊕ I)).factorial) *
            (L : ℝ)^(Fintype.card (Unit ⊕ I)) / ρ +
        scalarSpatialIndexAllowance I B *
          (spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
            (scalarSpatialInverseAllowance I B) R K * (Fintype.card N * ξ * Rn))
      (∀ v, |(∏ _i : Unit ⊕ I, H) * (p v).toReal - w v| ≤ E) ∧
      (∀ (t : Finset ((Unit ⊕ I) → ℤ)) (weight : ((Unit ⊕ I) → ℤ) → ℝ)
          (φ : ((Unit ⊕ I) → ℤ) → ℂ),
        (∀ v ∈ t, 0 ≤ weight v) → (∀ v ∈ t, ‖φ v‖ ≤ 1) →
        ‖(𝔼 v ∈ t, ((weight v * ((∏ _i : Unit ⊕ I, H) * (p v).toReal) : ℝ) : ℂ) * φ v) -
          (𝔼 v ∈ t, ((weight v * w v : ℝ) : ℂ) * φ v)‖ ≤ E * (𝔼 v ∈ t, weight v)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
  let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
  have hA : A.det ≠ 0 := goodScalarKernelTuple_spatial_det_ne_zero s x root (one_div_pos.mpr hB') hx
  have hFree : ∀ j, 0 < Sum.elim (fun _ : UnselectedColumn s => H / L) Q j := by
    intro j
    cases j with
    | inl j => exact div_pos hH hL'
    | inr j => exact hQ j
  have hscaleFree : ∀ j, ρ ≤ Sum.elim (fun _ : UnselectedColumn s => H / L) Q j := by
    intro j
    cases j with
    | inl j => exact hscale
    | inr j => exact hscaleQ j
  have hdet : (A.det.natAbs : ℝ) ≤ ((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I := by
    exact_mod_cast scalarSpatialPivot_det_bound s x root
  have hcoeff : ∀ i j, |(A i j : ℝ)| ≤ 1 * (L : ℝ)^1 := by
    intro i j
    simpa only [one_mul, pow_one, Int.cast_abs] using
      (show ((|(A i j : ℤ)| : ℤ) : ℝ) ≤ (L : ℝ) by exact_mod_cast scalarSpatialPivot_coeff_bound s x root hL hroot i j)
  have hmass : (2 * max R Rn + 2) ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) * Kfull *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2 := by
    apply le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) (by positivity)) hsmallMass
  have hindex : ((pivotFullImage A (Matrix.fromCols A' C)).toAddSubgroup.index : ℝ) ≤ scalarSpatialIndexAllowance I B := by
    dsimp only [A, A', scalarSpatialIndexAllowance]
    exact_mod_cast selectedSpatial_extended_index root (scalarCubeDifferenceMatrix x) s C hx.2
  have hinv : ‖(normalizedPivotEquiv A hA (spatialPivotScale I H L) (fun _ => H)
      (spatialPivotScale_pos I hH hL') (fun _ => hH)).symm.toContinuousLinearMap‖ ≤ scalarSpatialInverseAllowance I B := by
    simpa only [scalarSpatialInverseAllowance, one_div, div_inv_eq_mul] using
      scalarSpatialPivot_inverse_bound s x root (one_div_pos.mpr hB') hx hH hL hroot
  have hcol := scalarSpatial_free_norm_bound s x root C Q hL hH hξ1 (fun j => (hQ j).le) hroot hC
  have hmove := normalizedIntegerColumns_displacement C Q hH hξ0 hRn (fun j => (hQ j).le) hC g hgs
  have h := normalizedSpatial_probability_comparison A hA A' C (spatialPivotScale I H L) (fun _ => H)
    (fun _ : UnselectedColumn s => H / L) Q (spatialPivotScale_pos I hH hL') (fun _ => hH) hFree
    f g hf0 hg0 hf hg hfull 1 hR (by positivity) hρ hF (spatialPivotScale_lower I hH.le hL hscale)
    hscaleFree (hdet.trans hsmall) hcoeff hfs hgs hfmass hgmass hmass hbound hindex hinv hcol hmove
  simpa only [Nat.one_mul, one_pow, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def smoothSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (B L : ℕ) (ρ ξ : ℝ) : ℝ :=
  (normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    (scalarSpatialIndexAllowance I B) (scalarSpatialInverseAllowance I B)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
      (Fintype.card (Unit ⊕ I)).factorial) * (L : ℝ)^(Fintype.card (Unit ⊕ I)) / ρ +
    scalarSpatialIndexAllowance I B *
      (spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
        (scalarSpatialInverseAllowance I B) 1
        ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
          (Fintype.card N * ξ))

theorem smoothSpatial_probability_comparison {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} {H ρ ξ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ))
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * H)
    (hρ : 0 < ρ) (hscale : ρ ≤ H / L) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hsmall : ((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I ≤ ρ)
    (hsmallMass : 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
      (((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) : ℝ) *
        probabilityProfileLipschitz) *
      ((((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I) / ρ) ≤ 1 / 2) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let hS := spatialPivotScale_pos I hH (by exact_mod_cast hL)
    let hFree : ∀ j, 0 < Sum.elim (fun _ : UnselectedColumn s => H / L) Q j :=
      fun j => Sum.rec (fun _ => div_pos hH (by exact_mod_cast hL)) (fun j => hQ j) j
    let p := smoothIntegerImagePMF A (Matrix.fromCols A' C) (spatialPivotScale I H L)
      (Sum.elim (fun _ : UnselectedColumn s => H / L) Q) hS hFree
    let w := maskedIntegerImageDensity A (Matrix.fromCols A' C) (fun _ => H)
      (normalizedFiberDensity A hA A' (spatialPivotScale I H L) (fun _ => H)
        (fun _ => H / L) hS (fun _ => hH) (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)))
    (∀ v, |(∏ _i : Unit ⊕ I, H) * (p v).toReal - w v| ≤ smoothSpatialError N s B L ρ ξ) ∧
    (∀ (t : Finset ((Unit ⊕ I) → ℤ)) (weight : ((Unit ⊕ I) → ℤ) → ℝ)
        (φ : ((Unit ⊕ I) → ℤ) → ℂ),
      (∀ v ∈ t, 0 ≤ weight v) → (∀ v ∈ t, ‖φ v‖ ≤ 1) →
      ‖(𝔼 v ∈ t, ((weight v * ((∏ _i : Unit ⊕ I, H) * (p v).toReal) : ℝ) : ℂ) * φ v) -
        (𝔼 v ∈ t, ((weight v * w v : ℝ) : ℂ) * φ v)‖ ≤
          smoothSpatialError N s B L ρ ξ * (𝔼 v ∈ t, weight v)) := by
  have hfull : LipschitzWith
      ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz)
      (splitFreeProfile (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)) := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_lipschitz _ _
  have hbound : ∀ p, ‖splitFreeProfile
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N) p‖ ≤ 1 := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_norm_le _ _
  have hmass : (2 * max (1 : ℝ) 1 + 2) ^
      (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
      ((((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) *
        probabilityProfileLipschitz) : ℝ≥0) : ℝ) *
      ((((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I) / ρ) ≤ 1 / 2 := by
    simpa only [max_self, show (2 : ℝ) * 1 + 2 = 4 by norm_num,
      NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmallMass
  obtain ⟨hM, h⟩ := scalarSpatial_probability_comparison s x root hB hL hH hx hroot C Q hQ
    hξ0 hξ1 hC (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)
    (fun p => (smoothSplitProfile_range _ _ p).1) (fun n => (smoothProductProfile_range _ n).1)
    (smoothSplitProfile_lipschitz _ _) (smoothProductProfile_contDiff N).continuous hfull
    zero_le_one zero_le_one hρ zero_le_one hscale hscaleQ hsmall
    (smoothSplitProfile_zero_outside _ _) (smoothProductProfile_zero_outside _)
    (smoothSplitProfile_integral _ _) (smoothProductProfile_integral _) hmass hbound
  simpa only [splitFreeProfile_smooth, max_self, mul_one, smoothSpatialError,
    smoothIntegerImagePMF] using h

end Erdos3

end

end OAI
