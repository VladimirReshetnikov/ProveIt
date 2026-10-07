/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

noncomputable def fixedSpatialKernelBlockEquiv (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) : (X → ℝ) ≃L[ℝ] (X → ℝ) :=
  Classical.choose (matrixSupCLM_inverse_spec (fixedSpatialKernelBlock e W L z b) h).1

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_coe (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) :
    (fixedSpatialKernelBlockEquiv e W L z b h).toContinuousLinearMap =
      matrixSupCLM (fixedSpatialKernelBlock e W L z b) :=
  Classical.choose_spec (matrixSupCLM_inverse_spec (fixedSpatialKernelBlock e W L z b) h).1

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_apply (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) (t : X → ℝ) :
    fixedSpatialKernelBlockEquiv e W L z b h t =
      (fixedSpatialKernelBlock e W L z b).mulVec t :=
  congrArg (fun f : (X → ℝ) →L[ℝ] (X → ℝ) => f t)
    (fixedSpatialKernelBlockEquiv_coe e W L z b h)

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_jacobian (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) :
    inverseJacobian (fixedSpatialKernelBlockEquiv e W L z b h) =
      |(fixedSpatialKernelBlock e W L z b).det|⁻¹ := by
  rw [inverseJacobian_eq]
  congr 2
  change LinearMap.det (fixedSpatialKernelBlockEquiv e W L z b h).toContinuousLinearMap.toLinearMap = _
  rw [fixedSpatialKernelBlockEquiv_coe]
  exact LinearMap.det_toLin' _

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

noncomputable def fixedSpatialKernelDensity : (X → ℝ) → ℝ :=
  fixedSpatialBlockDensity (unitBoxMeasure T) (fun x => z (none,x))
    (fixedSpatialKernelRest e W L z)
    (fixedSpatialKernelBlockEquiv e W L z false h0)
    (fixedSpatialKernelBlockEquiv e W L z true h1)

omit [Fintype G] in
theorem fixedSpatialKernelDensity_bounds :
    (∀ x, fixedSpatialKernelDensity e W L z h0 h1 x ∈ Set.Icc (0 : ℝ)
      (fixedSpatialBlockDensityCap (fixedSpatialKernelBlockEquiv e W L z true h1))) ∧
      LipschitzWith (fixedSpatialBlockDensityLipschitz
        (fixedSpatialKernelBlockEquiv e W L z false h0)
        (fixedSpatialKernelBlockEquiv e W L z true h1))
        (fixedSpatialKernelDensity e W L z h0 h1) :=
  fixedSpatialBlockDensity_bounds (unitBoxMeasure T) _
    (fixedSpatialKernelRest_measurable e W L z) _ _

omit [Fintype G] in
theorem fixedSpatialKernelDensity_probability_density :
    (∀ x, 0 ≤ fixedSpatialKernelDensity e W L z h0 h1 x) ∧
      Integrable (fixedSpatialKernelDensity e W L z h0 h1) ∧
      (∫ x, fixedSpatialKernelDensity e W L z h0 h1 x) = 1 :=
  fixedSpatialBlockDensity_probability_density (unitBoxMeasure T) _
    (fixedSpatialKernelRest_measurable e W L z) _ _

omit [Fintype G] in
theorem fixedSpatialKernelDensity_probability :
    IsProbabilityMeasure (realDensityMeasure volume (fixedSpatialKernelDensity e W L z h0 h1)) :=
  fixedSpatialBlockDensity_probability (unitBoxMeasure T) _
    (fixedSpatialKernelRest_measurable e W L z) _ _

theorem fixedSpatialKernelDensity_image_law :
    (unitBoxMeasure G).map (fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) =
      realDensityMeasure volume (fixedSpatialKernelDensity e W L z h0 h1) :=
  fixedSpatialKernelMap_block_image_law e W L z _ _
    (fixedSpatialKernelBlockEquiv_apply e W L z false h0)
    (fixedSpatialKernelBlockEquiv_apply e W L z true h1)

omit [Fintype G] in
theorem fixedSpatialKernelDensity_bounds_of_det
    {H κ0 κ1 : ℝ} (hH : 0 ≤ H) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|) :
    (∀ x, fixedSpatialKernelDensity e W L z h0 h1 x ∈ Set.Icc (0 : ℝ) κ1⁻¹) ∧
      LipschitzWith
        (2 * (Fintype.card X : ℝ≥0) * Real.toNNReal (κ1⁻¹) *
          Real.toNNReal (Fintype.card X * ((Fintype.card X).factorial *
            H ^ (Fintype.card X - 1) / κ0)))
        (fixedSpatialKernelDensity e W L z h0 h1) := by
  have hcap : inverseJacobian (fixedSpatialKernelBlockEquiv e W L z true h1) ≤ κ1⁻¹ := by
    rw [fixedSpatialKernelBlockEquiv_jacobian]
    exact inv_anti₀ hκ1 hdet1
  have hnorm : ‖(fixedSpatialKernelBlockEquiv e W L z false h0).symm.toContinuousLinearMap‖ ≤
      Fintype.card X * ((Fintype.card X).factorial * H ^ (Fintype.card X - 1) / κ0) := by
    have h := (matrixSupCLM_inverse_norm_le (fixedSpatialKernelBlock e W L z false)
      hH hentry hκ0 hdet0).2
    rw [← fixedSpatialKernelBlockEquiv_coe e W L z false h0,
      ContinuousLinearMap.inverse_equiv] at h
    exact h
  have h := fixedSpatialBlockDensity_bounds_of_inverseBounds (unitBoxMeasure T)
    (fun x => z (none,x)) (fixedSpatialKernelRest_measurable e W L z)
    (fixedSpatialKernelBlockEquiv e W L z false h0)
    (fixedSpatialKernelBlockEquiv e W L z true h1)
    (Real.toNNReal (κ1⁻¹))
    (Real.toNNReal (Fintype.card X * ((Fintype.card X).factorial * H ^ (Fintype.card X - 1) / κ0)))
    (by simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr hκ1.le)] using hcap)
    (by simpa only [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ Fintype.card X *
      ((Fintype.card X).factorial * H ^ (Fintype.card X - 1) / κ0))] using hnorm)
  simpa only [fixedSpatialKernelDensity, Real.coe_toNNReal _ (inv_nonneg.mpr hκ1.le)] using h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

theorem fixedSpatialKernelMap_norm_le_two {W L : ℝ}
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (z : Option G × X → ℝ) (hz : ∀ a, |z a| ≤ 1)
    (t : G → ℝ) (ht : ‖t‖ ≤ 1) :
    ‖fixedSpatialKernelMap W L z t‖ ≤ 2 := by
  have hLip := fixedSpatialKernelMap_lipschitz_one hW hL hsize z (fun g x => hz (some g,x))
  have hd : dist (fixedSpatialKernelMap W L z t) (fixedSpatialKernelMap W L z 0) ≤ 1 := by
    have h := hLip.dist_le_mul t 0
    simp only [NNReal.coe_one, one_mul, dist_zero_right] at h
    exact h.trans ht
  have hzero : ‖fixedSpatialKernelMap W L z 0‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro a
    simpa only [fixedSpatialKernelMap, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero, Real.norm_eq_abs] using hz (none,a.1)
  calc
    _ ≤ ‖fixedSpatialKernelMap W L z t - fixedSpatialKernelMap W L z 0‖ +
        ‖fixedSpatialKernelMap W L z 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + 1 := add_le_add (by simpa only [dist_eq_norm] using hd) hzero
    _ = 2 := by norm_num

variable {T : Type*} [Fintype T] [DecidableEq X]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

theorem fixedSpatialKernelDensity_zero_of_norm_gt_two
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (y : X → ℝ) (hy : 2 < ‖y‖) :
    fixedSpatialKernelDensity e W L z h0 h1 y = 0 := by
  let F := fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩
  have hF : Measurable F := by unfold F fixedSpatialKernelMap; fun_prop
  apply continuousDensity_zero_off_closed (S := Metric.closedBall 0 2) volume _
    (fixedSpatialKernelDensity_bounds e W L z h0 h1).2.continuous
    (fixedSpatialKernelDensity_probability_density e W L z h0 h1).1
    (Metric.isClosed_closedBall) ?_ y ?_
  · rw [← fixedSpatialKernelDensity_image_law]
    apply (ae_map_iff hF.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
    filter_upwards [unitBoxMeasure_ae (ι := G)] with t ht
    simp only [dist_zero_right]
    have htnorm : ‖t‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      (fun g => by rw [Real.norm_eq_abs, abs_of_pos (ht g).1]; exact (ht g).2)
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro x
    exact (norm_le_pi_norm _ ⟨x, .inl ()⟩).trans
      (fixedSpatialKernelMap_norm_le_two hW hL hsize z hz t htnorm)
  · simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem columnScaledEquiv_symm_apply {X : Type*} [Fintype X]
    (A C : (X → ℝ) ≃L[ℝ] (X → ℝ)) (width : X → ℝ)
    (hscale : ∀ v, C v = A (fun i => width i * v i))
    (hwidth : ∀ i, width i ≠ 0) (y : X → ℝ) (i : X) :
    C.symm y i = A.symm y i / width i := by
  have hscaled : (fun j => width j * C.symm y j) = A.symm y := by
    apply A.injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hscale (C.symm y)).symm
  apply (eq_div_iff (hwidth i)).mpr
  simpa only [mul_comm] using congrFun hscaled i

theorem columnScaledEquiv_inverse_norm_le {X : Type*} [Fintype X]
    (A C : (X → ℝ) ≃L[ℝ] (X → ℝ)) (width : X → ℝ)
    (hscale : ∀ v, C v = A (fun i => width i * v i))
    {δ : ℝ} (hδ : 0 < δ) (hwidth : ∀ i, δ ≤ width i) :
    ‖C.symm.toContinuousLinearMap‖ ≤ δ⁻¹ * ‖A.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _))
  intro y
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖C.symm y i‖ ≤ _
  rw [columnScaledEquiv_symm_apply A C width hscale
    (fun j => (hδ.trans_le (hwidth j)).ne') y i,
    Real.norm_eq_abs, abs_div, abs_of_pos (hδ.trans_le (hwidth i))]
  have hcoord0 : |A.symm y i| ≤ ‖A.symm y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A.symm y) i
  have hcoord : |A.symm y i| ≤ ‖A.symm.toContinuousLinearMap‖ * ‖y‖ :=
    hcoord0.trans (A.symm.toContinuousLinearMap.le_opNorm y)
  calc
    _ ≤ (‖A.symm.toContinuousLinearMap‖ * ‖y‖) / width i :=
      div_le_div_of_nonneg_right hcoord (hδ.trans_le (hwidth i)).le
    _ ≤ (‖A.symm.toContinuousLinearMap‖ * ‖y‖) / δ :=
      div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hδ (hwidth i)
    _ = _ := by ring

variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]

theorem fixedSpatialKernelBlockEquiv_slice_apply
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (lower width : G → ℝ) (second : Bool)
    (hbase : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hslice : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0)
    (v : X → ℝ) :
    fixedSpatialKernelBlockEquiv e W L (fixedSpatialKernelSliceFrame W L z lower width) second hslice v =
      fixedSpatialKernelBlockEquiv e W L z second hbase
        (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) * v i) := by
  rw [fixedSpatialKernelBlockEquiv_apply, fixedSpatialKernelBlockEquiv_apply]
  rw [fixedSpatialKernelBlock_slice]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fixedSpatialKernelBlockEquiv_slice_inverse_norm_le
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (lower width : G → ℝ) (second : Bool)
    (hbase : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hslice : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : ∀ g, δ ≤ width g) :
    ‖(fixedSpatialKernelBlockEquiv e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second hslice).symm.toContinuousLinearMap‖ ≤
      δ⁻¹ * ‖(fixedSpatialKernelBlockEquiv e W L z second hbase).symm.toContinuousLinearMap‖ := by
  apply columnScaledEquiv_inverse_norm_le
    (fixedSpatialKernelBlockEquiv e W L z second hbase)
    (fixedSpatialKernelBlockEquiv e W L (fixedSpatialKernelSliceFrame W L z lower width) second hslice)
    (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)))
    (fixedSpatialKernelBlockEquiv_slice_apply e W L z lower width second hbase hslice) hδ
  intro i
  exact hwidth _

theorem fixedSpatialKernelBlockEquiv_slice_inverseJacobian_le
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (lower width : G → ℝ) (second : Bool)
    (hbase : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hslice : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : ∀ g, δ ≤ width g) :
    inverseJacobian (fixedSpatialKernelBlockEquiv e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second hslice) ≤
      (δ⁻¹) ^ Fintype.card X *
        inverseJacobian (fixedSpatialKernelBlockEquiv e W L z second hbase) := by
  let w : X → ℝ := fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))
  have hw : ∀ i, 0 < w i := fun i => hδ.trans_le (hwidth _)
  have hprod : δ ^ Fintype.card X ≤ ∏ i, w i := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => hδ.le) (fun i _ => hwidth
        (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))))
  have hmatrix : fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second =
      fixedSpatialKernelBlock e W L z second * Matrix.diagonal w := by
    ext x i
    rw [fixedSpatialKernelBlock_slice, Matrix.mul_diagonal]
  have hdet : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det =
      (fixedSpatialKernelBlock e W L z second).det * ∏ i, w i := by
    rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
  rw [fixedSpatialKernelBlockEquiv_jacobian, fixedSpatialKernelBlockEquiv_jacobian,
    hdet, abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hw i).le)), mul_inv_rev]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (abs_nonneg _))
  simpa only [← inv_pow] using inv_anti₀ (pow_pos hδ _) hprod

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lower width : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hw : ∀ g, width g ≠ 0)
local notation "frame" => fixedSpatialKernelSliceFrame W L z lower width
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width false h0 hw
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width true h1 hw

noncomputable def fixedSpatialKernelSliceDensity : (X → ℝ) → ℝ :=
  fixedSpatialKernelDensity e W L frame h0slice h1slice

local notation "density" => fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw

theorem fixedSpatialKernelSliceDensity_image_law :
    (unitBoxMeasure G).map (fun t x =>
      fixedSpatialKernelMap W L z (fun g => lower g + width g * t g) ⟨x, .inl ()⟩) =
      realDensityMeasure volume density := by
  simpa only [fixedSpatialKernelSliceDensity, fixedSpatialKernelMap_slice] using
    fixedSpatialKernelDensity_image_law e W L frame h0slice h1slice

theorem fixedSpatialKernelSliceDensity_probability_data :
    (∀ y, 0 ≤ density y) ∧ Integrable density ∧ (∫ y, density y) = 1 :=
  fixedSpatialKernelDensity_probability_density e W L frame h0slice h1slice

theorem fixedSpatialKernelSliceDensity_bounds :
    (∀ y, density y ∈ Set.Icc (0 : ℝ)
      (fixedSpatialBlockDensityCap (fixedSpatialKernelBlockEquiv e W L frame true h1slice))) ∧
    LipschitzWith (fixedSpatialBlockDensityLipschitz
      (fixedSpatialKernelBlockEquiv e W L frame false h0slice)
      (fixedSpatialKernelBlockEquiv e W L frame true h1slice)) density :=
  fixedSpatialKernelDensity_bounds e W L frame h0slice h1slice

omit [Fintype T] in

theorem fixedSpatialKernelBlock_slice_det_lower (second : Bool)
    {κ δ : ℝ} (hδ : 0 < δ)
    (hmin : ∀ g, δ ≤ width g)
    (hdet : κ ≤ |(fixedSpatialKernelBlock e W L z second).det|) :
    κ * δ ^ Fintype.card X ≤ |(fixedSpatialKernelBlock e W L frame second).det| := by
  rw [fixedSpatialKernelBlock_slice_det, abs_mul]
  have hprod : δ ^ Fintype.card X ≤
      ∏ i : X, width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
    calc
      _ = ∏ _i : X, δ := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hδ.le) (fun i _ => hmin _)
  have hp : 0 ≤ ∏ i : X, width (e.symm
      (if second then Sum.inr (Sum.inl i) else Sum.inl i)) :=
    Finset.prod_nonneg (fun i _ => hδ.le.trans (hmin _))
  rw [abs_of_nonneg hp]
  exact mul_le_mul hdet hprod (pow_nonneg hδ.le _) (abs_nonneg _)

omit [Fintype X] [Fintype T] in
theorem fixedSpatialKernelBlock_slice_entry_bound
    {H : ℝ} (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hwidth : ∀ g, 0 ≤ width g ∧ width g ≤ 1) :
    ∀ i j, |fixedSpatialKernelBlock e W L frame false i j| ≤ H := by
  intro i j
  rw [fixedSpatialKernelBlock_slice]
  dsimp only
  rw [abs_mul, abs_of_nonneg (hwidth _).1]
  exact (mul_le_mul_of_nonneg_left (hwidth _).2 (abs_nonneg _)).trans
    (by simpa only [mul_one] using hentry i j)

theorem fixedSpatialKernelSliceDensity_bounds_of_det
    {H κ0 κ1 δ : ℝ} (hH : 0 ≤ H) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1) (hδ : 0 < δ)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|)
    (hmin : ∀ g, δ ≤ width g) (hmax : ∀ g, width g ≤ 1) :
    (∀ y, density y ∈ Set.Icc (0 : ℝ) (κ1 * δ ^ Fintype.card X)⁻¹) ∧
    LipschitzWith
      (2 * (Fintype.card X : ℝ≥0) * Real.toNNReal ((κ1 * δ ^ Fintype.card X)⁻¹) *
        Real.toNNReal (Fintype.card X * ((Fintype.card X).factorial *
          H ^ (Fintype.card X - 1) / (κ0 * δ ^ Fintype.card X)))) density := by
  exact fixedSpatialKernelDensity_bounds_of_det e W L frame h0slice h1slice hH
    (mul_pos hκ0 (pow_pos hδ _)) (mul_pos hκ1 (pow_pos hδ _))
    (fixedSpatialKernelBlock_slice_entry_bound e W L z lower width hentry
      (fun g => ⟨hδ.le.trans (hmin g), hmax g⟩))
    (fixedSpatialKernelBlock_slice_det_lower e W L z lower width false hδ hmin hdet0)
    (fixedSpatialKernelBlock_slice_det_lower e W L z lower width true hδ hmin hdet1)

theorem fixedSpatialKernelSliceDensity_zero_of_norm_gt_two
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (hl : ∀ g, 0 ≤ lower g)
    (hw0 : ∀ g, 0 ≤ width g) (hcontained : ∀ g, lower g + width g ≤ 1)
    (y : X → ℝ) (hy : 2 < ‖y‖) : density y = 0 := by
  let F := fun (t : G → ℝ) x => fixedSpatialKernelMap W L z
    (fun g => lower g + width g * t g) ⟨x, .inl ()⟩
  have hF : Measurable F := by unfold F fixedSpatialKernelMap; fun_prop
  apply continuousDensity_zero_off_closed (S := Metric.closedBall 0 2) volume _
    (fixedSpatialKernelSliceDensity_bounds e W L z lower width h0 h1 hw).2.continuous
    (fixedSpatialKernelSliceDensity_probability_data e W L z lower width h0 h1 hw).1
    Metric.isClosed_closedBall ?_ y ?_
  · rw [← fixedSpatialKernelSliceDensity_image_law]
    apply (ae_map_iff hF.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
    filter_upwards [unitBoxMeasure_ae (ι := G)] with t ht
    simp only [dist_zero_right]
    have htnorm : ‖fun g => lower g + width g * t g‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro g
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hl g) (mul_nonneg (hw0 g) (ht g).1.le))]
      have hmul : width g * t g ≤ width g := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht g).2 (hw0 g)
      exact (add_le_add (le_refl (lower g)) hmul).trans (hcontained g)
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro x
    exact (norm_le_pi_norm _ ⟨x, .inl ()⟩).trans
      (fixedSpatialKernelMap_norm_le_two hW hL hsize z hz _ htnorm)
  · simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

end Erdos3

end

end OAI
