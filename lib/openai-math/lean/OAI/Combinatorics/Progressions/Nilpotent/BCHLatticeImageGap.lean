/- Modified for ProveIt: use the older manifold derivative lemma, handle
all conversion goals, and remove a closed-goal tactic on Lean 4.32.
Mathematical statements are unchanged. -/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import OAI.Combinatorics.Progressions.Geometry.RiemannianLocalCoordinates
import OAI.Combinatorics.Progressions.Linear.BasisCoordinateBounds
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientChart

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem rightVelocity_mapReal (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)
    (g : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity f (mapReal (hM := hM) φ g)).comp (basisCoordinateMap e f φ.toLinearMap) =
      (basisCoordinateMap e f φ.toLinearMap).comp (rightVelocity e g) := by
  let A := basisCoordinateMap e f φ.toLinearMap
  have hc : rightTranslate f (mapReal (hM := hM) φ g⁻¹) ∘ A = A ∘ rightTranslate e g⁻¹ := by
    funext x
    exact (basisCoordinateMap_rightTranslate e f φ g⁻¹ x).symm
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  have ho := (contDiff_rightTranslate f (mapReal (hM := hM) φ g⁻¹) 1).differentiable (by decide)
  have hd := congrArg (fun F : (ι → ℝ) → (κ → ℝ) => fderiv ℝ F (basisHomeomorph e g)) hc
  rw [fderiv_comp _ ho.differentiableAt A.differentiableAt,
    fderiv_comp _ A.differentiableAt hi.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
  dsimp only [A] at hd
  rw [← mapReal_basisHomeomorph e f φ, map_inv] at hd
  exact hd

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

section Norm

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem norm_tangent_eq_coordinateL2Norm (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g, ‖v‖ = coordinateL2Norm (rightVelocity e g v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  rw [norm_eq_sqrt_real_inner]
  change Real.sqrt (rightInnerForm e g v v) = _
  simpa only [coordinateL2Norm, pow_two] using
    congrArg Real.sqrt (rightInnerForm_apply e g v v)

end Norm

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem norm_mfderiv_mapReal_le {C : ℝ}
    (hA : ∀ w, coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap w) ≤ C * coordinateL2Norm w)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hM) f
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v‖ ≤ C * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  intro v
  have hv := mfderiv_mapReal_coordinates (hM := hM) e f φ g v
  have hc := congrArg (fun T : (ι → ℝ) →L[ℝ] (κ → ℝ) => T v)
    (rightVelocity_mapReal (hM := hM) e f φ g)
  have hvel := (congrArg (fun w : κ → ℝ => rightVelocity f (mapReal (hM := hM) φ g) w) hv).trans hc
  calc
    ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v‖ =
        coordinateL2Norm (rightVelocity f (mapReal (hM := hM) φ g)
          (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v)) :=
      norm_tangent_eq_coordinateL2Norm f _ _
    _ = coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap (rightVelocity e g v)) :=
      congrArg coordinateL2Norm hvel
    _ ≤ C * coordinateL2Norm (rightVelocity e g v) := hA _
    _ = C * ‖v‖ := congrArg (C * ·) (norm_tangent_eq_coordinateL2Norm e g v).symm

theorem lipschitz_mapReal_of_coordinate_bound {C : ℝ≥0} (hC : 0 < C)
    (hA : ∀ w, coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap w) ≤ C * coordinateL2Norm w) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith C (mapReal (hnil := hnil) (hM := hM) φ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  apply riemannianEDist_le_mul_of_mfderiv_bound hC (contMDiff_mapReal e f φ 1)
  intro g v
  have h := ENNReal.ofReal_le_ofReal (norm_mfderiv_mapReal_le (hM := hM) e f φ hA g v)
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s t : ℕ} (e : Basis ι ℝ L)
  (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)

theorem lipschitz_changeStep :
    letI := rightMetricSpace (hnil := hs) e
    letI := rightMetricSpace (hnil := ht) e
    LipschitzWith 1 (changeStep hs ht) := by
  apply lipschitz_mapReal_of_coordinate_bound (hnil := hs) (hM := ht)
    e e (LieHom.id : L →ₗ⁅ℝ⁆ L) (by norm_num : (0 : ℝ≥0) < 1)
  intro w
  change coordinateL2Norm (e.equivFun (e.equivFun.symm w)) ≤ 1 * coordinateL2Norm w
  rw [LinearEquiv.apply_symm_apply, one_mul]

theorem isometry_changeStep :
    letI := rightMetricSpace (hnil := hs) e
    letI := rightMetricSpace (hnil := ht) e
    Isometry (changeStep hs ht) := by
  let := rightMetricSpace (hnil := hs) e
  let := rightMetricSpace (hnil := ht) e
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using (lipschitz_changeStep e hs ht).dist_le_mul x y
  · have h := (lipschitz_changeStep e ht hs).dist_le_mul (changeStep hs ht x) (changeStep hs ht y)
    rw [show changeStep ht hs (changeStep hs ht x) = x from rfl,
      show changeStep ht hs (changeStep hs ht y) = y from rfl] at h
    simpa only [NNReal.coe_one, one_mul] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem rightTranslate_fderiv_zero_rightVelocity (e : Basis ι ℝ L)
    (g : NilpotentLieBCHGroup L s hnil) :
    (fderiv ℝ (rightTranslate e g) 0).comp (rightVelocity e g) =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h := rightTranslate_fderiv_leftInverse e g⁻¹ (basisHomeomorph e g)
  rw [rightTranslate_coordinates, mul_inv_cancel] at h
  simpa only [inv_inv, rightTranslate_coordinates, mul_inv_cancel, basisHomeomorph_apply,
    coord_one, map_zero, rightVelocity] using h

theorem coordinate_norm_le_rightVelocity (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) (v : ι → ℝ) :
    ‖v‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * coordinateL2Norm (rightVelocity e g v) := by
  have h := congrArg (fun A : (ι → ℝ) →L[ℝ] (ι → ℝ) => A v)
    (rightTranslate_fderiv_zero_rightVelocity e g)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  calc
    ‖v‖ = ‖fderiv ℝ (rightTranslate e g) 0 (rightVelocity e g v)‖ := congrArg norm h.symm
    _ ≤ ‖fderiv ℝ (rightTranslate e g) 0‖ * ‖rightVelocity e g v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * coordinateL2Norm (rightVelocity e g v) :=
      mul_le_mul (norm_fderiv_rightTranslate_zero_le e c hstructure hc g B hB hg)
        (norm_le_coordinateL2Norm _) (norm_nonneg _) (bchBoxCoordinateBound_nonneg _ _ _ (by linarith))

omit [IsScalarTower ℚ ℝ L] in
theorem mfderiv_basisHomeomorph_coordinates (e : Basis ι ℝ L)
    (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v = v := by
  let := basisChartedSpace (hnil := hnil) e
  have hm := (contMDiff_basisHomeomorph (hnil := hnil) e 1).mdifferentiableAt (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) g (basisHomeomorph e) = id := by
    funext x
    simp only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_symm_apply,
      extChartAt_model_space_eq_id, Homeomorph.apply_symm_apply, id_eq]
    rfl
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, fderiv_id]
  rfl

theorem norm_mfderiv_basisHomeomorph_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v)‖ ≤
        bchBoxCoordinateBound s (Fintype.card ι) H B * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  have hcoords : tangentModelVector
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v) = tangentModelVector v :=
    mfderiv_basisHomeomorph_coordinates e g v
  apply (congrArg norm hcoords).le.trans
  exact (coordinate_norm_le_rightVelocity e c hstructure hc g B hB hg v).trans_eq
    (congrArg (bchBoxCoordinateBound s (Fintype.card ι) H B * ·)
      (norm_tangent_eq_coordinateL2Norm e g v).symm)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def coordinateLine (e : Basis ι ℝ L) (v : ι → ℝ) (t : ℝ) :
    NilpotentLieBCHGroup L s hnil := (basisHomeomorph e).symm (t • v)

variable (e : Basis ι ℝ L) (v : ι → ℝ)

@[simp] theorem coordinateLine_zero : coordinateLine (hnil := hnil) e v 0 = 1 := by
  apply ext
  change e.equivFun.symm ((0 : ℝ) • v) = 0
  simp only [zero_smul, map_zero]

@[simp] theorem coordinateLine_one :
    coordinateLine (hnil := hnil) e v 1 = (basisHomeomorph e).symm v := by
  simp only [coordinateLine, one_smul]

theorem contMDiff_coordinateLine (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) n (coordinateLine (hnil := hnil) e v) := by
  let := basisChartedSpace (hnil := hnil) e
  exact (contMDiff_basisHomeomorph_symm e n).comp (contMDiff_id.smul contMDiff_const)

theorem rightTranslate_coordinateLine_inv (t u : ℝ) :
    rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ (u • v) = (u - t) • v := by
  change e.equivFun (lieBCH s (e.equivFun.symm (u • v)) (-e.equivFun.symm (t • v))) = _
  rw [map_smul, map_smul, lieBCH_eq_add_of_lie_eq_zero hnil (by simp [smul_lie, lie_smul])]
  simp only [map_add, map_neg, map_smul, LinearEquiv.apply_symm_apply, sub_eq_add_neg, add_smul, neg_smul]

variable [IsScalarTower ℚ ℝ L]

theorem rightVelocity_coordinateLine (t : ℝ) :
    rightVelocity e (coordinateLine (hnil := hnil) e v t) v = v := by
  have hl : HasDerivAt (fun u : ℝ => u • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hr := ((contDiff_rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ 1).differentiable
    one_ne_zero).differentiableAt (x := t • v) |>.hasFDerivAt
  have hcomp := hr.comp_hasDerivAt t hl
  have heq : rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ ∘ (fun u : ℝ => u • v) =
      fun u : ℝ => (u - t) • v := funext (rightTranslate_coordinateLine_inv e v t)
  rw [heq] at hcomp
  have hd : HasDerivAt (fun u : ℝ => (u - t) • v) v t := by
    simpa using ((hasDerivAt_id t).sub_const t).smul_const v
  simpa only [rightVelocity, coordinateLine, Homeomorph.apply_symm_apply] using hcomp.unique hd

omit [IsScalarTower ℚ ℝ L] in
theorem mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1 = v := by
  let := basisChartedSpace (hnil := hnil) e
  have hm := (contMDiff_coordinateLine (hnil := hnil) e v 1).mdifferentiableAt (x := t) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) t (coordinateLine (hnil := hnil) e v) =
      fun u : ℝ => u • v := by
    funext u
    simp [writtenInExtChartAt, coordinateLine]
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change deriv (fun u : ℝ => u • v) t = v
  exact (show HasDerivAt (fun u : ℝ => u • v) v t by
    simpa using (hasDerivAt_id t).smul_const v).deriv

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)
  (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hA : homCoordinates e f φ = A)

include hA

theorem linear_hom_basisHomeomorph (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph f (φ g) = A (basisHomeomorph e g) := by
  rw [← homCoordinates_apply e f φ, hA]

theorem contMDiff_linear_hom (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) n φ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph f).isOpenEmbedding
  have hc := A.contDiff.contMDiff.comp (contMDiff_basisHomeomorph (hnil := hnil) e n)
  convert hc using 1 <;> try rfl
  funext g
  exact linear_hom_basisHomeomorph e f φ A hA g

theorem mfderiv_linear_hom_coordinates (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v = A v := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  have hm := (contMDiff_linear_hom e f φ A hA 1).mdifferentiableAt (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) g φ = A := by
    funext x
    simpa only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_apply,
      basis_extChartAt_symm_apply, homCoordinates] using congrFun hA x
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, ContinuousLinearMap.fderiv]
  rfl

variable [IsScalarTower ℚ ℝ L] [IsScalarTower ℚ ℝ M]

theorem rightVelocity_linear_hom (g : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity f (φ g)).comp A = A.comp (rightVelocity e g) := by
  have hc : rightTranslate f (φ g⁻¹) ∘ A = A ∘ rightTranslate e g⁻¹ := by
    funext v
    have h := homCoordinates_rightTranslate e f φ g⁻¹ v
    rw [hA] at h
    exact h.symm
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  have ho := (contDiff_rightTranslate f (φ g⁻¹) 1).differentiable (by decide)
  have hd := congrArg (fun F : (ι → ℝ) → (κ → ℝ) => fderiv ℝ F (basisHomeomorph e g)) hc
  rw [fderiv_comp _ ho.differentiableAt A.differentiableAt,
    fderiv_comp _ A.differentiableAt hi.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
  rw [← linear_hom_basisHomeomorph e f φ A hA, map_inv] at hd
  exact hd

theorem norm_mfderiv_linear_hom_le {C : ℝ}
    (hbound : ∀ w, coordinateL2Norm (A w) ≤ C * coordinateL2Norm w)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hM) f
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v‖ ≤ C * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  intro v
  have hv := mfderiv_linear_hom_coordinates e f φ A hA g v
  have hc := congrArg (fun T : (ι → ℝ) →L[ℝ] (κ → ℝ) => T v)
    (rightVelocity_linear_hom e f φ A hA g)
  have hvel := (congrArg (fun w : κ → ℝ => rightVelocity f (φ g) w) hv).trans hc
  calc
    _ = coordinateL2Norm (rightVelocity f (φ g)
        (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v)) := norm_tangent_eq_coordinateL2Norm f _ _
    _ = coordinateL2Norm (A (rightVelocity e g v)) := congrArg coordinateL2Norm hvel
    _ ≤ C * coordinateL2Norm (rightVelocity e g v) := hbound _
    _ = C * ‖v‖ := congrArg (C * ·) (norm_tangent_eq_coordinateL2Norm e g v).symm

theorem lipschitz_linear_hom {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ w, coordinateL2Norm (A w) ≤ C * coordinateL2Norm w) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith C φ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  apply riemannianEDist_le_mul_of_mfderiv_bound hC (contMDiff_linear_hom e f φ A hA 1)
  intro g v
  have h := ENNReal.ofReal_le_ofReal (norm_mfderiv_linear_hom_le e f φ A hA hbound g v)
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

noncomputable def bchLogMetricConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨bchBoxCoordinateBound s d H B + 1,
    add_nonneg (bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg) zero_le_one⟩

theorem bchLogMetricConstant_pos (s d H : ℕ) (B : ℝ≥0) : 0 < bchLogMetricConstant s d H B := by
  change 0 < bchBoxCoordinateBound s d H B + 1
  have := bchBoxCoordinateBound_nonneg s d H B.coe_nonneg
  linarith

namespace NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem edist_coordinates_le_of_near_one (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H B
    (C : ℝ≥0∞) * edist 1 g < B →
      edist (basisHomeomorph (hnil := hnil) e 1) (basisHomeomorph e g) ≤ C * edist 1 g := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H B
  dsimp only
  intro hnear
  apply coordinate_edist_le_of_riemannianEDist_lt (bchLogMetricConstant_pos s (Fintype.card ι) H B)
    (contMDiff_basisHomeomorph e 1) 1 g ?_ hnear
  intro z hz v
  have hznorm : ‖basisHomeomorph e z‖ ≤ B := by
    simpa only [Metric.mem_closedBall, basisHomeomorph_apply, coord_one, map_zero,
      dist_zero_right] using hz
  have hzbox (i) : |e.repr z.coord i| ≤ B := by
    have hi := (norm_le_pi_norm (basisHomeomorph e z) i).trans hznorm
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using hi
  have hv := norm_mfderiv_basisHomeomorph_le e c hstructure hc z B hB hzbox v
  have hAC : bchBoxCoordinateBound s (Fintype.card ι) H B ≤ (C : ℝ) := by
    change bchBoxCoordinateBound s (Fintype.card ι) H B ≤ bchBoxCoordinateBound s (Fintype.card ι) H B + 1
    linarith
  have hv' := hv.trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg v))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ofReal_norm, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal hv'

theorem norm_coordinates_le_of_near_one (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H B
    (C : ℝ) * dist 1 g < B → ‖basisHomeomorph e g‖ ≤ C * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H B
  dsimp only
  intro hnear
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hnearE : (C : ℝ≥0∞) * edist 1 g < B := by
    have h : ENNReal.ofReal ((C : ℝ) * dist 1 g) < ENNReal.ofReal (B : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hnear
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
    simpa only [edist_dist] using h
  have h := edist_coordinates_le_of_near_one e c hstructure hc B hB g hnearE
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top 1 g)) h
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    basisHomeomorph_apply, coord_one, map_zero, dist_zero_left,
    ENNReal.toReal_ofReal (norm_nonneg _)] using hr

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def bchInverseBoxConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  (⟨bchBoxCoordinateBound s d H B, bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg⟩ + 2 * B) *
    bchLogMetricConstant s d H 1

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_bchInverseBoxConstant
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g h : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) (hh : ∀ i, |e.repr h.coord i| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
      bchInverseBoxConstant s (Fintype.card ι) H B * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let A := bchBoxCoordinateBound s (Fintype.card ι) H B
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  have hA : 0 ≤ A := bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg
  change dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
    (A + 2 * (B : ℝ)) * (C : ℝ) * dist g h
  by_cases hnear : (C : ℝ) * dist g h < 1
  · let z := h * g⁻¹
    have hdist : dist 1 z = dist g h := by
      simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
    have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
      have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
      simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
    have hzbox : ∀ i, |basisHomeomorph e z i| ≤ B := by
      intro i
      have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
      exact ((hi.trans hz).trans hnear.le).trans hB
    have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
      simp only [basisHomeomorph_apply, coord_one, map_zero]
    have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
      rw [← hzero, rightTranslate_coordinates, one_mul]
    have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
    have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg).dist_le_mul
      (basisHomeomorph e z) hzbox 0
      (show ∀ i, |(0 : ι → ℝ) i| ≤ (B : ℝ) by simpa only [Pi.zero_apply, abs_zero] using fun _ : ι => B.coe_nonneg)
    have hfirst : dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ A * ‖basisHomeomorph e z‖ := by
      rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
      simpa only [NNReal.toReal, dist_comm, A] using hLip
    calc
      _ ≤ A * ‖basisHomeomorph e z‖ := hfirst
      _ ≤ A * ((C : ℝ) * dist g h) := mul_le_mul_of_nonneg_left hz hA
      _ ≤ (A + 2 * (B : ℝ)) * ((C : ℝ) * dist g h) :=
        mul_le_mul_of_nonneg_right (by linarith [B.coe_nonneg]) (by positivity)
      _ = _ := by ring
  · have hdist : dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ 2 * (B : ℝ) := by
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      change |e.repr g.coord i - e.repr h.coord i| ≤ _
      exact (abs_sub _ _).trans (by linarith [hg i, hh i])
    calc
      _ ≤ 2 * (B : ℝ) := hdist
      _ ≤ 2 * (B : ℝ) * ((C : ℝ) * dist g h) :=
        le_mul_of_one_le_right (by positivity) (le_of_not_gt hnear)
      _ ≤ (A + 2 * (B : ℝ)) * ((C : ℝ) * dist g h) := by gcongr; linarith
      _ = _ := by ring

theorem lipschitzOn_basisHomeomorph_box
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (B : ℝ≥0) (hB : 1 ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzOnWith (bchInverseBoxConstant s (Fintype.card ι) H B) (basisHomeomorph (hnil := hnil) e)
      {g | ∀ i, |e.repr g.coord i| ≤ B} := by
  let := rightMetricSpace (hnil := hnil) e
  apply LipschitzOnWith.of_dist_le_mul
  intro g hg h hh
  exact dist_coordinates_le_bchInverseBoxConstant e c hstructure hc B hB g h hg hh

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

noncomputable def bchLatticeSeparationRadius (s d H l : ℕ) : ℝ :=
  1 / ((l : ℝ) + 1) / (bchLogMetricConstant s d H 1 : ℝ)

theorem bchLatticeSeparationRadius_pos (s d H l : ℕ) : 0 < bchLatticeSeparationRadius s d H l := by
  have hC : (0 : ℝ) < bchLogMetricConstant s d H 1 := bchLogMetricConstant_pos _ _ _ _
  unfold bchLatticeSeparationRadius
  positivity

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eq_one_of_subgroup_of_dist_lt (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l)
    (γ : NilpotentLieBCHGroup L s hnil) (hγ : γ ∈ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist 1 γ < bchLatticeSeparationRadius s (Fintype.card ι) H l → γ = 1 := by
  let := rightMetricSpace (hnil := hnil) e
  intro hsmall
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  have hC : (0 : ℝ) < C := bchLogMetricConstant_pos _ _ _ _
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hscaled : (C : ℝ) * dist 1 γ < 1 / ((l : ℝ) + 1) := by
    have h := (lt_div_iff₀ hC).mp hsmall
    simpa only [mul_comm] using h
  have hunit : 1 / ((l : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hn := norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl γ (hscaled.trans_le hunit)
  apply eq_one_of_subgroup_grid_of_small_coordinates e Γ l hl hgrid γ hγ
  intro i
  have hi : |e.repr γ.coord i| ≤ ‖basisHomeomorph e γ‖ := by
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (basisHomeomorph e γ) i
  exact ((hi.trans hn).trans_lt hscaled).trans (one_div_lt_one_div_of_lt hl' (by linarith))

theorem latticeSeparationRadius_le_dist (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l)
    (γ : NilpotentLieBCHGroup L s hnil) (hγ : γ ∈ Γ) (hne : γ ≠ 1) :
    letI := rightMetricSpace (hnil := hnil) e
    bchLatticeSeparationRadius s (Fintype.card ι) H l ≤ dist 1 γ := by
  let := rightMetricSpace (hnil := hnil) e
  by_contra! h
  exact hne (eq_one_of_subgroup_of_dist_lt e c hstructure hc Γ l hl hgrid γ hγ h)

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem one_le_bchLogMetricConstant (s d H : ℕ) (B : ℝ≥0) :
    1 ≤ bchLogMetricConstant s d H B := by
  change (1 : ℝ) ≤ bchBoxCoordinateBound s d H B + 1
  linarith [bchBoxCoordinateBound_nonneg s d H B.coe_nonneg]

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_of_near_box
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g h : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H 1
    (C : ℝ) * dist g h < 1 →
      dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
        bchBoxCoordinateBound s (Fintype.card ι) H B * C * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  dsimp only
  intro hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
  have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
    have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
    simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
  have hzbox (i) : |basisHomeomorph e z i| ≤ B := by
    have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
    exact ((hi.trans hz).trans hnear.le).trans hB
  have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
    simp only [basisHomeomorph_apply, coord_one, map_zero]
  have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
    rw [← hzero, rightTranslate_coordinates, one_mul]
  have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
  have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg).dist_le_mul
    (basisHomeomorph e z) hzbox 0 (by
      intro i
      simpa only [Pi.zero_apply, abs_zero] using B.coe_nonneg)
  rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
  calc
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * ‖basisHomeomorph e z‖ := by
      simpa only [dist_comm, NNReal.toReal] using hLip
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * ((C : ℝ) * dist g h) :=
      mul_le_mul_of_nonneg_left hz (bchBoxCoordinateBound_nonneg s _ H B.coe_nonneg)
    _ = _ := by ring

theorem dist_coordinates_le_of_near_unit_box
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g h : NilpotentLieBCHGroup L s hnil) (hg : ∀ i, |e.repr g.coord i| ≤ 1) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H 1
    (C : ℝ) * dist g h < 1 →
      dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ (C : ℝ) ^ 2 * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  dsimp only
  intro hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
  have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
    have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
    simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
  have hzbox (i) : |basisHomeomorph e z i| ≤ 1 := by
    have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
    exact ((hi.trans hz).trans hnear.le)
  have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
    simp only [basisHomeomorph_apply, coord_one, map_zero]
  have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
    rw [← hzero, rightTranslate_coordinates, one_mul]
  have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
  have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g 1 le_rfl hg).dist_le_mul
    (basisHomeomorph e z) hzbox 0 (by simp)
  rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
  have hAC : bchBoxCoordinateBound s (Fintype.card ι) H 1 ≤ (C : ℝ) := by
    change bchBoxCoordinateBound s (Fintype.card ι) H 1 ≤ bchBoxCoordinateBound s (Fintype.card ι) H 1 + 1
    linarith
  calc
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H 1 * ‖basisHomeomorph e z‖ := by
      simpa only [dist_comm, NNReal.toReal] using hLip
    _ ≤ (C : ℝ) * ‖basisHomeomorph e z‖ := mul_le_mul_of_nonneg_right hAC (norm_nonneg _)
    _ ≤ (C : ℝ) * ((C : ℝ) * dist g h) := mul_le_mul_of_nonneg_left hz C.coe_nonneg
    _ = _ := by ring

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem rational_kernel_of_near_bounded_point
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (g γ : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B)
    (hγ : basisHomeomorph e γ ∈ realDenominatorGrid l)
    (hkernel : (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    (C : ℝ) * dist g γ < 1 →
    ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
      (A * C) * dist g γ < 1 →
    (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e γ = 0 := by
  let := rightMetricSpace (hnil := hnil) e
  dsimp only
  intro hnear hsmall
  apply rational_matrix_kernel_separation Q HQ hQ l hl (basisHomeomorph e γ) (basisHomeomorph e g)
    hγ hkernel
  have hcoord := dist_coordinates_le_of_near_box e c hstructure hc B hB g γ hg hnear
  rw [dist_comm] at hcoord
  calc
    _ ≤ ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
        (bchBoxCoordinateBound s (Fintype.card κ) H B *
          (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * dist g γ) := by
      exact mul_le_mul_of_nonneg_left hcoord (by positivity)
    _ < 1 := by nlinarith [hsmall]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lattice_translate_mem_of_small_dist
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B K : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (J : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hJ : ∀ g, g ∈ J ↔ (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0)
    (x y γ : NilpotentLieBCHGroup L s hnil) (hx : x ∈ J) (hy : y ∈ J)
    (hγ : basisHomeomorph e γ ∈ realDenominatorGrid l)
    (hxy : ∀ i, |e.repr (y⁻¹ * x).coord i| ≤ B)
    (hleft : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith K (fun z => y⁻¹ * z)) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    (C : ℝ) * K * dist x (y * γ) < 1 →
    ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
      (A * C) * K * dist x (y * γ) < 1 → γ ∈ J := by
  let := rightMetricSpace (hnil := hnil) e
  dsimp only
  intro hnear hsmall
  have hdist : dist (y⁻¹ * x) γ ≤ (K : ℝ) * dist x (y * γ) := by
    simpa only [inv_mul_cancel_left] using hleft.dist_le_mul x (y * γ)
  apply (hJ γ).mpr
  apply rational_kernel_of_near_bounded_point e c hstructure hc Q HQ B hB hQ l hl (y⁻¹ * x) γ
    hxy hγ ((hJ _).mp (J.mul_mem (J.inv_mem hy) hx))
  · calc
      _ ≤ (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * (K * dist x (y * γ)) :=
        mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg _)
      _ < 1 := by nlinarith [hnear]
  · have hA := bchBoxCoordinateBound_nonneg s (Fintype.card κ) H B.coe_nonneg
    calc
      _ ≤ ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
          (bchBoxCoordinateBound s (Fintype.card κ) H B *
            (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ)) * (K * dist x (y * γ)) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ < 1 := by nlinarith [hsmall]

theorem exists_uniform_lattice_image_gap
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B K : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (J Λ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hJ : ∀ g, g ∈ J ↔ (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0)
    (hΛ : ∀ γ ∈ Λ, basisHomeomorph e γ ∈ realDenominatorGrid l)
    (S : Set (NilpotentLieBCHGroup L s hnil)) (hS : S ⊆ J)
    (hprod : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |e.repr (y⁻¹ * x).coord i| ≤ B)
    (hleft : letI := rightMetricSpace (hnil := hnil) e;
      ∀ y ∈ S, LipschitzWith K (fun z => y⁻¹ * z)) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    ∃ ε : ℝ≥0, 0 < ε ∧
      (ε : ℝ)⁻¹ = (C : ℝ) * K +
        ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
          (A * C) * K + 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ γ ∈ Λ, dist x (y * γ) < ε → γ ∈ J := by
  let := rightMetricSpace (hnil := hnil) e
  let a : ℝ := (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * K
  let b : ℝ := ((matrixDenominator Q * l : ℕ) : ℝ) *
    (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
    (bchBoxCoordinateBound s (Fintype.card κ) H B *
      (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ)) * K
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    have := bchBoxCoordinateBound_nonneg s (Fintype.card κ) H B.coe_nonneg
    dsimp [b]
    positivity
  have hr : 0 < a + b + 1 := by linarith
  let ε : ℝ≥0 := ⟨(a + b + 1)⁻¹, (inv_pos.mpr hr).le⟩
  refine ⟨ε, show (0 : ℝ) < (a + b + 1)⁻¹ from inv_pos.mpr hr, ?_, ?_⟩
  · exact inv_inv (a + b + 1)
  · intro x hx y hy γ hγ hnear
    have hscaled : (a + b + 1) * dist x (y * γ) < 1 := by
      have h := mul_lt_mul_of_pos_left hnear hr
      change (a + b + 1) * dist x (y * γ) < (a + b + 1) * (a + b + 1)⁻¹ at h
      simpa only [mul_inv_cancel₀ hr.ne'] using h
    apply lattice_translate_mem_of_small_dist e c hstructure hc Q HQ B K hB hQ l hl
      J hJ x y γ (hS hx) (hS hy) (hΛ γ hγ) (hprod x hx y hy) (hleft y hy)
    · change a * dist x (y * γ) < 1
      nlinarith [dist_nonneg (x := x) (y := y * γ)]
    · change b * dist x (y * γ) < 1
      nlinarith [dist_nonneg (x := x) (y := y * γ)]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
