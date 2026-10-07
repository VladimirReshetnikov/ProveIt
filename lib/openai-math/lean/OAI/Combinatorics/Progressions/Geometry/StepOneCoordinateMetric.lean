import OAI.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module Manifold NilpotentLieBCHGroup
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  (F : NilpotentLieFiltration L 1) (e : Basis ι ℝ L)

omit [IsScalarTower ℚ ℝ L] in
theorem stepOne_rightTranslate (g : F.Group) (x : ι → ℝ) :
    rightTranslate e g x = x + e.equivFun g.coord := by
  simp only [rightTranslate, basisHomeomorph_apply, F.stepOne_coord_mul, map_add]
  rw [← basisHomeomorph_apply, Homeomorph.apply_symm_apply]

omit [IsScalarTower ℚ ℝ L] in
theorem stepOne_rightVelocity (g : F.Group) :
    rightVelocity e g = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  unfold rightVelocity
  have heq : rightTranslate e g⁻¹ = fun x => x + e.equivFun (g⁻¹).coord :=
    funext (F.stepOne_rightTranslate e g⁻¹)
  rw [heq]
  simp

theorem stepOne_norm_mfderiv_coordinates_le (g : F.Group) :
    letI := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
    letI := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v)‖ ≤ ‖v‖ := by
  let := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
  intro v
  calc
    _ = ‖tangentModelVector v‖ := congrArg (fun w => ‖tangentModelVector w‖)
      (mfderiv_basisHomeomorph_coordinates e g v)
    _ ≤ coordinateL2Norm v := norm_le_coordinateL2Norm _
    _ = ‖v‖ := by
      rw [norm_tangent_eq_coordinateL2Norm, F.stepOne_rightVelocity]
      rfl

theorem stepOne_coordinates_lipschitz :
    letI := rightMetricSpace (hnil := F.lowerCentralSeries_eq_bot) e
    LipschitzWith 1 (basisHomeomorph (hnil := F.lowerCentralSeries_eq_bot) e) := by
  let := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace (hnil := F.lowerCentralSeries_eq_bot) e
  intro x y
  let r : ℝ≥0 := ⟨dist x y + 1, by positivity⟩
  have hnear : (1 : ℝ≥0∞) * riemannianEDist 𝓘(ℝ, ι → ℝ) x y < r := by
    change (1 : ℝ≥0∞) * edist x y < r
    rw [one_mul, edist_dist]
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (dist x y) < ENNReal.ofReal (dist x y + 1)
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hbound : ∀ z : F.Group, basisHomeomorph e z ∈ Metric.closedBall (basisHomeomorph e x) r →
      ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) z,
        ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) z v)‖ₑ ≤
          (1 : ℝ≥0∞) * ‖v‖ₑ := by
    intro z _ v
    simpa only [one_mul, ofReal_norm] using
      ENNReal.ofReal_le_ofReal (F.stepOne_norm_mfderiv_coordinates_le e z v)
  exact coordinate_edist_le_of_riemannianEDist_lt (C := 1) (r := r) (by norm_num)
    (contMDiff_basisHomeomorph e 1) x y hbound hnear

end Erdos3.NilpotentLieFiltration

end

end OAI
