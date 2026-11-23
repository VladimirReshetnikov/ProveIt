import GlobeFlattening.SphereChart
import GlobeFlattening.RestrictedArea
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Tangent isometries and the differential in the ambient spaces
-/

namespace GlobeFlattening

open Filter Set
open scoped RealInnerProductSpace Topology

noncomputable section

/-- The usual coordinate identification of the real plane with Euclidean space.
The pair carries the product norm for the analytic construction. -/
def planarEuclideanEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

theorem planarEuclideanEquiv_apply (v : ℝ × ℝ) :
    planarEuclideanEquiv v = !₂[v.1, v.2] := rfl

/-- The ambient left inverse to the coordinate derivative. Dividing the east
component by the cosine of latitude changes from arc length to longitude. -/
def sphereChartInverseDerivative (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ × ℝ :=
  ((Real.cos p.2)⁻¹ • (EuclideanSpace.proj 0).comp (sphereFlattenDerivative p)).prod
    ((EuclideanSpace.proj 1).comp (sphereFlattenDerivative p))

theorem sphereChartInverseDerivative_apply (p : ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 3)) :
    sphereChartInverseDerivative p w =
      ((Real.cos p.2)⁻¹ * (sphereFlattenDerivative p w) 0, (sphereFlattenDerivative p w) 1) :=
  rfl

theorem sphereChartInverseDerivative_leftInverse (p : ℝ × ℝ) (hc : Real.cos p.2 ≠ 0) :
    Function.LeftInverse (sphereChartInverseDerivative p) (sphereDerivative p) := by
  intro v
  rw [sphereChartInverseDerivative_apply, sphereFlattenDerivative_sphereDerivative]
  change ((Real.cos p.2)⁻¹ * (Real.cos p.2 * v.1), v.2) = v
  simp [hc]

theorem hasFDerivWithinAt_sphereChartInverse {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    HasFDerivWithinAt sphereChartInverse (sphereChartInverseDerivative p) cutSphere
      (spherePoint p) := by
  have hw : spherePoint p ∈ cutSphere := spherePoint_mapsTo hp
  have hcos := (Real.cos_pos_of_mem_Ioo hp.2).ne'
  have hcont : Tendsto sphereChartInverse (𝓝[cutSphere] (spherePoint p))
      (𝓝[univ] (sphereChartInverse (spherePoint p))) := by
    rw [nhdsWithin_univ]
    exact continuousOn_sphereChartInverse (spherePoint p) hw
  have hf : HasFDerivWithinAt spherePoint (sphereDerivative p) univ
      (sphereChartInverse (spherePoint p)) := by
    rw [sphereChartInverse_spherePoint hp]
    exact (hasFDerivAt_spherePoint p).hasFDerivWithinAt
  have hcomp : spherePoint ∘ sphereChartInverse =ᶠ[𝓝[cutSphere] (spherePoint p)] id := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact spherePoint_sphereChartInverse hw
  simpa only [ContinuousLinearMap.comp_id] using hf.of_comp_of_leftInverse hcont
    (hasFDerivWithinAt_id _ _) hcomp (sphereChartInverseDerivative_leftInverse p hcos) hw

theorem sphereFlatten_comp_inverseDerivative (p : ℝ × ℝ) (hc : Real.cos p.2 ≠ 0) :
    planarEuclideanEquiv.toContinuousLinearMap.comp
      ((coordinateDerivative (Real.cos p.2)).comp (sphereChartInverseDerivative p)) =
      sphereFlattenDerivative p := by
  apply ContinuousLinearMap.ext
  intro w
  change planarEuclideanEquiv ((coordinateDerivative (Real.cos p.2))
    (sphereChartInverseDerivative p w)) = _
  rw [sphereChartInverseDerivative_apply, planarEuclideanEquiv_apply]
  ext i
  fin_cases i
  · change Real.cos p.2 * ((Real.cos p.2)⁻¹ * (sphereFlattenDerivative p w) 0) = _
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rfl
  · rfl

/-- The prescribed longitude derivative in rectangular coordinates gives the
ambient differential that extracts the two orthonormal tangent components. -/
theorem hasFDerivWithinAt_sphereFlatten {u : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ sphereLongitudeDomain)
    (hu : HasFDerivWithinAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      sphereLongitudeDomain p) :
    HasFDerivWithinAt (planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse))
      (sphereFlattenDerivative p) cutSphere (spherePoint p) := by
  have h := hasFDerivWithinAt_flattenCoordinates hu
  rw [← sphereChartInverse_spherePoint hp] at h
  have hrect := h.comp (spherePoint p) (hasFDerivWithinAt_sphereChartInverse hp)
    sphereChartInverse_mapsTo
  rw [sphereChartInverse_spherePoint hp] at hrect
  have hc := (Real.cos_pos_of_mem_Ioo hp.2).ne'
  rw [← sphereFlatten_comp_inverseDerivative p hc]
  exact planarEuclideanEquiv.hasFDerivAt.comp_hasFDerivWithinAt (spherePoint p) hrect

private def sphereFrameBasis (p : ℝ × ℝ) : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  let h := orthonormal_sphereFrame p
  let b := basisOfOrthonormalOfCardEqFinrank h (by simp [finrank_euclideanSpace])
  b.toOrthonormalBasis (by simpa [b] using h)

private theorem sphereFrameBasis_apply (p : ℝ × ℝ) (i : Fin 3) :
    sphereFrameBasis p i = sphereFrame p i := by
  simp [sphereFrameBasis]

/-- Zero radial component is exactly what is needed to recover the original
vector from its two tangent coordinates. -/
theorem sphereTangentLift_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ)
    {w : EuclideanSpace ℝ (Fin 3)} (h : ⟪spherePoint p, w⟫ = 0) :
    sphereTangentLift p (sphereFlattenDerivative p w) = w := by
  have hexpand := (sphereFrameBasis p).sum_repr' w
  simp only [Fin.sum_univ_three, sphereFrameBasis_apply, sphereFrame, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at hexpand
  rw [sphereTangentLift_apply, sphereFlattenDerivative_apply]
  change ⟪sphereEast p, w⟫ • sphereEast p + ⟪sphereNorth p, w⟫ • sphereNorth p = w
  simpa [h] using hexpand

theorem norm_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ) {w : EuclideanSpace ℝ (Fin 3)}
    (hw : ⟪spherePoint p, w⟫ = 0) : ‖sphereFlattenDerivative p w‖ = ‖w‖ := by
  rw [← norm_sphereTangentLift p (sphereFlattenDerivative p w),
    sphereTangentLift_sphereFlattenDerivative_of_tangent p hw]

/-- The metric in spherical coordinates has diagonal entries
`cos latitude` squared and `1`. -/
theorem sq_norm_sphereDerivative (p v : ℝ × ℝ) :
    ‖sphereDerivative p v‖ ^ 2 = (Real.cos p.2 * v.1)^2 + v.2^2 := by
  change ‖sphereTangentLift p !₂[Real.cos p.2 * v.1, v.2]‖ ^ 2 = _
  rw [norm_sphereTangentLift, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

/-- A nonzero longitude scale makes the triangular derivative invertible. -/
def coordinateDerivativeEquiv (slope : ℝ) (hs : slope ≠ 0) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 slope hs)).prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)

theorem coordinateDerivativeEquiv_toContinuousLinearMap (slope : ℝ) (hs : slope ≠ 0) :
    (coordinateDerivativeEquiv slope hs).toContinuousLinearMap = coordinateDerivative slope := rfl

theorem coordinateDerivativeEquiv_symm_toContinuousLinearMap (slope : ℝ) (hs : slope ≠ 0) :
    (coordinateDerivativeEquiv slope hs).symm.toContinuousLinearMap =
      coordinateDerivative slope⁻¹ := rfl

/-- The differential of the inverse planar chart followed by the spherical
parametrization is the lift into the tangent plane. -/
theorem hasFDerivAt_sphereFlatten_inverse
    (g : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) {p : ℝ × ℝ}
    (hp : p ∈ g.source) (hc : Real.cos p.2 ≠ 0)
    (hg : HasFDerivAt g (coordinateDerivative (Real.cos p.2)) p) :
    HasFDerivAt (spherePoint ∘ (g.symm ∘ planarEuclideanEquiv.symm)) (sphereTangentLift p)
      (planarEuclideanEquiv (g p)) := by
  have hinv : HasFDerivAt g.symm (coordinateDerivative (Real.cos p.2)⁻¹) (g p) := by
    rw [← coordinateDerivativeEquiv_symm_toContinuousLinearMap _ hc]
    apply g.hasFDerivAt_symm (g.map_source hp)
    rw [g.left_inv hp, coordinateDerivativeEquiv_toContinuousLinearMap]
    exact hg
  have hg' := hinv.comp (planarEuclideanEquiv (g p))
    planarEuclideanEquiv.symm.hasFDerivAt
  have hs' : HasFDerivAt spherePoint (sphereDerivative p)
      ((g.symm ∘ planarEuclideanEquiv.symm) (planarEuclideanEquiv (g p))) := by
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, g.left_inv hp]
      using hasFDerivAt_spherePoint p
  have hD : (sphereDerivative p).comp
      ((coordinateDerivative (Real.cos p.2)⁻¹).comp planarEuclideanEquiv.symm.toContinuousLinearMap) =
      sphereTangentLift p := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, sphereDerivative_apply, sphereTangentLift_apply]
    change (Real.cos p.2 * ((Real.cos p.2)⁻¹ * v 0)) • sphereEast p +
      v 1 • sphereNorth p = _
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [← hD]
  exact hs'.comp (planarEuclideanEquiv (g p)) hg'

end

end GlobeFlattening
