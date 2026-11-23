import GlobeFlattening.SphereChart
import GlobeFlattening.RestrictedArea
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

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

/-- The coordinate identification after changing longitude to eastward arc length. -/
private def scaledPlanarEquiv (p : ℝ × ℝ) (hc : Real.cos p.2 ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 (Real.cos p.2) hc)).prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).trans planarEuclideanEquiv

/-- The metric in spherical coordinates has diagonal entries
`cos latitude` squared and `1`. -/
theorem sq_norm_sphereDerivative (p v : ℝ × ℝ) :
    ‖sphereDerivative p v‖ ^ 2 = (Real.cos p.2 * v.1)^2 + v.2^2 := by
  change ‖sphereTangentLift p !₂[Real.cos p.2 * v.1, v.2]‖ ^ 2 = _
  rw [norm_sphereTangentLift, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

/-- The differential of the inverse planar chart followed by the spherical
parametrization is the lift into the tangent plane. -/
theorem hasFDerivAt_sphereFlatten_inverse
    (g : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) {p : ℝ × ℝ}
    (hp : p ∈ g.source) (hc : Real.cos p.2 ≠ 0)
    (hg : HasFDerivAt g (coordinateDerivative (Real.cos p.2)) p) :
    HasFDerivAt (spherePoint ∘ (g.symm ∘ planarEuclideanEquiv.symm)) (sphereTangentLift p)
      (planarEuclideanEquiv (g p)) := by
  let D := scaledPlanarEquiv p hc
  let G := g.transHomeomorph planarEuclideanEquiv.toHomeomorph
  have hG : HasFDerivAt G D.toContinuousLinearMap p :=
    planarEuclideanEquiv.hasFDerivAt.comp p hg
  have hGinv := G.hasFDerivAt_symm (f' := D) (G.map_source hp) (by rwa [G.left_inv hp])
  have hs' : HasFDerivAt spherePoint (sphereDerivative p) (G.symm (G p)) := by
    rw [G.left_inv hp]
    exact hasFDerivAt_spherePoint p
  apply (hs'.comp (G p) hGinv).congr_fderiv
  ext v : 1
  change sphereTangentLift p (D (D.symm v)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The forward differential is the linear left inverse of the tangent lift. -/
theorem hasFDerivWithinAt_sphereFlatten
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)}
    {fInv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {p : ℝ × ℝ}
    (hcont : ContinuousOn f cutSphere) (hleft : LeftInvOn fInv f cutSphere)
    (hp : spherePoint p ∈ cutSphere)
    (hinv : HasFDerivAt fInv (sphereTangentLift p) (f (spherePoint p))) :
    HasFDerivWithinAt f (sphereFlattenDerivative p) cutSphere (spherePoint p) := by
  simpa only [ContinuousLinearMap.comp_id] using
    (hinv.hasFDerivWithinAt (s := univ)).of_comp_of_leftInverse
      (by rw [nhdsWithin_univ]; exact hcont (spherePoint p) hp)
      (hasFDerivWithinAt_id _ _) hleft.eqOn.eventuallyEq_nhdsWithin
      (sphereFlattenDerivative_leftInverse p) hp

end

end GlobeFlattening
