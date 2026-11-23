import GlobeFlattening.SphereFrame
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Tangent isometries and the differential in the ambient spaces
-/

namespace GlobeFlattening

open Filter Set
open scoped RealInnerProductSpace Topology

noncomputable section

/-- The differential of the inverse planar chart followed by the spherical
parametrization is the lift into the tangent plane. -/
theorem hasFDerivAt_sphereFlatten_inverse
    (g : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) {p : ℝ × ℝ}
    (hp : p ∈ g.source) (hc : Real.cos p.2 ≠ 0)
    (hg : HasFDerivAt g (coordinateDerivative (Real.cos p.2)) p) :
    HasFDerivAt (spherePoint ∘ (g.symm ∘ planarEuclideanEquiv.symm)) (sphereTangentLift p)
      (planarEuclideanEquiv (g p)) := by
  rw [← Function.comp_assoc, planarEuclideanEquiv.symm.comp_right_hasFDerivAt_iff',
    planarEuclideanEquiv.symm_apply_apply]
  let D := (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
    (Units.mk0 (Real.cos p.2) hc)).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hginv := g.hasFDerivAt_symm (f' := D) (g.map_source hp) ((g.left_inv hp).symm ▸ hg)
  have hs' : HasFDerivAt spherePoint (sphereDerivative p) (g.symm (g p)) :=
    (g.left_inv hp).symm ▸ hasFDerivAt_spherePoint p
  exact (hs'.comp (g p) hginv).congr_fderiv <|
    ContinuousLinearMap.ext fun v => congrArg (sphereTangentLift p ∘ planarEuclideanEquiv)
      (D.apply_symm_apply v)

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
