import GlobeFlattening.SphereFrame
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Tangent isometries and the differential in the ambient spaces
-/

namespace GlobeFlattening

open Set

/-- The differential of the inverse planar chart followed by the spherical
parametrization is the lift into the tangent plane. -/
theorem hasFDerivAt_sphereFlatten_inverse
    (g : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) {p : ℝ × ℝ}
    (hp : p ∈ g.source) (hc : Real.cos p.2 ≠ 0)
    (hg : HasFDerivAt g (coordinateDerivative (Real.cos p.2)) p) :
    HasFDerivAt (spherePoint ∘ (g.symm ∘ planarEuclideanEquiv.symm)) (sphereTangentLift p)
      (planarEuclideanEquiv (g p)) := by
  let h := g.trans planarEuclideanEquiv.toHomeomorph.toOpenPartialHomeomorph
  have hp' : p ∈ h.source := ⟨hp, mem_univ _⟩
  let D := ((ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.cos p.2) hc)).prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).trans planarEuclideanEquiv
  have hinv := h.hasFDerivAt_symm (f' := D) (h.map_source hp') <|
    (h.left_inv hp').symm ▸ planarEuclideanEquiv.hasFDerivAt.comp p hg
  refine (HasFDerivAt.comp (h p) (g' := sphereDerivative p) ?_ hinv).congr_fderiv ?_
  · exact (h.left_inv hp').symm ▸ hasFDerivAt_spherePoint p
  · exact ContinuousLinearMap.ext fun v => congrArg (sphereTangentLift p) (D.apply_symm_apply v)

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
      ((hcont _ hp).tendsto_nhdsWithin (mapsTo_univ _ _))
      (hasFDerivWithinAt_id _ _) hleft.eqOn.eventuallyEq_nhdsWithin
      (sphereFlattenDerivative_leftInverse p) hp

end GlobeFlattening
