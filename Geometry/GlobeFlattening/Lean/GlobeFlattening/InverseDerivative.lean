import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Differentiating the inverse on the good set
-/

namespace GlobeFlattening

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The report's inverse derivative lemma at a point of the source. A
homeomorphism of open sets has the inverse derivative as soon as its
derivative at that point is a continuous linear equivalence. -/
theorem hasFDerivAt_inverse_image (f : OpenPartialHomeomorph E F) {p : E}
    {A : E ≃L[ℝ] F} (hp : p ∈ f.source)
    (hA : HasFDerivAt f (A : E →L[ℝ] F) p) :
    HasFDerivAt f.symm (A.symm : F →L[ℝ] E) (f p) := by
  apply f.hasFDerivAt_symm (f.map_source hp)
  rwa [f.left_inv hp]

end GlobeFlattening
