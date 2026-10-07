import OAI.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped Classical

variable {X : Type*} {m dim : ℕ} {J O : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem physicalCubeRowSample_cover (v : X → (Unit ⊕ Fin dim) → ℤ) :
    d • physicalCubeRowSample U d rows p hm v = physicalCubeRowSample U 1 rows p hm v := by
  unfold physicalCubeRowSample
  rw [← map_nsmul, ← map_nsmul, physicalCubeCoveredSample_cover]

theorem coveredJetAmbientTorus_rowSample (v : X → (Unit ⊕ Fin dim) → ℤ) :
    coveredJetAmbientTorus U d (physicalCubeRowSample U d rows p hm v) =
      coveredJetAmbientTorus U 1 (physicalCubeRowSample U 1 rows p hm v) := by
  rw [coveredJetAmbientTorus_nsmul, physicalCubeRowSample_cover]

end Erdos3.BooleanCubeKernel

end

end OAI
