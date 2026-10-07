import OAI.Combinatorics.Progressions.Geometry.SpatialSiteShift

namespace OAI

section

namespace Erdos3

theorem spatialSiteApprox_eq_residue {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (C : Matrix (Unit ⊕ I) N ℤ) (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ) :
    spatialSiteApprox A (Matrix.fromCols B C) m f H b r =
      spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (integerResidueMatrix C m))) m f H b r := by
  funext v
  unfold spatialSiteApprox
  rw [pivotFullImage_eq_of_kernel_residues A B C _ m hp (by rw [liftResidueMatrix_residue])]

end Erdos3

end

end OAI
