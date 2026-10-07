import OAI.Combinatorics.Progressions.Estimates.NormalizedMeshLengths
import OAI.Combinatorics.Progressions.Estimates.SecondaryMeshGeometry

namespace OAI

section

namespace Erdos3

theorem secondaryMesh_geometry_inverse {boundary movement sourceRatio parameterRatio beta U : ℝ}
    (hb : 0 ≤ boundary) (hm : 0 ≤ movement) (hs : 0 ≤ sourceRatio) (hp : 0 ≤ parameterRatio)
    (hbeta : 0 < beta) (hU : 0 ≤ U)
    (hbU : boundary ≤ Real.exp U) (hmU : movement ≤ Real.exp U)
    (hsU : sourceRatio ≤ Real.exp U) (hpU : parameterRatio ≤ Real.exp U)
    (hbetaU : beta⁻¹ ≤ Real.exp U) :
    (secondaryBoundaryMargin boundary beta)⁻¹ ≤ Real.exp (2 * U + 8) ∧
    (secondaryMeshDelta boundary (secondaryMovementBudget movement sourceRatio parameterRatio) beta)⁻¹ ≤
      Real.exp (4 * U + 18) := by
  have he : Real.exp U ≤ Real.exp (U + 3) := Real.exp_le_exp.mpr (by linarith)
  have hM : 0 ≤ secondaryMovementBudget movement sourceRatio parameterRatio := by
    unfold secondaryMovementBudget; positivity
  have h := secondaryMeshAllocation_inverse_bounds hb hM hbeta (by linarith : 0 ≤ U + 3)
    (hbU.trans he) (secondaryMovementBudget_le_exp hmU hsU hpU) (hbetaU.trans he)
  simpa only [show 2 * (U + 3) + 2 = 2 * U + 8 by ring,
    show 4 * (U + 3) + 6 = 4 * U + 18 by ring] using h

theorem secondaryMesh_rounding_of_scale {boundary beta U lengthLog H : ℝ}
    (hmargin : 0 < secondaryBoundaryMargin boundary beta)
    (hinv : (secondaryBoundaryMargin boundary beta)⁻¹ ≤ Real.exp (2 * U + 8))
    (hU : 0 ≤ U) (hlen : 0 ≤ lengthLog)
    (hH : 4 * Real.exp (4 * U + 18 + lengthLog) ≤ H) :
    1 ≤ secondaryBoundaryMargin boundary beta * H := by
  have hexp : Real.exp (2 * U + 8) ≤ Real.exp (4 * U + 18 + lengthLog) :=
    Real.exp_le_exp.mpr (by linarith)
  have hle : (secondaryBoundaryMargin boundary beta)⁻¹ ≤ H := by
    have hpos := Real.exp_pos (4 * U + 18 + lengthLog)
    linarith [hinv.trans hexp]
  have h := mul_le_mul_of_nonneg_left hle hmargin.le
  simpa only [mul_inv_cancel₀ hmargin.ne'] using h

end Erdos3

end

end OAI
