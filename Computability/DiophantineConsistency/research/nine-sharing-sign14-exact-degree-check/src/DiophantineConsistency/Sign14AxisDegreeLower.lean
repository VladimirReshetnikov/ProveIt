import DiophantineConsistency.Sign14AxisDiagonalBinding

/-! SOURCE-ONLY: transfer the corrected-axis seed degree to total degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisDegreeLower
open Sign17UnivariateDegree Sign14AxisSeedDegree Sign14AxisDiagonal

theorem expression_polynomial_degree_ge (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    124 ≤ (Sign14AbstractExpression.expression p).toPolynomial.totalDegree := by
  have hd := mapped_degree_le (diagonal (Sign14AbstractExpression.expression p).toPolynomial)
  rw [direct_axis, seed_axis_degree p hz] at hd
  exact hd.trans (diagonal_totalDegree_le _)

end DiophantineConsistency.Sign14AxisDegreeLower
#print axioms DiophantineConsistency.Sign14AxisDegreeLower.expression_polynomial_degree_ge
