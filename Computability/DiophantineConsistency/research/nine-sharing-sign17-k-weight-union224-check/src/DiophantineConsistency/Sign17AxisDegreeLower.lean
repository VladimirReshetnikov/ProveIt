import DiophantineConsistency.Sign17AxisDiagonalBinding

/-! SOURCE-ONLY: transfer the corrected-axis seed degree to total degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisDegreeLower
open Sign17UnivariateDegree Sign17AxisSeedDegree Sign17AxisDiagonal

theorem expression_polynomial_degree_ge (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    96 ≤ (Sign17AbstractExpression.expression p).toPolynomial.totalDegree := by
  have hd := mapped_degree_le (diagonal (Sign17AbstractExpression.expression p).toPolynomial)
  rw [direct_axis, seed_axis_degree p hz] at hd
  exact hd.trans (diagonal_totalDegree_le _)

end DiophantineConsistency.Sign17AxisDegreeLower
#print axioms DiophantineConsistency.Sign17AxisDegreeLower.expression_polynomial_degree_ge
