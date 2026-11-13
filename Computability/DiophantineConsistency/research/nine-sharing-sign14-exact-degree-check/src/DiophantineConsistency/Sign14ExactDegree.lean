import DiophantineConsistency.Sign14AxisDegreeLower

/-! SOURCE-ONLY: exact degree from upper and conditional lower bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14ExactDegree

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.radix CurrentMasks2011.lowPort CurrentMasks2011.highPort

set_option maxHeartbeats 4000000 in
theorem current_port_positive : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
  have hr : 1 < CurrentMasks2011.radix ^ 2011 :=
    one_lt_pow₀ (by unfold CurrentMasks2011.radix; decide : 1 < CurrentMasks2011.radix) (by decide)
  have hb : 0 < CurrentMasks2011.beta := by unfold CurrentMasks2011.beta; omega
  change (0 : ℤ) < (CurrentMasks2011.beta : ℤ)
  exact_mod_cast hb

theorem current_port_nonzero : CurrentWindowCarry2011.ports 0 ≠ 0 :=
  ne_of_gt current_port_positive

theorem abstract_exact (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    (Sign14AbstractExpression.expression p).toPolynomial.totalDegree = 124 :=
  Nat.le_antisymm (Sign14SyntaxDegree.expression_polynomial_degree_le p)
    (Sign14AxisDegreeLower.expression_polynomial_degree_ge p hz)

theorem current_exact : Sign14CurrentExpression.expression.toPolynomial.totalDegree = 124 :=
  abstract_exact CurrentWindowCarry2011.ports current_port_nonzero

end DiophantineConsistency.Sign14ExactDegree
#print axioms DiophantineConsistency.Sign14ExactDegree.current_port_positive
#print axioms DiophantineConsistency.Sign14ExactDegree.current_port_nonzero
#print axioms DiophantineConsistency.Sign14ExactDegree.abstract_exact
#print axioms DiophantineConsistency.Sign14ExactDegree.current_exact
