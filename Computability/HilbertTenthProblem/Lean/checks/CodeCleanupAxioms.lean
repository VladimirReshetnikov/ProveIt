import Diophantine.MRDP
import Diophantine.Common.DiophantineFunctionPolynomial
import Diophantine.Common.PellInt
import Diophantine.Common.RelationCombiningArithmetic
import Diophantine.Paper1974.More
import Diophantine.Paper1976.ExactDegreePrimePolynomial
import Diophantine.Paper1978.Godel
import Diophantine.Paper1984.Identities

/-! Transitive axiom checks for the first code-simplification batch after MRDP.
Audit shared helpers and their public clients, including the MRDP equivalence.
Run with `lake env lean Computability/HilbertTenthProblem/Lean/checks/CodeCleanupAxioms.lean` after `lake build`. -/

#print axioms Diophantine.eq_zero_of_mul_one_sub_sq_pos
#print axioms Diophantine.mul_one_sub_sq_pos_iff
#print axioms Diophantine.rePred_dioph
#print axioms Diophantine.mrdp_iff
#print axioms Diophantine.exists_polynomial_of_dioph_graph
#print axioms Diophantine.RelationCombiningArithmetic.sum_rational_of_factor
#print axioms Diophantine.RelationCombiningArithmetic.conditions_of_factor
#print axioms Diophantine.RelationCombiningArithmetic.exists_factor_of_conditions
#print axioms Diophantine.RelationCombiningArithmetic.factor_iff
#print axioms Diophantine.two_step
#print axioms Diophantine.xn_add_two_add_sub_two
#print axioms Jones1974.run_eq_of_halted
#print axioms Jones1974.score_unique
#print axioms Jones1974.computes_seq
#print axioms Jones1974.prints_seq
#print axioms Jones1974.haltsWithScore_seq_addOne
#print axioms Jones1974.sigma_le_SH
#print axioms Jones1974.sigma_le_SC
#print axioms Jones1974.theorem_1
#print axioms Jones1978.exists_S_eq
#print axioms JM1984.Mask.le
#print axioms JSWW1976.TwelveVariable.prime_iff_positive_value
#print axioms JSWW1976.RefinedTwelveVariable.prime_iff_positive_value
#print axioms JSWW1976.FiveSquarePrimePolynomial.prime_iff_positive_value
#print axioms JSWW1976.ExactDegreePrimePolynomial.prime_iff_positive_value
