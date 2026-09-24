import Diophantine.Common.RefinedRelationCombiningPolynomial
import Diophantine.Paper1982.EnumerationQuartic
import Diophantine.Paper1982.ShortQuartic
import Diophantine.Paper1980.PellRelaxed
import Diophantine.Paper1980.CodeDigits
import Diophantine.Paper1980.Pack93
import Diophantine.Paper1980.Pell93
import Diophantine.Paper1980.Window93
import Diophantine.Paper1980.MaskDigits

/-! Transitive axiom checks for the polynomial-helper cleanup and the two
repaired incoming Pell proofs. Run after the consolidated `lake build`.
The helper statements allow arbitrary variable types and commutative semirings
(commutative rings for sign flips); the clients retain their existing bounds. -/

#print axioms Diophantine.exists_eval_rename_option_iff
#print axioms Diophantine.eval_rename_zeroWitnesses
#print axioms Diophantine.totalDegree_sum_pow_le
#print axioms Diophantine.RelationCombiningPolynomial.signFlip_signed_X
#print axioms Diophantine.RelationCombiningPolynomial.signFlip_rawFactor
#print axioms Diophantine.RefinedRelationCombiningPolynomial.signFlip_rawFactor
#print axioms Jones1982.EnumerationQuartic.sumSquares_totalDegree_le_four
#print axioms Jones1982.EnumerationQuartic.wset_quartic_iff
#print axioms Jones1982.EnumerationQuartic.quartic_normalized
#print axioms Jones1982.ShortQuadratic.sumSquares_totalDegree_le_four
#print axioms Jones1982.ShortQuadratic.shiftedSumSquares_totalDegree_le_four
#print axioms Jones1982.ShortQuadratic.wset_quartic58_iff
#print axioms Jones1982.ShortQuadratic.quartic58_normalized
#print axioms Jones1980.pow_x_y
#print axioms Jones1980.xn_yn_modEq_pow
#print axioms Jones1980.S2_eq_ofDigits
#print axioms Jones1980.masks_iff_central
#print axioms Jones1980.pell_block
#print axioms Jones1980.window_digits
#print axioms Jones1980.window_nonneg_of_small
#print axioms Jones1980.τ_eq_zero_iff_digits
