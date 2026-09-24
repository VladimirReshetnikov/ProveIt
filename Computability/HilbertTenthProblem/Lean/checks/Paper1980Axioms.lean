import Diophantine.Paper1980.IndexCode
import Diophantine.Paper1980.Theorem5
import Diophantine.Paper1980.SingleParameter
import Diophantine.Paper1982.RecursivelyEnumerableSystems
import Diophantine.Paper1982.UniversalQuartic

/-!
Audit of the currently proved 1980 endpoints, including their reused 1982
proofs. This checks dependencies of these declarations; it does not claim
coverage of the other universal pairs or the arithmetic-operation bound.
-/

#print axioms Jones1980.indexCode_injective
#print axioms Jones1982.theorem_1
#print axioms Jones1982.theorem_2
#print axioms Jones1982.theorem_3
#print axioms Jones1982.rePred_printed_systems
#print axioms Jones1982.rePred_theorem1_system
#print axioms Jones1982.rePred_theorem2_system
#print axioms Jones1982.rePred_theorem3_system
#print axioms Jones1982.UniversalQuartic.specialize_jointPolynomial
#print axioms Jones1982.universal_quartic58
#print axioms Jones1980.theorem_5
#print axioms Jones1980.indexCode_pos
#print axioms Jones1980.singleParameterSolvable_indexCode_iff
#print axioms Jones1980.SingleParameterSolvable.code_pos
#print axioms Jones1980.rePred_single_parameter_systems
