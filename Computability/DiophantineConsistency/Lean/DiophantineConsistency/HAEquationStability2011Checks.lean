import DiophantineConsistency.HAEquationStability2011

set_option Elab.async false
namespace DiophantineConsistency.HAEquationStability2011Checks
open SetTheory.PA
open HAEquationStability2011

example : HA.Derives [] (.imp
    (HA.doubleNeg ArithmeticCurrentEquation2011.unsolvabilitySentence)
    ArithmeticCurrentEquation2011.unsolvabilitySentence) := derives_stability

example : HA.Relative (fun _ => False) [] (.imp
    (HA.doubleNeg ArithmeticCurrentEquation2011.unsolvabilitySentence)
    ArithmeticCurrentEquation2011.unsolvabilitySentence) :=
  HA.relative_of_derives derives_stability

example : Formula.Sentence ArithmeticCurrentEquation2011.unsolvabilitySentence :=
  ArithmeticCurrentEquation2011.sentence_unsolvabilitySentence

#print axioms negative_unsolvabilitySentence
#print axioms derives_stability
#print axioms proves_stability
#print axioms of_proves_doubleNeg

end DiophantineConsistency.HAEquationStability2011Checks
