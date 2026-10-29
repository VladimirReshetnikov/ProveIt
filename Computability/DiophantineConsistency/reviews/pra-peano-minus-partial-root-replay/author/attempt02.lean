import DiophantineConsistency.PRAPeanoMinusPartial

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAPeanoMinusPartial

example : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addComm := PRA_proves_addComm
example : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addEqOfLt := PRA_proves_addEqOfLt
example : PeanoMinus PeanoMinus.Axiom.addComm := PeanoMinus.addComm
example : PeanoMinus PeanoMinus.Axiom.addEqOfLt := PeanoMinus.addEqOfLt
#print axioms DiophantineConsistency.PRAPeanoMinusPartial.PRA_proves_addComm
#print axioms DiophantineConsistency.PRAPeanoMinusPartial.PRA_proves_addEqOfLt
#print axioms DiophantineConsistency.PRAPeanoMinusPartial.PRA_proves_addZero
#print axioms DiophantineConsistency.PRAPeanoMinusPartial.PRA_proves_mulZero
