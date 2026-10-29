import DiophantineConsistency.PRAParsonsOpenRule

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAParsonsOpenRule

example (φ : Semiproposition language 1) (hφ : φ.Open)
    (hb : PRA ⊢ (DiophantineConsistency.ParsonsRule.base φ).univCl)
    (hs : PRA ⊢ (DiophantineConsistency.ParsonsRule.step φ).univCl) :
    PRA ⊢ (∀⁰ φ).univCl := parsons_open_induction_rule φ hφ hb hs
#print axioms DiophantineConsistency.PRAParsonsOpenRule.parsons_open_induction_rule
#check DiophantineConsistency.PRAParsonsOpenRule.parsons_open_induction_rule
