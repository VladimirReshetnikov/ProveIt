import DiophantineConsistency.PRAInductionRule

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAInductionRule

example (φ : Semiproposition language 1) (hφ : φ.Open)
    (hb : PRA ⊢ (base φ).univCl) (hs : PRA ⊢ (step φ).univCl) :
    PRA ⊢ (∀⁰ φ).univCl := open_induction_rule φ hφ hb hs
#print axioms DiophantineConsistency.PRAInductionRule.open_induction_rule
#check DiophantineConsistency.PRAInductionRule.open_induction_rule
