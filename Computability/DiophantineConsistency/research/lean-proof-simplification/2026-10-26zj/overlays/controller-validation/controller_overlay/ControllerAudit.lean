import DiophantineConsistency.ControllerResidueLift
open DiophantineConsistency ControllerIntervalSums ControllerAuxiliaryChoice ControllerResidueLift
example : (interval (0 : ZMod 1) 0).card = 0 := interval_card _ _ (by decide)
example : (interval (0 : ZMod 1) 1).card = 1 := interval_card _ _ (by decide)
example : ∃ u : ZMod 1, (0 : ZMod (1*1)) = 0+1*(u.val : ZMod (1*1)) :=
  exists_coordinate 0 0 (by decide) (by decide)
example : ∃ u : ZMod 6, (17 : ZMod (6*6)) = 5+6*(u.val : ZMod (6*6)) :=
  exists_coordinate 17 5 (by decide) (by decide)
example : ∃ e a : ℕ, e ≤ 1 ∧ 0 < a ∧ a < 6 ∧
    (a : ZMod 6) = 0-(e : ZMod 6)*1 ∧ Nat.Coprime a (2^0) :=
  exists_coprime_cardinality (by decide : Nat.Prime 2) (by decide) 0 1 (by decide) 0
#print axioms interval_injOn
#print axioms interval_card
#print axioms exists_coprime_cardinality
#print axioms exists_coordinate
#print axioms exists_subset_boolean_sum
