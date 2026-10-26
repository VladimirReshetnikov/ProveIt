import DiophantineConsistency.ControllerResidueLift

namespace DiophantineConsistency.ControllerResidueLiftChecks

open ControllerResidueLift
open scoped BigOperators

set_option Elab.async false

-- This is an actual quotient lift: 13=3+5*2 modulo15.
example : ∃ u : ZMod 3,
    (13 : ZMod (5*3)) = 3+5*(u.val : ZMod (5*3)) :=
  exists_coordinate 13 3 (by decide) (by decide)
example : (13 : ℕ)%5 = 3 ∧ (13 : ℕ)/5 = 2 := by decide

-- The zero residue and the T=1 endpoint also lift.
example : ∃ u : ZMod 3, (10 : ZMod (5*3)) = 0+5*(u.val : ZMod (5*3)) :=
  exists_coordinate 10 0 (by decide) (by decide)
example : ∃ u : ZMod 1, (3 : ZMod (5*1)) = 3+5*(u.val : ZMod (5*1)) :=
  exists_coordinate 3 3 (by decide) (by decide)

-- A composite C0 is allowed. Every target mod54 is reached by an actual
-- distinct subset and an optional unit, with size strictly between0 and6.
example (t : ZMod (6*9)) :
    ∃ e a : ℕ, ∃ s : Finset (ZMod 9),
      e ≤ 1 ∧ 0 < a ∧ a < 6 ∧ s.card = a ∧
      (∑ x ∈ s, (1+6*(x.val : ZMod (6*9))))+(e : ZMod (6*9))*1 = t := by
  exact exists_subset_boolean_sum (by norm_num : Nat.Prime 3) (by decide)
    2 (by decide : 9 = 3^2) (by decide : 6 < 9) id Function.injective_id
    (fun x => 1+6*(x.val : ZMod (6*9))) (fun _ => rfl) t 1 (by decide)

#print axioms exists_coordinate
#print axioms exists_subset_boolean_sum

end DiophantineConsistency.ControllerResidueLiftChecks
