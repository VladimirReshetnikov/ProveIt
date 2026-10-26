import DiophantineConsistency.CurrentAuxiliaryOrder2011

namespace DiophantineConsistency.CurrentAuxiliaryOrder2011Checks

open CurrentControllerData2011 CurrentAuxiliaryOrder2011
set_option Elab.async false
attribute [local irreducible] CurrentControllerData2011.B

example : 1 < B^(auxiliary-1) := generator_gt_one
example : auxiliary ∣ B^(auxiliary-1)-1 := generator_dvd
example : ¬ auxiliary^2 ∣ B^(auxiliary-1)-1 := generator_not_square
example : ¬ auxiliary ∣ B^(auxiliary-1) := generator_not_dvd

-- The actual generator modulo the auxiliary prime is already1.
example : orderOf ((B : ZMod (auxiliary^1))^(auxiliary-1)) = 1 := by
  simpa using generator_order 1 (by decide)

-- Each successive modulus increases the order by the auxiliary prime.
example : orderOf ((B : ZMod (auxiliary^2))^(auxiliary-1)) = auxiliary := by
  simpa using generator_order 2 (by decide)
example : orderOf ((B : ZMod (auxiliary^3))^(auxiliary-1)) = auxiliary^2 := by
  simpa using generator_order 3 (by decide)
example (k : ℕ) :
    auxiliary^(k+1) ∣ (B^(auxiliary-1))^(auxiliary^k)-1 ∧
      ¬ auxiliary^(k+2) ∣ (B^(auxiliary-1))^(auxiliary^k)-1 :=
  generator_exact_lift k

-- The actual first lift has a strictly interior nonzero digit.
example : 7300767062 = 1+auxiliary*60739 ∧ 0 < (60739 : ℕ) ∧ 60739 < auxiliary :=
  lift_nonzero_digit
example : (1+auxiliary*0) % auxiliary^2 = 1 := by decide
example : (7300767062 : ℕ) ≠ 1 := by decide

#print axioms generator_gt_one
#print axioms generator_mod_prime
#print axioms generator_dvd
#print axioms generator_not_square
#print axioms generator_not_dvd
#print axioms generator_exact_lift
#print axioms generator_order_succ
#print axioms generator_order

end DiophantineConsistency.CurrentAuxiliaryOrder2011Checks
