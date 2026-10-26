import DiophantineConsistency.CurrentControllerData2011

/-! Exact finite controller data and explicit limits of the kernel-residue
interface. The conditional Hs tests are not a proof of the actual K residues. -/

namespace DiophantineConsistency.CurrentControllerData2011Checks

open CurrentControllerData2011

set_option Elab.async false
set_option maxRecDepth 10000

example : d = 47*2011 ∧ d = 94517 ∧ Odd d ∧ Squarefree d :=
  ⟨d_factors,d_eq,d_odd,d_squarefree⟩

example : Nat.Prime 47 ∧ Nat.Prime 2011 ∧ Nat.Prime auxiliary :=
  ⟨prime_47,prime_2011,prime_auxiliary⟩

example : orderOf (2 : ZMod 47) = 23 ∧ orderOf (2 : ZMod 2011) = 402 ∧
    orderOf (B : ZMod 47) = 23 ∧ orderOf (B : ZMod 2011) = 402 :=
  ⟨two_order_47,two_order_2011,B_order_47,B_order_2011⟩

/-- 2011 is prime, but the order of 2 is not its full multiplicative group size. -/
example : orderOf (2 : ZMod 2011) ≠ 2010 := by rw [two_order_2011]; decide

example : (2 : ZMod 2011)^201 ≠ 1 := by rw [proper_power_2011_2]; decide
example : (2 : ZMod 2011)^134 ≠ 1 := by rw [proper_power_2011_3]; decide
example : (2 : ZMod 2011)^6 ≠ 1 := by rw [proper_power_2011_67]; decide

example : Nat.lcm 23 402 = spacing ∧ spacing ∣ auxiliary-1 ∧ d < auxiliary :=
  ⟨spacing_lcm,spacing_dvd,auxiliary_gt_d⟩

example : B % 47 = 37 ∧ B % 2011 = 1283 ∧ B % auxiliary = 37435 :=
  ⟨B_mod_47,B_mod_2011,B_mod_auxiliary⟩

example : B^2 % 47 = 6 ∧ B^2 % 2011 = 1091 ∧ B^2 % auxiliary = 99283 :=
  ⟨B_square_mod_47,B_square_mod_2011,B_square_mod_auxiliary⟩

example : B^(auxiliary-1) % auxiliary^2 = 7300767062 ∧
    B^(auxiliary-1) % auxiliary^2 ≠ 1 := ⟨auxiliary_lift,lift_ne_one⟩

example : 7300767062 = 1+auxiliary*60739 ∧ 0 < (60739 : ℕ) ∧ 60739 < auxiliary :=
  lift_nonzero_digit

/-- The actual kernel residue is a visible premise in each wrapper. -/
example (h47 : CurrentKernel2011.K % 47 = 26)
    (h2011 : CurrentKernel2011.K % 2011 = 1995)
    (haux : CurrentKernel2011.K % auxiliary = 114787) :
    (1+B*CurrentKernel2011.K+B^2) % 47 = 29 ∧
    (1+B*CurrentKernel2011.K+B^2) % 2011 = 674 ∧
    (1+B*CurrentKernel2011.K+B^2) % auxiliary = 36379 :=
  ⟨Hs_mod_47 h47,Hs_mod_2011 h2011,Hs_mod_auxiliary haux⟩

#print axioms B_eq
#print axioms prime_47
#print axioms prime_2011
#print axioms prime_auxiliary
#print axioms d_squarefree
#print axioms two_order_47
#print axioms two_order_2011
#print axioms B_order_47
#print axioms B_order_2011
#print axioms spacing_lcm
#print axioms spacing_coprime
#print axioms B_mod_47
#print axioms B_mod_2011
#print axioms B_mod_auxiliary
#print axioms B_square_mod_auxiliary
#print axioms auxiliary_lift
#print axioms lift_nonzero_digit
#print axioms lift_ne_one
#print axioms Hs_mod_47
#print axioms Hs_mod_2011
#print axioms Hs_mod_auxiliary

end DiophantineConsistency.CurrentControllerData2011Checks
