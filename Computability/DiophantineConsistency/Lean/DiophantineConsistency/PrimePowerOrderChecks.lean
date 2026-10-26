import DiophantineConsistency.PrimePowerOrder

namespace DiophantineConsistency.PrimePowerOrderChecks

open PrimePowerOrder
set_option Elab.async false

-- The base modulus has order1, not p.
example : orderOf (4 : ZMod (3^1)) = 1 := by
  simpa using order_prime_power (p:=3) (g:=4) (n:=1)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : orderOf (4 : ZMod (3^3)) = 9 := by
  simpa using order_prime_power (p:=3) (g:=4) (n:=3)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example (k : ℕ) : 3^(k+1) ∣ 4^(3^k)-1 ∧ ¬ 3^(k+2) ∣ 4^(3^k)-1 :=
  exact_lift (by decide) (by decide) (by decide) (by decide) k

-- Natural subtraction at g=0 or1 cannot satisfy the nontrivial lift.
example (p : ℕ) : p^2 ∣ (0 : ℕ)-1 := by simp
example (p : ℕ) : p^2 ∣ (1 : ℕ)-1 := by simp

-- The odd-prime hypothesis matters:3 modulo8 has order2, not4.
example : orderOf (3 : ZMod 8) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide) (by decide)
example : 2 ∣ (3 : ℕ)-1 ∧ ¬ 2^2 ∣ (3 : ℕ)-1 := by decide

-- A lift divisible by p² may instead have order1 already modulo p².
example : orderOf (10 : ZMod 9) = 1 :=
  orderOf_eq_one_iff.mpr (by decide)
example : 3^2 ∣ (10 : ℕ)-1 := by decide

-- The generic cast bridge includes exponent0 and even modulus0.
example : (4 : ZMod 0)^0 = 1 ↔ (0 : ℕ) ∣ 4^0-1 :=
  pow_cast_eq_one_iff (by decide) 0

#print axioms one_lt_of_not_square
#print axioms not_dvd_of_dvd_sub_one
#print axioms pow_cast_eq_one_iff
#print axioms exact_lift
#print axioms order_succ
#print axioms order_prime_power

end DiophantineConsistency.PrimePowerOrderChecks
