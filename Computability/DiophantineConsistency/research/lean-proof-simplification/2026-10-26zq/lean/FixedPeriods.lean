import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-! The fixed CRT components require annihilating powers. Exact order is
reserved for the auxiliary prime-power component and the orbit injection. -/
namespace NewControllerProofs.FixedPeriods

set_option Elab.async false
set_option maxRecDepth 10000

theorem pow_eq_one_of_dvd_period {M : Type*} [Monoid M]
    {x : M} {m e : ℕ} (hm : x ^ m = 1) (hdiv : m ∣ e) : x ^ e = 1 := by
  obtain ⟨k, rfl⟩ := hdiv
  rw [pow_mul, hm, one_pow]

theorem power_preserves_period {M : Type*} [Monoid M]
    {x : M} {m : ℕ} (hm : x ^ m = 1) (s : ℕ) : (x ^ s) ^ m = 1 := by
  rw [← pow_mul, Nat.mul_comm s m, pow_mul, hm, one_pow]

-- These are the actual bounded fixed-prime certificates.
theorem two_period_47 : (2 : ZMod 47) ^ 23 = 1 := by reduce_mod_char
theorem two_period_2011 : (2 : ZMod 2011) ^ 402 = 1 := by reduce_mod_char

theorem B_period_47 : ((2 : ZMod 47) ^ 94517) ^ 23 = 1 :=
  power_preserves_period two_period_47 _

theorem B_period_2011 : ((2 : ZMod 2011) ^ 94517) ^ 402 = 1 :=
  power_preserves_period two_period_2011 _

theorem generator_projection_47 :
    ((2 : ZMod 47) ^ 94517) ^ (120199 - 1) = 1 :=
  pow_eq_one_of_dvd_period B_period_47 (by decide)

theorem generator_projection_2011 :
    ((2 : ZMod 2011) ^ 94517) ^ (120199 - 1) = 1 :=
  pow_eq_one_of_dvd_period B_period_2011 (by decide)

-- Alternative for the fixed literal controller: one bounded modular
-- certificate proves the complete projection, with logarithmic powering.
-- This does not compute the unreduced natural number 2^11360754366.
theorem generator_projection_C0 :
    ((2 : ZMod (94517 * 120199)) ^ 94517) ^ (120199 - 1) = 1 := by
  rw [← pow_mul]
  reduce_mod_char

-- Periods alone cannot justify power-orbit injectivity.
example : (1 : ZMod 9) ^ 3 = 1 := by decide
example : orderOf (1 : ZMod 9) ≠ 3 := by simp

#print axioms pow_eq_one_of_dvd_period
#print axioms power_preserves_period
#print axioms B_period_47
#print axioms B_period_2011
#print axioms generator_projection_47
#print axioms generator_projection_2011
#print axioms generator_projection_C0

end NewControllerProofs.FixedPeriods
