import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity

namespace DiophantineProofIdeas.ControllerBaseUnit

/-- A power of two is a unit modulo every odd modulus; the claim does not
need an element-order computation or a prime-power lifting theorem. -/
theorem power_two_unit {m : ℕ} (hm : Odd m) (a : ℕ) :
    IsUnit ((2 ^ a : ℕ) : ZMod m) :=
  (ZMod.isUnit_iff_coprime _ _).mpr ((Nat.coprime_two_left.mpr hm).pow_left a)

/-- Exact shape of the actual block modulus, valid also for k=0. -/
theorem block_base_unit (k : ℕ) :
    IsUnit ((2 ^ 94517 : ℕ) : ZMod (((47 * 2011) * 120199) * 120199 ^ k)) := by
  apply power_two_unit
  exact (by decide : Odd ((47 * 2011) * 120199)).mul ((by decide : Odd 120199).pow)

#print axioms power_two_unit
#print axioms block_base_unit

end DiophantineProofIdeas.ControllerBaseUnit
