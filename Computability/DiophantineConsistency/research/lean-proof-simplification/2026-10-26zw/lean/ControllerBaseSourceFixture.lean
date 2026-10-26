import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity

/-! Exact source-body fixture. Constant identities and parity facts are
explicit hypotheses; no source-order theorem is assumed. -/
namespace DiophantineProofIdeas.ControllerBaseSourceFixture
section
variable (B d auxiliary : ℕ)
variable (B_eq : B = 2 ^ 94517) (d_odd : Odd d) (auxiliary_odd : Odd auxiliary)

include B_eq d_odd auxiliary_odd

theorem block_base_isUnit (k : ℕ) :
    IsUnit (B : ZMod ((d*auxiliary)*auxiliary^k)) := by
  rw [B_eq, Nat.cast_pow]
  exact ((ZMod.isUnit_iff_coprime 2 _).mpr (Nat.coprime_two_left.mpr
    ((d_odd.mul auxiliary_odd).mul auxiliary_odd.pow))).pow 94517

#print axioms block_base_isUnit

end
end DiophantineProofIdeas.ControllerBaseSourceFixture
