import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-! The selector follows from annihilation and balance, without an idempotence premise. -/
namespace ProofReview.ZeroTestTwoRows

theorem selector_of_annihilation_balance
    {R : Type*} [CommSemiring R] [IsCancelMulZero R] [DecidableEq R]
    {bit n unit : R} (hu : unit ≠ 0)
    (hn : bit * n = 0) (hs : n + bit * unit = unit) :
    bit = if n = 0 then 1 else 0 := by
  split_ifs with hzero
  · apply mul_right_cancel₀ hu
    simpa only [hzero, zero_add, one_mul] using hs
  · exact (mul_eq_zero.mp hn).resolve_right hzero

theorem integer_selector (bit n slack : ℕ)
    (hn : (bit : ℤ) * (n : ℤ) = 0)
    (hs : (n : ℤ) - (1 - (bit : ℤ)) * ((slack : ℤ) + 1) = 0) :
    bit = if n = 0 then 1 else 0 := by
  have h := selector_of_annihilation_balance
    (unit := (slack : ℤ) + 1) (by omega) hn (by nlinarith only [hs])
  exact_mod_cast h

theorem natural_selector (bit n slack : ℕ)
    (hn : bit * n = 0) (hs : n + bit * (slack + 1) = slack + 1) :
    bit = if n = 0 then 1 else 0 :=
  selector_of_annihilation_balance (Nat.succ_ne_zero slack) hn hs

theorem idempotence_redundant (bit n slack : ℕ)
    (hn : bit * n = 0) (hs : n + bit * (slack + 1) = slack + 1) :
    bit * bit = bit := by
  rw [natural_selector bit n slack hn hs]
  split_ifs <;> decide

-- Literal predicate copied from QuadraticBoolean; the old first field remains.
namespace ExternalFixture
def ZeroCertificate (bit n slack : ℕ) : Prop :=
  (bit : ℤ) * ((bit : ℤ) - 1) = 0 ∧
  (bit : ℤ) * (n : ℤ) = 0 ∧
  (n : ℤ) - (1 - (bit : ℤ)) * ((slack : ℤ) + 1) = 0

theorem zero_certificate_sound {bit n slack : ℕ} (h : ZeroCertificate bit n slack) :
    bit = if n = 0 then 1 else 0 :=
  integer_selector bit n slack h.2.1 h.2.2
theorem zero_certificate_sound_direct {bit n slack : ℕ} (h : ZeroCertificate bit n slack) :
    bit = if n = 0 then 1 else 0 := by
  rcases h with ⟨-, hn, hs⟩
  by_cases hz : n = 0 <;> simp_all [mul_eq_zero]
  omega

end ExternalFixture

-- Exact internal certificate shape over an abstract admissible semiring.
-- The production instantiation is R = ObjectOmegaSemiring.Natural H.
namespace InternalFixture
variable {R : Type*} [CommSemiring R] [IsCancelMulZero R]
  [DecidableEq R]

def Certificate (bit n slack : R) : Prop :=
  bit * bit = bit ∧ bit * n = 0 ∧ n + bit * (slack + 1) = slack + 1

theorem certificate_sound {bit n slack : R} (hu : slack + 1 ≠ 0)
    (h : Certificate bit n slack) : bit = if n = 0 then 1 else 0 :=
  selector_of_annihilation_balance hu h.2.1 h.2.2
theorem certificate_sound_direct {bit n slack : R} (hu : slack + 1 ≠ 0)
    (h : Certificate bit n slack) : bit = if n = 0 then 1 else 0 := by
  rcases h with ⟨-, hn, hs⟩
  by_cases hz : n = 0 <;> simp_all [mul_eq_zero, mul_eq_right₀ hu]

end InternalFixture

-- ObjectNaturalOrderedSemiring installs these exact algebra/order classes.
example {R : Type*} [CommSemiring R] [LinearOrder R] [CanonicallyOrderedAdd R]
    [IsStrictOrderedRing R] :
    IsCancelMulZero R := inferInstance

example : (0 : ℕ) * 1 = 0 ∧ 1 + 0 * (0 + 1) = 0 + 1 := by decide
example : (1 : ℕ) * 0 = 0 ∧ 0 + 1 * (7 + 1) = 7 + 1 := by decide

-- The nonzero guard is essential: unit = n = 0 allows every bit.
example : (2 : ℕ) * 0 = 0 ∧ 0 + 2 * 0 = 0 ∧ (2 : ℕ) ≠ 1 := by decide

#print axioms selector_of_annihilation_balance
#print axioms integer_selector
#print axioms natural_selector
#print axioms idempotence_redundant
#print axioms ExternalFixture.zero_certificate_sound
#print axioms InternalFixture.certificate_sound
#print axioms ExternalFixture.zero_certificate_sound_direct
#print axioms InternalFixture.certificate_sound_direct

end ProofReview.ZeroTestTwoRows
