import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.GroupWithZero.Idempotent

namespace PostBaseline
variable {R : Type*} [CommSemiring R] [LinearOrder R] [CanonicallyOrderedAdd R]
  [IsOrderedCancelAddMonoid R] [NoZeroDivisors R] [Nontrivial R]

omit [Nontrivial R] in
theorem mul_strict_left (a b c : R) (ha : 0 < a) (hbc : b < c) : a*b < a*c := by
  obtain ⟨d, hd⟩ := exists_add_of_le hbc.le
  have hd0 : d ≠ 0 := by
    intro hz
    apply hbc.ne
    simpa only [hz, add_zero] using hd.symm
  rw [hd, mul_add]
  exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (mul_ne_zero ha.ne' hd0))

theorem orderedFromCanonical : IsStrictOrderedRing R where
  __ := (inferInstance : IsOrderedCancelAddMonoid R)
  __ := (inferInstance : Nontrivial R)
  zero_le_one := zero_le
  mul_lt_mul_of_pos_left a ha b c hbc := mul_strict_left a b c ha hbc
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [mul_comm] using mul_strict_left a b c ha hbc

theorem mul_self_eq_self_iff (x : R) : x*x=x ↔ x=0 ∨ x=1 := by
  letI : IsStrictOrderedRing R := orderedFromCanonical
  exact IsIdempotentElem.iff_eq_zero_or_one

#print axioms PostBaseline.mul_self_eq_self_iff
end PostBaseline
