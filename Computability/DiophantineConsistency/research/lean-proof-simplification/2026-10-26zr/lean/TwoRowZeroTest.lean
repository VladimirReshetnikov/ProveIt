import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
The two non-Boolean rows already determine the zero-test bit.
The explicit nonzero slack premise is essential.  The literal Boolean row
can remain in the repository's polynomial system without being used here.
-/
namespace ProofRefinements

section Minimal
variable {R : Type*} [CommSemiring R] [IsCancelMulZero R] [DecidableEq R]

theorem zeroTest_two_rows {bit n slack : R}
    (hs : slack+1 ≠ 0) (hbn : bit*n = 0)
    (hns : n+bit*(slack+1) = slack+1) :
    bit = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp only [hn, zero_add] at hns
    simpa only [if_pos hn] using
      mul_right_cancel₀ hs (hns.trans (one_mul _).symm)
  · simpa only [if_neg hn] using (mul_eq_zero.mp hbn).resolve_right hn

end Minimal

section OrderedCarrier
variable {R : Type*} [CommSemiring R] [LinearOrder R]
  [CanonicallyOrderedAdd R] [IsStrictOrderedRing R]

/-- This matches the three-row certificate consumed by the existing proof.
The first conjunct is retained in the statement and deliberately unused. -/
theorem zeroTest_certificate_sound {bit n slack : R} (hs : slack+1 ≠ 0)
    (h : bit*bit = bit ∧ bit*n = 0 ∧ n+bit*(slack+1) = slack+1) :
    bit = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · have he : bit*(slack+1) = 1*(slack+1) := by
      simpa only [hn, zero_add, one_mul] using h.2.2
    simpa only [if_pos hn] using mul_right_cancel₀ hs he
  · simpa only [if_neg hn] using (mul_eq_zero.mp h.2.1).resolve_right hn

end OrderedCarrier

#print axioms zeroTest_two_rows
#print axioms zeroTest_certificate_sound

end ProofRefinements
