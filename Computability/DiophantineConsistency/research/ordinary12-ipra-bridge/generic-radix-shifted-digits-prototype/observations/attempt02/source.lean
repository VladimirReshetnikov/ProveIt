import Mathlib.Data.Nat.Digits.Lemmas

/-! A repunit shift can be absorbed by one low-digit decrement and one
    appended high digit, provided the low digit was already positive. -/
set_option autoImplicit false
set_option Elab.async false
namespace RadixShiftedDigits

theorem add_repunit (b k a : ℕ) (tail : List ℕ) (hb : 0 < b)
    (hlen : tail.length + 1 = k) :
    (b^k - 1) + Nat.ofDigits b ((a+1)::tail) =
      Nat.ofDigits b ((a::tail) ++ [1]) := by
  have hp : 1 ≤ b^k := Nat.one_le_pow k b hb
  rw [Nat.ofDigits_append]
  simp only [List.length_cons, Nat.ofDigits_cons, Nat.ofDigits_nil, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one]
  rw [hlen]
  omega

#print axioms RadixShiftedDigits.add_repunit
end RadixShiftedDigits
