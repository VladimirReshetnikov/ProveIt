import DiophantineConsistency.NativeRadixDigits

/-! One origin-correction theorem for both generations of high masks. -/
namespace DiophantineConsistency.RefactorWordOrigin

open NativeCyclicConvolution NativeRadixDigits

variable {n : ℕ} [NeZero n]

/-- The guard prevents a borrow from leaving the origin digit. -/
theorem word_sub_origin (r q : ℕ) (a : ZMod n → ℕ) (hq : q ≤ a 0) :
    word r (fun k => a k - if k = 0 then q else 0) = word r a - q := by
  have he (k : ZMod n) :
      (a k - if k = 0 then q else 0) + (if k = 0 then q else 0) = a k := by
    apply Nat.sub_add_cancel
    by_cases hk : k = 0
    · simpa [hk] using hq
    · simp only [if_neg hk, Nat.zero_le]
  have hw := congrArg (word r) (funext he)
  rw [word_add, word_origin] at hw
  exact Nat.eq_sub_of_add_eq hw

#print axioms word_sub_origin

end DiophantineConsistency.RefactorWordOrigin
