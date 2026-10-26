import DiophantineConsistency.SparseBorrowCarry

/-!+# The exact signed-prefix meaning of the existing finite borrow recurrence

The implementation and radix word are unchanged. The conclusion identifies
both parts of Euclidean division, including when the signed value is negative.
-/

namespace DiophantineConsistency.SignedPrefix

open Finset SparseBorrowCarry
open scoped BigOperators

/-- The terminal borrow is the quotient and the word is the remainder of
the complete signed prefix at radix `B^n`. This also covers `n = 0`. -/
theorem prefix_divmod {B n : ℕ} (hB : 1 < B) (a : ℕ → ℤ)
    (ha : ∀ i < n, -(B : ℤ) < a i ∧ a i < (B : ℤ)) :
    (∑ i ∈ range n, a i * (B : ℤ)^i) / (B : ℤ)^n = borrow a n ∧
    (∑ i ∈ range n, a i * (B : ℤ)^i) % (B : ℤ)^n = (word B n a : ℤ) := by
  apply (Int.ediv_emod_unique (by positivity)).mpr
  refine ⟨?_, by positivity, ?_⟩
  · rw [word_cast (by omega) a ha]
    exact digit_sum B n a
  · exact_mod_cast word_lt hB a ha

/-- Final borrow detection depends only on the sign of the full prefix. -/
theorem borrow_zero_iff {B n : ℕ} (hB : 1 < B) (a : ℕ → ℤ)
    (ha : ∀ i < n, -(B : ℤ) < a i ∧ a i < (B : ℤ)) :
    borrow a n = 0 ↔ 0 ≤ ∑ i ∈ range n, a i * (B : ℤ)^i := by
  have hs := digit_sum B n a
  rw [← word_cast (by omega) a ha] at hs
  constructor
  · intro hz
    rw [hz, mul_zero, add_zero] at hs
    exact hs ▸ Int.natCast_nonneg _
  · intro hvalue
    have hq := (prefix_divmod hB a ha).1
    have hnonneg : 0 ≤ borrow a n := by
      rw [← hq]
      exact Int.ediv_nonneg hvalue (by positivity)
    rcases borrow_cases a n with h | h <;> omega

/-- The old nonnegative-value contract is a corollary of terminal-borrow
classification, with no new condition on the individual coefficients. -/
theorem word_eq_toNat_of_nonneg {B n : ℕ} (hB : 1 < B) (a : ℕ → ℤ)
    (ha : ∀ i < n, -(B : ℤ) < a i ∧ a i < (B : ℤ))
    (hvalue : 0 ≤ ∑ i ∈ range n, a i * (B : ℤ)^i) :
    word B n a = (∑ i ∈ range n, a i * (B : ℤ)^i).toNat := by
  have hs := digit_sum B n a
  rw [← word_cast (by omega) a ha,
    (borrow_zero_iff hB a ha).mpr hvalue, mul_zero, add_zero] at hs
  exact congrArg Int.toNat hs

/-- Negative total values are intentionally kept: `-1` produces the
largest two-digit base-four word and an outstanding borrow of `-1`. -/
example : borrow (fun i => if i = 0 then (-1 : ℤ) else 0) 2 = -1 ∧
    word 4 2 (fun i => if i = 0 then (-1 : ℤ) else 0) = 15 := by
  decide

example {B : ℕ} (hB : 1 < B) (a : ℕ → ℤ) :
    (∑ i ∈ range 0, a i * (B : ℤ)^i) / (B : ℤ)^0 = borrow a 0 ∧
    (∑ i ∈ range 0, a i * (B : ℤ)^i) % (B : ℤ)^0 = (word B 0 a : ℤ) :=
  prefix_divmod hB a (by simp)

#print axioms prefix_divmod
#print axioms borrow_zero_iff
#print axioms word_eq_toNat_of_nonneg

end DiophantineConsistency.SignedPrefix
