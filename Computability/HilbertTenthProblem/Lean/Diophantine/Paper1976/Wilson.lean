import Mathlib.NumberTheory.Wilson

/-!
# JSWW 1976, Lemma 2.9 (Wilson's theorem)

> **Lemma 2.9.** For any number `k ≥ 1`, `k+1` is prime if and only if `k+1 ∣ k! + 1`.

This is Mathlib's `Nat.prime_iff_fac_equiv_neg_one` restated with divisibility.
-/

namespace JSWW1976

/-- Lemma 2.9. -/
theorem lemma_2_9 {k : ℕ} (hk : 1 ≤ k) : Nat.Prime (k + 1) ↔ k + 1 ∣ k.factorial + 1 := by
  have h1 : k + 1 ≠ 1 := by omega
  rw [Nat.prime_iff_fac_equiv_neg_one h1, Nat.add_sub_cancel]
  constructor
  · intro h
    have : ((k.factorial + 1 : ℕ) : ZMod (k + 1)) = 0 := by
      push_cast; rw [h]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  · intro h
    have : ((k.factorial + 1 : ℕ) : ZMod (k + 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at this
    linear_combination this

end JSWW1976
