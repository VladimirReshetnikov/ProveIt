import Surreal.Algebra.PellTwoDivisibility

/-!
# Growth and parity of the ordinary Pell sequence

Completes `odg:lem:pellsequence` and `odg:eq:pellmod8`: positivity,
exponential growth, alternating residues modulo eight, and arbitrarily
large coordinates in each parity subsequence. All indices are ordinary naturals.
-/

namespace Surreal.PellTwo

/-- The first Pell coordinate is positive, including at index zero. -/
theorem X_pos (k : ℕ) : 0 < X k :=
  Pell.Solution₁.x_pow_pos (by norm_num [fundamental]) k

/-- The second coordinate is nonnegative, including at index zero. -/
theorem Y_nonneg (k : ℕ) : 0 ≤ Y k := by
  cases k with
  | zero => simp [Y]
  | succ k => exact le_of_lt (Y_pos (Nat.succ_pos k))

/-- The lower bound printed in the Pell-witness lemma. -/
theorem three_pow_le_X (k : ℕ) : (3 : ℤ) ^ k ≤ X k := by
  induction k with
  | zero => simp [X]
  | succ k ih =>
    rw [X_succ, pow_succ]
    have := Y_nonneg k
    nlinarith

/-- A convenient linear consequence for constructing witnesses above a bound. -/
theorem index_lt_X (k : ℕ) : (k : ℤ) < X k := by
  induction k with
  | zero => exact X_pos 0
  | succ k ih =>
    rw [X_succ, Nat.cast_add, Nat.cast_one]
    have := Y_nonneg k
    have := X_pos k
    linarith

/-- The second-order recurrence used to compute the residues modulo eight. -/
theorem X_add_two (k : ℕ) : X (k + 2) = 6 * X (k + 1) - X k := by
  rw [show k + 2 = (k + 1) + 1 by omega, X_succ, X_succ, Y_succ]
  ring

/-- Even and odd indices have first coordinates congruent to 1 and 3. -/
theorem X_parity_mod_eight (j : ℕ) :
    X (2 * j) ≡ 1 [ZMOD 8] ∧ X (2 * j + 1) ≡ 3 [ZMOD 8] := by
  induction j with
  | zero => norm_num [X, fundamental, Int.ModEq]
  | succ j ih =>
    have h₁ := X_add_two (2 * j)
    have h₂ := X_add_two (2 * j + 1)
    rcases ih with ⟨he, ho⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by omega,
      show 2 * j + 2 + 1 = (2 * j + 1) + 2 by omega]
    simp only [Int.ModEq] at he ho ⊢
    have hn : X (2 * j + 2) % 8 = 1 % 8 := by
      rw [h₁, Int.sub_emod, Int.mul_emod, ho, he]
      norm_num
    refine ⟨hn, ?_⟩
    rw [h₂, show 2 * j + 1 + 1 = 2 * j + 2 by omega,
      Int.sub_emod, Int.mul_emod, hn, ho]
    norm_num

/-- Both parity subsequences exceed every ordinary integer bound. -/
theorem exists_parity_bounds (b : ℤ) :
    ∃ j : ℕ, b < X (2 * j) ∧ b < X (2 * j + 1) := by
  refine ⟨b.toNat + 1, ?_, ?_⟩
  · have := index_lt_X (2 * (b.toNat + 1))
    have : b ≤ (b.toNat : ℤ) := by omega
    push_cast at *
    omega
  · have := index_lt_X (2 * (b.toNat + 1) + 1)
    have : b ≤ (b.toNat : ℤ) := by omega
    push_cast at *
    omega

/-- There is an ordinary Pell coordinate above any prescribed integer. -/
theorem exists_X_gt (b : ℤ) : ∃ k : ℕ, b < X k := by
  obtain ⟨j, hj, _⟩ := exists_parity_bounds b
  exact ⟨2 * j, hj⟩

end Surreal.PellTwo
