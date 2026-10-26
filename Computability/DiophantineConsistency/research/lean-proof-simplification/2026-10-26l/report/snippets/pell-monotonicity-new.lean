theorem coordinates_mono_base {A B : ℕ} (hA : 1 < A) (hB : 1 < B)
    (hAB : A ≤ B) (n : ℕ) :
    xn hA n ≤ xn hB n ∧ yn hA n ≤ yn hB n := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact ⟨Nat.add_le_add (Nat.mul_le_mul ih.1 hAB)
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul hAB hAB) 1) ih.2),
      Nat.add_le_add ih.1 (Nat.mul_le_mul ih.2 hAB)⟩
