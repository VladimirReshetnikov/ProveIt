import DiophantineConsistency.NativeBaseBounds52

open DiophantineConsistency.NativeBaseBounds52

example : base (2 ^ 1182955) (2 ^ 0) = 2 ^ 1182967 := by
  simpa only [Nat.mul_zero, Nat.add_zero] using published_base_power 0

example (B b g : ℕ) (h : 8 * g < cap B b) : g < 4 * b * B ^ 174 :=
  weak_cap_of_ratio h

example (B b g : ℕ) (h : g < b * B ^ 174) : 32 * g < cap B b :=
  strong_cap_of_code h

example {n : ℕ} (lower : ℕ) (x : Fin n → ℕ) :
    lower < cofinalBound lower x ∧ ∀ i, x i < cofinalBound lower x :=
  ⟨(cofinalBound_spec lower x).1, (cofinalBound_spec lower x).2.1⟩

#print axioms base
#print axioms cofinalBound
#print axioms base_gt_four_digits
#print axioms packedBase_bounds
#print axioms published_base_power
#print axioms cofinalBound_spec
