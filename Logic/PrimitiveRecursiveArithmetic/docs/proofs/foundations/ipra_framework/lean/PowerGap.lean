import Std

/-!
Native arithmetic lemmas for the superelliptic power-gap argument.
These are Lean theorems over Nat. They are not embedded iPRA derivations.
The integer lemma includes every sign and parity case. Polynomial bounds
and the certificate compiler remain formalization work, specified in the
accompanying article.
-/

namespace IPRAFramework.PowerGap

/-- The gap between distinct nonnegative integer powers is at least
the preceding power of the larger base. No division is used. -/
theorem lower_gap (a b n : Nat) (h : b < a) :
    b ^ (n + 1) + a ^ n ≤ a ^ (n + 1) := by
  calc
    b ^ (n + 1) + a ^ n = b ^ n * b + a ^ n := by
      rw [Nat.pow_succ]
    _ ≤ a ^ n * b + a ^ n :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_right b (Nat.pow_le_pow_left (Nat.le_of_lt h) n)) _
    _ = a ^ n * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ a ^ n * a := Nat.mul_le_mul_left _ h
    _ = a ^ (n + 1) := (Nat.pow_succ _ _).symm

/-- The gap on the other side is at least the preceding power of
the smaller base as well. -/
theorem upper_gap (a b n : Nat) (h : a < b) :
    a ^ (n + 1) + a ^ n ≤ b ^ (n + 1) := by
  have hp : a ^ n ≤ b ^ n := Nat.pow_le_pow_left (Nat.le_of_lt h) n
  exact Nat.le_trans (Nat.add_le_add_left hp _) (lower_gap b a n h)

/-- An integer strictly between a power and the next possible power
cannot itself be a power. -/
theorem small_positive_perturbation (a b n r : Nat)
    (hr : 0 < r) (hsmall : r < a ^ n) :
    b ^ (n + 1) ≠ a ^ (n + 1) + r := by
  intro heq
  by_cases h : a < b
  · have hg := upper_gap a b n h
    omega
  · have hle : b ≤ a := by omega
    have hp := Nat.pow_le_pow_left hle (n + 1)
    omega

/-- The analogous exclusion below a power. -/
theorem small_negative_perturbation (a b n r : Nat)
    (hr : 0 < r) (hsmall : r < a ^ n) :
    b ^ (n + 1) + r ≠ a ^ (n + 1) := by
  intro heq
  by_cases h : b < a
  · have hg := lower_gap a b n h
    omega
  · have hle : a ≤ b := by omega
    have hp := Nat.pow_le_pow_left hle (n + 1)
    omega

/-- All integer sign and parity cases, obtained from absolute values and
the triangle inequality. Exponent `n + 1` is positive. -/
theorem integer_gap (a b : Int) (n : Nat)
    (h : b ^ (n + 1) ≠ a ^ (n + 1)) :
    a.natAbs ^ n ≤ (b ^ (n + 1) - a ^ (n + 1)).natAbs := by
  have ht := Int.natAbs_add_le (b ^ (n + 1) - a ^ (n + 1)) (a ^ (n + 1))
  simp only [Int.sub_add_cancel, Int.natAbs_pow] at ht
  have ht' := Int.natAbs_add_le (a ^ (n + 1) - b ^ (n + 1)) (b ^ (n + 1))
  have rev : (a ^ (n + 1) - b ^ (n + 1)).natAbs =
      (b ^ (n + 1) - a ^ (n + 1)).natAbs := by
    rw [show a ^ (n + 1) - b ^ (n + 1) =
        -(b ^ (n + 1) - a ^ (n + 1)) by omega, Int.natAbs_neg]
  simp only [Int.sub_add_cancel, Int.natAbs_pow, rev] at ht'
  by_cases hlt : a.natAbs < b.natAbs
  · have hg := upper_gap a.natAbs b.natAbs n hlt
    omega
  by_cases hgt : b.natAbs < a.natAbs
  · have hg := lower_gap a.natAbs b.natAbs n hgt
    omega
  have habs : a.natAbs = b.natAbs := by omega
  have habsPow : (b ^ (n + 1)).natAbs = (a ^ (n + 1)).natAbs := by
    simp only [Int.natAbs_pow, habs]
  rcases Int.natAbs_eq_natAbs_iff.mp habsPow with heq | hneg
  · exact False.elim (h heq)
  · have haPos : 1 ≤ a.natAbs := by
      by_cases hzero : a.natAbs = 0
      · have ha0 : a = 0 := Int.natAbs_eq_zero.mp hzero
        have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
        simp [ha0, hb0] at h
      · omega
    have hp : a.natAbs ^ n ≤ a.natAbs ^ (n + 1) := by
      calc
        a.natAbs ^ n = a.natAbs ^ n * 1 := by simp
        _ ≤ a.natAbs ^ n * a.natAbs := Nat.mul_le_mul_left _ haPos
        _ = a.natAbs ^ (n + 1) := (Nat.pow_succ _ _).symm
    rw [hneg, show -a ^ (n + 1) - a ^ (n + 1) = (-2) * a ^ (n + 1) by omega]
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    change a.natAbs ^ n ≤ 2 * a.natAbs ^ (n + 1)
    omega

#print axioms lower_gap
#print axioms upper_gap
#print axioms small_positive_perturbation
#print axioms small_negative_perturbation
#print axioms integer_gap

end IPRAFramework.PowerGap
