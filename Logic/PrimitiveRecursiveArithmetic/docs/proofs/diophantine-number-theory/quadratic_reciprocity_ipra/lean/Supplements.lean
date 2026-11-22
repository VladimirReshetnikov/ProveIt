import QuadraticReciprocity

namespace QR

/-- The number of flagged indices in `1,...,n` above a cut at `t`. -/
private theorem sum_cut (f : Nat → Nat) (t n : Nat)
    (hf : ∀ i, 0 < i → i ≤ n → f i = if t < i then 1 else 0) :
    sum1 f n = n - t := by
  induction n with
  | zero => simp [sum1]
  | succ n ih =>
    rw [sum1, ih (fun i hi hin => hf i hi (by omega)), hf (n+1) (by omega) (by omega)]
    split <;> omega

/-- Reduction of a positive index multiplied by the residue class of minus one. -/
private theorem neg_one_mul_residue (p i : Nat) (hi : 0 < i) (hip : i < p) :
    (p - 1) * i % p = p - i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := i) (by omega)
  have hmul := Nat.succ_mul (p-1) (j+1)
  have hp : (p-1).succ = p := by omega
  rw [hp, Nat.mul_succ p j] at hmul
  have hrepr : (p-1) * (j+1) = p*j + (p - (j+1)) := by omega
  rw [hrepr, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- All the residues of `-i` in the Gauss half-list are high. -/
theorem highCount_neg_one (p : Nat) (hp : 0 < p) :
    highCount p (p-1) = half p := by
  unfold highCount
  apply Eq.trans (sum_cut _ 0 _ ?_)
  · exact Nat.sub_zero _
  · intro i hi hih
    have hbound : 2 * half p < p := by unfold half; omega
    rw [neg_one_mul_residue p i hi (by omega)]
    simp [show half p < p-i by omega, hi]

/-- Exactly the upper part of the index interval contributes for numerator two. -/
theorem highCount_two (p : Nat) (hp : 0 < p) :
    highCount p 2 = half p - half p / 2 := by
  unfold highCount
  apply sum_cut
  intro i _ hih
  have hbound : 2 * half p < p := by unfold half; omega
  rw [Nat.mod_eq_of_lt (show 2*i < p by omega)]
  by_cases hc : half p / 2 < i
  · simp [hc, show half p < 2*i by omega]
  · simp [hc, show ¬half p < 2*i by omega]

/-- The sign for minus one is negative exactly in the class three modulo four. -/
theorem highCount_neg_one_mod_four (p : Nat) (hp : p % 2 = 1) :
    highCount p (p-1) % 2 = if p % 4 = 3 then 1 else 0 := by
  rw [highCount_neg_one p (by omega)]
  unfold half
  split <;> omega

/-- Convert the number of high terms for two into the residue-class test. -/
theorem highCount_two_mod_eight (p : Nat) (hp : p % 2 = 1) :
    highCount p 2 % 2 = if p % 8 = 3 ∨ p % 8 = 5 then 1 else 0 := by
  rw [highCount_two p (by omega)]
  unfold half
  split <;> omega

/-- The parity of the textbook exponent is also the residue-class test. -/
theorem two_exponent_mod_eight (p : Nat) (hp : p % 2 = 1) :
    ((p*p-1)/8) % 2 = if p % 8 = 3 ∨ p % 8 = 5 then 1 else 0 := by
  have hsq := Nat.mul_mod p p 16
  have hpos := Nat.mul_pos (show 0 < p by omega) (show 0 < p by omega)
  have hr : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨
      p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by omega
  rcases hr with h|h|h|h|h|h|h|h <;> rw [h] at hsq <;>
    split <;> omega

/-- The Gauss count for two has the parity of the standard quadratic exponent. -/
theorem highCount_two_exponent (p : Nat) (hp : p % 2 = 1) :
    highCount p 2 % 2 = ((p*p-1)/8) % 2 :=
  (highCount_two_mod_eight p hp).trans (two_exponent_mod_eight p hp).symm

end QR
