import DiophantineConsistency.NativeCyclicRotation

/-!
# Every binary phase of a Boolean native word

A Boolean digit cannot overflow even at the last partial phase. Thus the
actual cyclic binary rotation is a scaled digit permutation, its digits
are at most half a radix, and every nonzero phase is even. These arithmetic
facts precede any temporal alignment or native tile interpretation.
-/

namespace DiophantineConsistency.NativeBooleanRotation

open NativeCyclicRotation

set_option Elab.async false

variable {n : ℕ}

/-- No quotient contribution occurs for any phase when the inputs are Boolean. -/
theorem rotation_eq_scaled {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (k : ZMod n) :
    binaryRotation v W c k =
      2 ^ (W % v) * c (k - ((W / v : ℕ) : ZMod n)) := by
  have hphase : W % v < v := Nat.mod_lt W hv
  have hp : 2 ^ (W % v) < 2 ^ v := Nat.pow_lt_pow_right (by decide) hphase
  have hsmall (i : ZMod n) : 2 ^ (W % v) * c i < 2 ^ v := by
    have h : 2 ^ (W % v) * c i ≤ 2 ^ (W % v) := by
      simpa only [mul_one] using Nat.mul_le_mul_left (2 ^ (W % v)) (hc i)
    exact lt_of_le_of_lt h hp
  unfold binaryRotation rotate
  exact shiftDigits_of_small c hsmall _

/-- The half-radix bound includes phase v−1, with no extra carry unit. -/
theorem rotation_le_half {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (k : ZMod n) :
    binaryRotation v W c k ≤ 2 ^ (v - 1) := by
  rw [rotation_eq_scaled hv W c hc]
  have hphase : W % v ≤ v - 1 := by have := Nat.mod_lt W hv; omega
  have hp : 2 ^ (W % v) ≤ 2 ^ (v - 1) := Nat.pow_le_pow_right (by decide) hphase
  have h : 2 ^ (W % v) * c (k - ((W / v : ℕ) : ZMod n)) ≤ 2 ^ (W % v) := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left (2 ^ (W % v)) (hc (k - ((W / v : ℕ) : ZMod n)))
  exact h.trans hp

/-- Every fractional phase is even, including the final half-radix phase. -/
theorem rotation_even {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (hphase : 0 < W % v)
    (k : ZMod n) : binaryRotation v W c k % 2 = 0 := by
  rw [rotation_eq_scaled hv W c hc]
  have he : W % v = (W % v - 1) + 1 := by omega
  rw [he, pow_succ]
  simp [Nat.mul_mod]

/-- At phase zero the temporal word is exactly the whole-cell permutation. -/
theorem rotation_zero_phase {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (hphase : W % v = 0)
    (k : ZMod n) :
    binaryRotation v W c k = c (k - ((W / v : ℕ) : ZMod n)) := by
  rw [rotation_eq_scaled hv W c hc, hphase, pow_zero, one_mul]

/-- The fixed origin bit appears at the actual shifted position and scale. -/
theorem rotation_origin_anchor {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (h0 : c 0 = 1) :
    binaryRotation v W c ((W / v : ℕ) : ZMod n) = 2 ^ (W % v) := by
  rw [rotation_eq_scaled hv W c hc, sub_self, h0, mul_one]

end DiophantineConsistency.NativeBooleanRotation
