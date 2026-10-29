import DiophantineConsistency.MFNativeBooleanRotation
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
      2 ^ (W % v) * c (k - ((W / v : ℕ) : ZMod n)) := MF.NativeBooleanRotation.rotation_eq_scaled hv W c hc k

/-- The half-radix bound includes phase v−1, with no extra carry unit. -/
theorem rotation_le_half {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (k : ZMod n) :
    binaryRotation v W c k ≤ 2 ^ (v - 1) := MF.NativeBooleanRotation.rotation_le_half hv W c hc k

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
    binaryRotation v W c k = c (k - ((W / v : ℕ) : ZMod n)) := MF.NativeBooleanRotation.rotation_zero_phase hv W c hc hphase k

/-- The fixed origin bit appears at the actual shifted position and scale. -/
theorem rotation_origin_anchor {v : ℕ} (hv : 0 < v) (W : ℕ)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (h0 : c 0 = 1) :
    binaryRotation v W c ((W / v : ℕ) : ZMod n) = 2 ^ (W % v) := by
  rw [rotation_eq_scaled hv W c hc, sub_self, h0, mul_one]

end DiophantineConsistency.NativeBooleanRotation
