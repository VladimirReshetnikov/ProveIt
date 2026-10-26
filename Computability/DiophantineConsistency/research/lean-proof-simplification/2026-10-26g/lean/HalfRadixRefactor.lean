import DiophantineConsistency.NativeCyclicRotation
import HalfRadixCore

/-! Same-signature replacement candidates for NativeCyclicRotation. -/
namespace DiophantineConsistency.RefactorHalfRadix

open NativeCyclicRotation

variable {n : ℕ}

theorem shiftDigits_half_bound {s : ℕ} (hs : 0 < s) (c : ZMod n → ℕ)
    (hc : ∀ i, c i ≤ 3) (k : ZMod n) : shiftDigits (2 * s) s c k ≤ s + 1 := by
  exact half_digit_le hs (c k) (c (k - 1)) (hc (k - 1))

theorem shiftDigits_half_parity_89 (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3)
    (k : ZMod n) : shiftDigits (2 ^ 89) (2 ^ 88) c k % 2 = c (k - 1) / 2 := by
  change shiftDigits (2 * 2 ^ 88) (2 ^ 88) c k % 2 = _
  exact half_digit_parity (by decide) (by decide) (c k) (c (k - 1)) (hc (k - 1))

#print axioms shiftDigits_half_bound
#print axioms shiftDigits_half_parity_89

end DiophantineConsistency.RefactorHalfRadix
