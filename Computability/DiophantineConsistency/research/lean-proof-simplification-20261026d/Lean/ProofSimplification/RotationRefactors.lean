import DiophantineConsistency.NativeCyclicRotation
import ProofSimplification.ArithmeticRefactors

/-!
Exact-statement alternatives to the existing half-radix bound and parity
theorems. Both use the general scaled quotient/remainder identity. They
retain the original hypotheses, including the absence of a NeZero n
assumption; no cyclic-word or consistency theorem is assumed here.
-/
namespace DiophantineConsistency.RotationRefactors
open NativeCyclicRotation ArithmeticRefactors

variable {n : Nat}

theorem shiftDigits_half_bound {s : ℕ} (hs : 0 < s) (c : ZMod n → ℕ)
    (hc : ∀ i, c i ≤ 3) (k : ZMod n) : shiftDigits (2 * s) s c k ≤ s + 1 := by
  exact scaled_half_bound s (c k) (c (k - 1)) hs (hc (k - 1))

theorem shiftDigits_half_parity_89 (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3)
    (k : ZMod n) : shiftDigits (2 ^ 89) (2 ^ 88) c k % 2 = c (k - 1) / 2 := by
  change (2 ^ 88 * c k % (2 * 2 ^ 88) +
    2 ^ 88 * c (k - 1) / (2 * 2 ^ 88)) % 2 = _
  exact scaled_half_parity (2 ^ 88) (c k) (c (k - 1))
    (by decide) (by decide) (hc (k - 1))

#print axioms shiftDigits_half_bound
#print axioms shiftDigits_half_parity_89

end DiophantineConsistency.RotationRefactors
