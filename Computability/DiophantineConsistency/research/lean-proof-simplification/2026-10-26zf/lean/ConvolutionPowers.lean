import DiophantineConsistency.SplitCoefficientBounds

/-!
Research candidate only. This file has NOT been compiled in this session.
The project pins Lean 4.32.0; replay in its normal dependency environment.
The minimal production patch uses only the square specialization. This
all-exponent extension is optional and has no claimed immediate net saving.
-/

namespace DiophantineConsistency.ConvolutionPowersCandidate

open Polynomial SelectiveQuadraticCoding
open scoped BigOperators

/-- Iterating the existing linear estimate avoids expanding a k-fold product. -/
theorem abs_coeff_pow_mul_le {m : ℕ} (w : Fin (m + 1) → ℕ)
    (u : Fin (m + 1) → ℤ) (p : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hp : ∀ i, |p.coeff i| ≤ H) (k n : ℕ) :
    |(encoded w u ^ k * p).coeff n| ≤ H * (∑ i, |u i|) ^ k := by
  have hs : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun i _ => abs_nonneg (u i)
  induction k generalizing n with
  | zero => simpa using hp n
  | succ k ih =>
      have hstep := SplitCoefficientBounds.abs_coeff_linear_mul_le w u
        (encoded w u ^ k * p) (H * (∑ i, |u i|) ^ k)
        (mul_nonneg hH (pow_nonneg hs k)) ih n
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hstep

#print axioms abs_coeff_pow_mul_le

end DiophantineConsistency.ConvolutionPowersCandidate
