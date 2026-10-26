import DiophantineConsistency.SplitCoefficientBounds

/-! Uncompiled candidate. This proves the replacement square argument against
the existing linear interface. The production patch moves that interface
earlier, preserving the existing import direction and old theorem name. -/

namespace ProofDelta.SquareCoefficient
open DiophantineConsistency
open Polynomial SelectiveQuadraticCoding
open scoped BigOperators

theorem square_bound {m : ℕ} (w : Fin (m + 1) → ℕ)
    (u : Fin (m + 1) → ℤ) (p : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hp : ∀ i, |p.coeff i| ≤ H) (n : ℕ) :
    |(encoded w u ^ 2 * p).coeff n| ≤ H * (∑ i, |u i|) ^ 2 := by
  have hs : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun i _ => abs_nonneg (u i)
  have hlinear := SplitCoefficientBounds.abs_coeff_linear_mul_le w u p H hH hp
  have htwice := SplitCoefficientBounds.abs_coeff_linear_mul_le w u
    (encoded w u * p) (H * ∑ i, |u i|) (mul_nonneg hH hs) hlinear n
  simpa only [pow_two, mul_assoc] using htwice

#print axioms square_bound
end ProofDelta.SquareCoefficient
