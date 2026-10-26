import DiophantineConsistency.SelectiveCoefficientBounds

namespace ProofSimplification.CoefficientAction

open Polynomial Finset
open DiophantineConsistency.SelectiveQuadraticCoding
open DiophantineConsistency.SelectiveCoefficientBounds
open scoped BigOperators

theorem abs_coeff_encoded_mul_le {m : ℕ} (w : Fin (m + 1) → ℕ)
    (y : Fin (m + 1) → ℤ) (D : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hD : ∀ i, |D.coeff i| ≤ H) (n : ℕ) :
    |(encoded w y * D).coeff n| ≤ H * ∑ i, |y i| := by
  classical
  rw [encoded]
  simp only [Finset.sum_mul, finsetSum_coeff]
  calc
    |∑ i, (monomial (w i) (y i) * D).coeff n| ≤
        ∑ i, |(monomial (w i) (y i) * D).coeff n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |y i| * H := Finset.sum_le_sum fun i _ =>
      abs_coeff_monomial_mul_le D H hH hD (w i) n (y i)
    _ = H * ∑ i, |y i| := by rw [← Finset.sum_mul]; ring

theorem square_via_action {m : ℕ} (w : Fin (m + 1) → ℕ)
    (u : Fin (m + 1) → ℤ) (p : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hp : ∀ i, |p.coeff i| ≤ H) (n : ℕ) :
    |(encoded w u ^ 2 * p).coeff n| ≤ H * (∑ i, |u i|) ^ 2 := by
  have hsum : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hlinear := abs_coeff_encoded_mul_le w u p H hH hp
  have h := abs_coeff_encoded_mul_le w u (encoded w u * p)
    (H * ∑ i, |u i|) (mul_nonneg hH hsum) hlinear n
  simpa only [pow_two, mul_assoc] using h

#print axioms abs_coeff_encoded_mul_le
#print axioms square_via_action

end ProofSimplification.CoefficientAction
