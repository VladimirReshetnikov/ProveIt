import DiophantineConsistency.SelectiveQuadraticCoding
import Mathlib.Algebra.Polynomial.BigOperators

namespace DiophantineConsistency.SelectiveCarry
open Polynomial Finset
open SidonPositions (PairIndex)
open SelectiveQuadraticCoding
open scoped BigOperators

/-- The complete selective quadratic product. -/
noncomputable def rowProduct {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) (E : Fin r → ℕ) : ℤ[X] :=
  encoded w u ^ 2 * combined w s a E

theorem combined_degree_le {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (E : Fin r → ℕ) (D : ℕ)
    (hD : ∀ k p, p ∈ s k → E k - pairWeight w p ≤ D) :
    (combined w s a E).natDegree ≤ D := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [combined, complementary, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro p hp
  have hd := hD k p hp
  exact if_neg (by omega)

/-- Every coefficient outside the actual product span is zero. -/
theorem coeff_rowProduct_eq_zero {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) (E : Fin r → ℕ) (W D : ℕ)
    (hw : ∀ i, w i ≤ W)
    (hD : ∀ k p, p ∈ s k → E k - pairWeight w p ≤ D)
    {n : ℕ} (hn : D + 2 * W < n) : (rowProduct w s a u E).coeff n = 0 := by
  have he : (encoded w u).natDegree ≤ W := by
    unfold encoded
    exact natDegree_sum_le_of_forall_le _ _
      (fun i _ => (natDegree_monomial_le (u i)).trans (hw i))
  have hd := natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 he)
    (combined_degree_le w s a E D hD)
  apply coeff_eq_zero_of_natDegree_lt
  change (encoded w u ^ 2 * combined w s a E).natDegree < n
  omega

#print axioms coeff_rowProduct_eq_zero
end DiophantineConsistency.SelectiveCarry
