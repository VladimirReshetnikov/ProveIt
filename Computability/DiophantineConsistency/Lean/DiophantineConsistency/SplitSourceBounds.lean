import DiophantineConsistency.SplitCoefficientBounds
import DiophantineConsistency.SplitWordBounds

/-! # Degree bounds for a split source polynomial -/

namespace DiophantineConsistency.SplitSourceBounds

open Polynomial Finset
open SelectiveQuadraticCoding
open scoped BigOperators

/-- A finite encoded word has degree at most its largest permitted position. -/
theorem encoded_natDegree_le {m W : ℕ} (w : Fin (m+1) → ℕ)
    (hw : ∀ i,w i≤W) (y : Fin (m+1) → ℤ) : (encoded w y).natDegree≤W := by
  classical
  unfold encoded
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le (y i)).trans (hw i)

/-- Degree bookkeeping for all three channels, without nonzero hypotheses. -/
theorem product_natDegree_le {m W d0 d1 d2 : ℕ} (w : Fin (m+1) → ℕ)
    (hw : ∀ i,w i≤W) (y : Fin (m+1) → ℤ) (D0 D1 D2 : ℤ[X])
    (h0 : D0.natDegree≤d0) (h1 : D1.natDegree≤d1) (h2 : D2.natDegree≤d2) :
    (SplitCoefficientBounds.product w y D0 D1 D2).natDegree≤
      max (max (2*W+d2) (W+d1)) d0 := by
  have he := encoded_natDegree_le w hw y
  unfold SplitCoefficientBounds.product
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 he) h2
    · exact natDegree_mul_le_of_le he h1
  · exact h0

/-- The split116 kernel bounds control every signed digit assignment. -/
theorem product_natDegree_le_2161 {m : ℕ} (w : Fin (m+1) → ℕ)
    (hw : ∀ i,w i≤116) (y : Fin (m+1) → ℤ) (D0 D1 D2 : ℤ[X]) {H : ℤ}
    (hk : SplitWordBounds.KernelBounds D0 D1 D2 H) :
    (SplitCoefficientBounds.product w y D0 D1 D2).natDegree≤2161 := by
  have h := product_natDegree_le w hw y D0 D1 D2 hk.degree_zero hk.degree_one hk.degree_two
  exact h

/-- This is the finite coefficient length required by the sparse decoder. -/
theorem product_natDegree_lt_2162 {m : ℕ} (w : Fin (m+1) → ℕ)
    (hw : ∀ i,w i≤116) (y : Fin (m+1) → ℤ) (D0 D1 D2 : ℤ[X]) {H : ℤ}
    (hk : SplitWordBounds.KernelBounds D0 D1 D2 H) :
    (SplitCoefficientBounds.product w y D0 D1 D2).natDegree<2162 := by
  have h := product_natDegree_le_2161 w hw y D0 D1 D2 hk
  omega

end DiophantineConsistency.SplitSourceBounds
