import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficient_inverse_product_le {n : ℕ} {a₀ b₀ κ C Q : ℝ}
    (a b : Fin n → ℝ) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) (hκ : 0 < κ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hlen₀ : a₀ ≤ C * b₀) (hlen : ∀ j, a j ≤ C * b j) (hQ : 0 ≤ Q) :
    Q / ((κ * b₀) * ∏ j, b j) ≤ Q * C ^ (n + 1) / ((κ * a₀) * ∏ j, a j) := by
  have hp := reciprocal_product_le_of_lengths (Fin.cons a₀ a) (Fin.cons b₀ b)
    (fun _ : Fin (n + 1) => C)
    (Fin.cases ha₀ ha) (Fin.cases hb₀ hb) (Fin.cases hlen₀ hlen) hQ
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hp
  calc
    _ = (Q / (b₀ * ∏ j, b j)) / κ := by ring
    _ ≤ (Q * C ^ (n + 1) / (a₀ * ∏ j, a j)) / κ :=
      div_le_div_of_nonneg_right hp hκ.le
    _ = _ := by ring

end Erdos3

end

end OAI
