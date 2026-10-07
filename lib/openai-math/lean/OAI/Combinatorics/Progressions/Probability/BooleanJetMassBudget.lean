import OAI.Combinatorics.Progressions.Polynomial.BooleanPolynomialBudget

namespace OAI

section

namespace Erdos3

noncomputable def booleanJetMassBudget (q h : ℕ) (W : ℝ) : ℝ :=
  (2 : ℝ) ^ q * (W * ((q : ℝ) + 1) ^ h)

theorem booleanJetMassBudget_nonneg (q h : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    0 ≤ booleanJetMassBudget q h W := by unfold booleanJetMassBudget; positivity

theorem booleanJetMassBudget_bound {α : Type*} [Fintype α] (s : Finset α)
    {h H : ℕ} (hh : h ≤ H) {w W : ℝ} (hw : 0 ≤ w) (hW : w ≤ W) :
    (2 : ℝ) ^ s.card * (w * ((Fintype.card α : ℝ) + 1) ^ h) ≤
      booleanJetMassBudget (Fintype.card α) H W := by
  have hb : (1 : ℝ) ≤ (Fintype.card α : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ s)
  · exact mul_le_mul hW (pow_le_pow_right₀ hb hh) (by positivity) (hw.trans hW)
  · positivity
  · positivity

end Erdos3

end

end OAI
