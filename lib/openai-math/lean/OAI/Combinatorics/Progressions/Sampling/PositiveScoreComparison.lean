import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

universe u

namespace Erdos3

open scoped BigOperators TensorProduct

theorem CyclicNiltestUpperComparison.of_positive_scores {degree N : ℕ} [NeZero N]
    {P epsilon : ℝ} {f g : ZMod N → ℝ}
    (h : ∀ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N P T →
      (𝔼 x, (f x - g x) * T x) ≤ epsilon) :
    CyclicNiltestUpperComparison.{u} degree N P epsilon f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  exact h (fun x => (T.evalCyclic N (fun _ => x)).re)
    (.of_test D hs T hT hTc (fun _ => rfl))

theorem exists_positive_score_of_not_upperComparison {degree N : ℕ} [NeZero N]
    {P epsilon : ℝ} {f g : ZMod N → ℝ}
    (h : ¬ CyclicNiltestUpperComparison.{u} degree N P epsilon f g) :
    ∃ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N P T ∧
      epsilon < 𝔼 x, (f x - g x) * T x := by
  by_contra hnone
  apply h
  apply CyclicNiltestUpperComparison.of_positive_scores
  intro T hT
  by_contra he
  exact hnone ⟨T, hT, lt_of_not_ge he⟩

theorem CyclicNiltestUpperComparison.normalize {degree N : ℕ} [NeZero N]
    {P epsilon alpha c : ℝ} {f : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N P epsilon f (fun _ => c * alpha))
    (halpha : 0 < alpha) :
    CyclicNiltestUpperComparison.{u} degree N P (epsilon / alpha)
      (fun x => f x / alpha) (fun _ => c) := by
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  have he (x : ZMod N) : (f x / alpha - c) * (T.evalCyclic N (fun _ => x)).re =
      ((f x - c * alpha) * (T.evalCyclic N (fun _ => x)).re) / alpha := by
    field_simp [halpha.ne']
  simp only [he, ← Finset.expect_div]
  exact div_le_div_of_nonneg_right (h D hs T hT hTc) halpha.le

end Erdos3

end

end OAI
