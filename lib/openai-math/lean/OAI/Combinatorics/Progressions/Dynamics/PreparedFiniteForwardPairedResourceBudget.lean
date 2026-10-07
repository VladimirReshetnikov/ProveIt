import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardPairedResource_budget (Cdirect Cresource : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cresource) ^ Cresource ≤
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + (X + Polynomial.C Cdirect) ^ Cdirect +
    Polynomial.C Cresource) ^ Cresource
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog hx hg hs
  let t := preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
    preparedFiniteForwardWork A stageCountConstant n x
  have ht : 0 ≤ t := add_nonneg
    (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)
  have heq : preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cresource =
      t + (t + Cdirect) ^ Cdirect + Cresource := by
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    dsimp only [t]
    ring
  rw [heq]
  simpa [P, X, Polynomial.eval₂_pow, t] using hpoly t ht

end Erdos3.VectorPolynomial

end

end OAI
