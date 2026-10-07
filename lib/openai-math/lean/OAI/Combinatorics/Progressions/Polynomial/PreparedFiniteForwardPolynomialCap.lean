import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForward_polynomial_cap (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog : ℝ}, C ≤ A → 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      P.eval₂ (Nat.castRingHom ℝ)
        (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
          preparedFiniteForwardWork A stageCountConstant n x) ≤
        preparedFiniteForwardCap A stageCountConstant n x := by
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog hCA hx hg hs
  have hprec := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  exact (hpoly _ (add_nonneg hprec.2.1 hw)).trans
    (preparedFiniteForward_phase_cap A stageCountConstant n C hx hg hs hCA)

theorem exists_preparedFiniteForward_composed_phase_cap (Cnative Cmajor : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog pMajor : ℝ}, C ≤ A → 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → 0 ≤ pMajor →
      pMajor ≤ (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cnative) ^ Cnative →
      (pMajor + Cmajor) ^ Cmajor ≤ preparedFiniteForwardCap A stageCountConstant n x := by
  let P : Polynomial ℕ := ((Polynomial.X + Polynomial.C Cnative) ^ Cnative +
    Polynomial.C Cmajor) ^ Cmajor
  obtain ⟨C, hC, hpoly⟩ := exists_preparedFiniteForward_polynomial_cap P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog pMajor hCA hx hg hs hp hbound
  apply le_trans (pow_le_pow_left₀ (add_nonneg hp (Nat.cast_nonneg Cmajor))
    (add_le_add hbound (le_refl (Cmajor : ℝ))) Cmajor)
  simpa [P, Polynomial.eval₂_pow] using hpoly A stageCountConstant n hCA hx hg hs

end Erdos3.VectorPolynomial

end

end OAI
