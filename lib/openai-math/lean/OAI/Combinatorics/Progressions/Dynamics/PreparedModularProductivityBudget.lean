import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_preparedModularProductivity_budget (Aprod Cresource : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Pmaster Plate required : ℝ},
      0 ≤ Pmaster → 0 ≤ Plate →
      required ≤ (Pmaster + Plate + Cresource) ^ Cresource →
      max required ((4 * (Plate + 8) ^ 2 + Aprod) ^ Aprod) ≤
        (Pmaster + Plate + C) ^ C := by
  let cost : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C Cresource) ^ Cresource +
      (4 * (Polynomial.X + 8) ^ 2 + Polynomial.C Aprod) ^ Aprod
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget cost
  refine ⟨C, hC, ?_⟩
  intro Pmaster Plate required hP hL hrequired
  have h := hbudget (Pmaster + Plate) (add_nonneg hP hL)
  have hsum : (Pmaster + Plate + Cresource) ^ Cresource +
      (4 * (Pmaster + Plate + 8) ^ 2 + Aprod) ^ Aprod ≤
      (Pmaster + Plate + C) ^ C := by
    simpa [cost, Polynomial.eval₂_pow] using h
  have hprod : (4 * (Plate + 8) ^ 2 + Aprod) ^ Aprod ≤
      (4 * (Pmaster + Plate + 8) ^ 2 + Aprod) ^ Aprod := by
    gcongr
    linarith only [hP]
  have h0 : 0 ≤ (Pmaster + Plate + Cresource) ^ Cresource := by positivity
  have h1 : 0 ≤ (4 * (Pmaster + Plate + 8) ^ 2 + Aprod) ^ Aprod := by positivity
  exact max_le (by linarith) (by linarith)

end Erdos3

end

end OAI
