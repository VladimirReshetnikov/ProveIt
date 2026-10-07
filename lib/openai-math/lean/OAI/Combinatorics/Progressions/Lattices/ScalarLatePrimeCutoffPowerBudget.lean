import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

theorem exists_scalarLatePrimeCutoff_power_budget (d r E C F A : ℕ) :
    ∃ G : ℕ, 2 ≤ G ∧ ∀ b : ℝ, 0 ≤ b →
      let p := (b + 2) ^ E
      let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
      let t := (target + 2) ^ C
      (p + F) ^ F ≤ (b + 2) ^ G ∧ (t + 2) ^ A ≤ (b + 2) ^ G := by
  let Pscalar : Polynomial ℕ := ((Polynomial.X + 2) ^ E + Polynomial.C F) ^ F
  let Psample : Polynomial ℕ :=
    ((Polynomial.C (8 * (r * d + 1)) * ((Polynomial.X + 2) ^ E + 1) + 2) ^ C + 2) ^ A
  obtain ⟨G, hG, hbound⟩ := exists_natPolynomial_fixed_power_budget (Pscalar + Psample)
  refine ⟨G, hG, ?_⟩
  intro b hb p target t
  have hsum : (p + F) ^ F + (t + 2) ^ A ≤ (b + 2) ^ G := by
    simpa [Pscalar, Psample, p, target, t, Polynomial.eval₂_pow] using hbound b hb
  have hscalar : 0 ≤ (p + F) ^ F := by dsimp only [p]; positivity
  have hsample : 0 ≤ (t + 2) ^ A := by dsimp only [t, target, p]; positivity
  exact ⟨(le_add_of_nonneg_right hsample).trans hsum,
    (le_add_of_nonneg_left hscalar).trans hsum⟩

theorem exists_scalarLatePrimeCutoff_composite_power_budget (d r E C F A H : ℕ) :
    ∃ G : ℕ, 2 ≤ G ∧ ∀ p : ℝ, 2 ≤ p →
      let b := (p + 2) ^ H
      let scalarInput := (b + 2) ^ E
      let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (scalarInput + 1)
      let t := (target + 2) ^ C
      (scalarInput + F) ^ F ≤ (p + 2) ^ G ∧ (t + 2) ^ A ≤ (p + 2) ^ G := by
  obtain ⟨G, hG, hbudget⟩ := exists_scalarLatePrimeCutoff_power_budget d r E C F A
  refine ⟨(H + 1) * G, by nlinarith, ?_⟩
  intro p hp b scalarInput target t
  have hbase : 1 ≤ p + 2 := by linarith
  have hb : 1 ≤ b := one_le_pow₀ hbase
  have hshift : b + 2 ≤ (p + 2) ^ (H + 1) := by
    rw [pow_succ']
    change b + 2 ≤ (p + 2) * b
    nlinarith
  have hcompose : (b + 2) ^ G ≤ (p + 2) ^ ((H + 1) * G) := by
    calc
      _ ≤ ((p + 2) ^ (H + 1)) ^ G := pow_le_pow_left₀ (by linarith) hshift G
      _ = _ := (pow_mul _ _ _).symm
  have h := hbudget b (by linarith)
  exact ⟨h.1.trans hcompose, h.2.trans hcompose⟩

end Erdos3

end

end OAI
