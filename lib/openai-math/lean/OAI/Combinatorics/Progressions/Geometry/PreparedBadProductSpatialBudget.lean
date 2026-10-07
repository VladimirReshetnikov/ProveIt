import OAI.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedBadProductSpatialBudget (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ B : ℝ, 0 ≤ B →
      let P := (B + A) ^ A
      let Ps := (B + C) ^ C
      let Q := allocatedFourierLogBudget m P
      P ≤ Ps ∧ 2 * P + 7 * B + 24 ≤ Ps ∧
        allocatedMaskedFourierBudget m P ≤ Ps ∧
        (4 * Q + 2) ^ 4 ≤ Ps ∧ 4 * Q * (4 * Q + 2) ^ 4 + Q ≤ Ps := by
  obtain ⟨a, _, ha⟩ := exists_allocatedMaskedFourierBudget_bound m 2
  let p : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (2 * p + 7 * Polynomial.X + 24 + (p + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro B hB P Ps Q
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hF : 0 ≤ (P + a) ^ a := by positivity
  have htotal : 2 * P + 7 * B + 24 + (P + a) ^ a ≤ Ps := by
    simpa [p, P, Ps, Polynomial.eval₂_pow] using hbound B hB
  have hmask : allocatedMaskedFourierBudget m P ≤ Ps :=
    (ha P hP).1.trans (by linarith)
  have hcomponents := allocatedMaskedFourierBudget_bounds m hP
  exact ⟨by linarith, by linarith, hmask,
    hcomponents.2.2.1.trans hmask, hcomponents.2.2.2.trans hmask⟩

end Erdos3.VectorPolynomial

end

end OAI
