import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedRefinedData

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedChosenScaleBudget {A : Type*} [Semiring A]
    (m : ℕ) (p E T : A) : A :=
  allocatedPrimitiveNormalizedScaleLog m p E T + p + E + T

theorem allocatedChosenScaleBudget_bounds (m : ℕ) {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    let P := allocatedChosenScaleBudget m p E T
    0 ≤ P ∧ p ≤ P ∧ E ≤ P ∧ T ≤ P ∧ allocatedComparisonDimension m p ≤ P ∧
      allocatedPrimitiveNormalizedScaleLog m p E T ≤ P := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  obtain ⟨_, hQ, hDQ, _, _, hQL⟩ := allocatedNormalizedScaleBudget_bounds m hp hD hE hT
  have hL : 0 ≤ allocatedPrimitiveNormalizedScaleLog m p E T := hQ.trans hQL
  have hDL : allocatedComparisonDimension m p ≤ allocatedPrimitiveNormalizedScaleLog m p E T :=
    hDQ.trans hQL
  dsimp only [allocatedChosenScaleBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_allocatedChosenThreshold_bound (m A K : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E T : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ T →
      let P := allocatedChosenScaleBudget m p E T
      let V := (p + E + T + a) ^ a
      P ≤ V ∧ (P + A) ^ A ≤ V ∧ (P + p + E + K) ^ K ≤ V := by
  obtain ⟨b, _, hlog⟩ := exists_allocatedPrimitiveNormalizedScaleLog_bound m
  let H : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + Polynomial.X
  let poly : Polynomial ℕ := H + (H + Polynomial.C A) ^ A +
    (H + 2 * Polynomial.X + Polynomial.C K) ^ K + 1
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p E T hp hE hT
  let u := p + E + T
  let Hval := (u + b) ^ b + u
  let P := allocatedChosenScaleBudget m p E T
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hH : 0 ≤ Hval := by dsimp [Hval]; positivity
  have hP : 0 ≤ P := (allocatedChosenScaleBudget_bounds m hp hE hT).1
  have hPH : P ≤ Hval := by
    have h := hlog hp hE hT
    dsimp [P, allocatedChosenScaleBudget, Hval, u]
    linarith
  have hA : (P + A) ^ A ≤ (Hval + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (add_le_add hPH le_rfl) A
  have hK : (P + p + E + K) ^ K ≤ (Hval + 2 * u + K) ^ K := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [u] at *
    linarith
  have hbnd : Hval + (Hval + A) ^ A + (Hval + 2 * u + K) ^ K + 1 ≤ (u + a) ^ a := by
    simpa [poly, H, Hval, Polynomial.eval₂_pow] using hbound u hu
  have hA0 : 0 ≤ (Hval + A) ^ A := by positivity
  have hK0 : 0 ≤ (Hval + 2 * u + K) ^ K := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3.VectorPolynomial

end

end OAI
