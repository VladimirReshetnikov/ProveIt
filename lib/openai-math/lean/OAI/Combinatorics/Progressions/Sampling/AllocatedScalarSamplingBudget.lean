import OAI.Combinatorics.Progressions.Fourier.AllocatedErrorFourierBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedScalarSamplingBudget (m dim A : ℕ) (P Perr : ℝ) : ℝ :=
  allocatedJetFourierBudget m dim A P + allocatedErrorFourierOutput m Perr

theorem allocatedScalarSamplingBudget_bounds (m dim A : ℕ) {P Perr : ℝ}
    (hP : 0 ≤ P) (hPerr : 0 ≤ Perr) :
    0 ≤ allocatedScalarSamplingBudget m dim A P Perr ∧
      allocatedJetFourierBudget m dim A P ≤ allocatedScalarSamplingBudget m dim A P Perr ∧
      allocatedErrorFourierOutput m Perr ≤ allocatedScalarSamplingBudget m dim A P Perr ∧
      Perr ≤ allocatedScalarSamplingBudget m dim A P Perr := by
  have hjet := allocatedJetFourierBudget_nonneg m dim A hP
  obtain ⟨_, _, _, _, herr, _, _⟩ := allocatedErrorFourier_budgets m hPerr
  have he := hPerr.trans herr
  unfold allocatedScalarSamplingBudget
  exact ⟨add_nonneg hjet he, le_add_of_nonneg_right he, le_add_of_nonneg_left hjet,
    herr.trans (le_add_of_nonneg_left hjet)⟩

theorem exists_allocatedScalarSamplingThreshold_bound (m dim A K : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P Perr p : ℝ}, 0 ≤ P → 0 ≤ Perr → P ≤ p → Perr ≤ p →
      (allocatedScalarSamplingBudget m dim A P Perr + K) ^ K ≤ (p + a) ^ a := by
  obtain ⟨b, _hb, hjet⟩ := exists_allocatedJetFourierBudget_bound m dim A
  obtain ⟨c, _hc, herr⟩ := exists_allocatedErrorFourierOutput_bound m
  let poly : Polynomial ℕ :=
    ((Polynomial.X + Polynomial.C b) ^ b + (Polynomial.X + Polynomial.C c) ^ c + Polynomial.C K) ^ K
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P Perr p hP hPerr hPp hPerrp
  have h1 : allocatedJetFourierBudget m dim A P ≤ (p + b) ^ b :=
    (hjet P hP).trans (pow_le_pow_left₀ (show 0 ≤ P + (b : ℝ) by positivity)
      (show P + (b : ℝ) ≤ p + b by linarith) b)
  have h2 : allocatedErrorFourierOutput m Perr ≤ (p + c) ^ c :=
    (herr Perr hPerr).trans (pow_le_pow_left₀ (show 0 ≤ Perr + (c : ℝ) by positivity)
      (show Perr + (c : ℝ) ≤ p + c by linarith) c)
  have hbudget := (allocatedScalarSamplingBudget_bounds m dim A hP hPerr).1
  calc
    _ ≤ ((p + b) ^ b + (p + c) ^ c + K) ^ K :=
      pow_le_pow_left₀ (add_nonneg hbudget (Nat.cast_nonneg K))
        (add_le_add (add_le_add h1 h2) le_rfl) _
    _ ≤ _ := by simpa [poly, Polynomial.eval₂_pow] using hbound p (hP.trans hPp)

end Erdos3.VectorPolynomial

end

end OAI
