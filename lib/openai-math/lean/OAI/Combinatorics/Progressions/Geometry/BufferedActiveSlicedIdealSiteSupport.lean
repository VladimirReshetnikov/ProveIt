import OAI.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_supported_buffered_active_sliced_ideal_site_approximation
    {D G Z α U : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    [PseudoMetricSpace U] {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ * L + C) (f k s)) ∧
        (∀ k s u, χ s u = 0 → f k s u = 0) ∧
        ∀ u : Finset α → U,
          ‖(∏ s, χ s (u s)) * (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
              (booleanSiteJets sets (fun s d => y s (u s) d.val)) : ℂ) -
            ∑ k, a k * ∏ s, f k s (u s)‖ ≤ ε := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ :=
    exists_active_sliced_ideal_site_approximation (G := G) (Z := Z) (B := B) h P sets center width δ hδ hR hε hp hRp hεp hδp
  dsimp only
  refine ⟨n, hn, a, bufferedSiteFactor y χ f, ha, ?_, ?_, ?_, ?_⟩
  · exact bufferedSiteFactor_bound y χ f hχ1 hf
  · exact bufferedSiteFactor_lipschitz y χ f hy hχ hLip hχ1 hf
  · intro k s u hu
    simp only [bufferedSiteFactor, hu, zero_mul]
  · intro u
    exact bufferedSiteExpansion_error y χ
      (activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ)
      a f hε.le hχ1 hsupport herr u

end Erdos3

end

end OAI
