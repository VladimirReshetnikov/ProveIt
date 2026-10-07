import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestDetection

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem exists_polynomial_box_detection.{u,v} (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p →
      (Fintype.card σ : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
      (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f T.eval‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f := by
  obtain ⟨c, _, hc⟩ := exists_boxNiltestDetection s
  let R := (Polynomial.X + P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hcorr
  let q := p + P.eval₂ (Nat.castRingHom ℝ) p
  have hP : 0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := natPolynomial_eval_nonneg P hp
  have hq : 0 ≤ q := add_nonneg hp hP
  have hPq : P.eval₂ (Nat.castRingHom ℝ) p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcorrq := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  have hn := hc D q hq (hσ.trans hPq) w hw T (hT.mono hPq) a lengths f hf hcorrq
  have hbudget : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hn

end Erdos3

end

end OAI
