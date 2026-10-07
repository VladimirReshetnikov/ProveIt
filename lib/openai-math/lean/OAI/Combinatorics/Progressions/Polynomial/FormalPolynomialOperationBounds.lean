import OAI.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
        A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
        ∀ M : ℝ, 0 ≤ M → ∀ Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L),
        Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T M Q →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) * M) (dualAdjoint A Q)) ∧
      (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
        A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
        ∀ i : σ, CoefficientBound (b.baseChange ℝ) T
          (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
          (formalLogDerivative i A)) := by
  obtain ⟨C, hC, hoperations⟩ := exists_scaled_polynomial_dual_bound s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT
  classical
  have hN : (1 : ℝ) ≤ Real.exp ((p + 2) ^ a) := Real.one_le_exp (by positivity)
  have hops := hoperations F b ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hc T hT
  constructor
  · intro A hA hAbound M hM Q hQ hQbound
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxbound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ a)) x := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT (Real.exp_nonneg _) x).mpr
      rwa [hx]
    have hybound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T M y := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT hM y).mpr
      rwa [hy]
    have hunit : ∀ z, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 z →
        F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C)) (dualAdjoint G z) := by
      intro z hz
      exact hops.2 G z hxbound (F.realAdaptedCoefficientBound_mono b ω hF _ T hT hN z hz)
    have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
        (Real.exp ((p + C) ^ C) * M) (dualAdjoint G y) :=
      weighted_linear_bound_of_unit
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
        (dualAdjointRealLinearEquiv G).toLinearMap _ hunit hM y hybound
    have hf := (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT
      (mul_nonneg (Real.exp_nonneg _) hM) _).mp hout
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hf
    exact hf
  · intro A hA hAbound i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxbound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ a)) x := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT (Real.exp_nonneg _) x).mpr
      rwa [hx]
    let Φ := dualRealLogarithmicDifferential
      (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot) x
    have hunit : ∀ y, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 y →
        F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C)) (Φ y) := by
      intro y hy
      have hy' := F.realAdaptedCoefficientBound_mono b ω hF _ T hT hN y hy
      change F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C))
        (dualLogDerivative ⟨dualConstantLie x + dualInfinitesimal y⟩)
      apply hops.1
      · simpa only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero] using hxbound
      · simpa only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add] using hy'
    have hderivative := F.realAdaptedDirectionalDerivative_single_bound b ω hF T hT
      (Real.exp_nonneg _) x hxbound i
    have hfactor : 0 ≤ (s : ℝ) * Real.exp ((p + 2) ^ a) / T i :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) (hT i).le
    have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
        (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
        (F.realAdaptedLogDerivative (Pi.single i 1) x) :=
      weighted_linear_bound_of_unit
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
        Φ _ hunit hfactor _ hderivative
    have hf := (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT
      (mul_nonneg (Real.exp_nonneg _) hfactor) _).mp hout
    rw [F.realAdaptedLogDerivative_eq_formal, hx] at hf
    exact hf

end Erdos3.NilpotentLieFiltration

end

end OAI
