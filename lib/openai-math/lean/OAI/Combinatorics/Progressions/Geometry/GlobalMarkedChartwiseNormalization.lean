import OAI.Combinatorics.Progressions.Estimates.GlobalMarkedOuterNormalization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem weightedAdaptedRealChartHom_constant
    (w : σ → ℕ) (v : τ → ℕ) (γ : σ → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i)) (a : F.realification.Group) :
    F.weightedAdaptedRealChartHom w v γ hγ (F.realification.adaptedConstantGroupHom w a) =
      F.realification.adaptedConstantGroupHom v a := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.weightedAdaptedRealChartHom_coord, F.realification.adaptedConstantGroupHom_log,
    F.realification.adaptedConstantGroupHom_log]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  simp only [map_sub, eval₂_realChartSubstitute, VectorPolynomial.eval₂_monomial,
    Finsupp.prod_zero_index, one_smul, sub_self]

theorem exists_chartwise_controlled_globalMarkedNativeFactors (s a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + Cr) ^ Cr) ∧ l ∣ n ∧
      ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
        (E R : F.RealPolynomialSymbolGroup w),
      F.realPolynomialSymbolHom b ω hF w e₀ = E →
      F.realPolynomialSymbolHom b ω hF w r₀ = R →
      (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) →
      F.PolynomialRationalGrid b w l r₀ →
      ∃ A : GlobalMarkedNativeFactors F b ω hF w W g E R,
        F.PolynomialRationalGrid b w n A.right ∧
        ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
          (Fintype.card τ : ℝ) ≤ p →
          ∀ (γ : σ → MvPolynomial τ ℝ)
            (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
            (T : τ → ℝ), (∀ i, 0 < T i) →
          F.PolynomialSlowBound b v T (Real.exp ((p + 2) ^ a))
            (F.weightedAdaptedRealChartHom w v γ hγ e₀) →
          F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
            (F.weightedAdaptedRealChartHom w v γ hγ A.left) := by
  obtain ⟨Ce, hCe, hslow⟩ := exists_polynomial_slow_product_bound s a 2
  obtain ⟨Cr, hCr, hrat⟩ := exists_polynomial_rational_product_bound s 2
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H l p hH hl hp hι hσ hHp hlp hbracket
  obtain ⟨n, hn, hnp, hln, hproduct⟩ :=
    hrat F b ω hF w hw H p hH hp hι hσ hHp hbracket l hl hlp
  refine ⟨n, hn, hnp, hln, ?_⟩
  intro W g e₀ r₀ E R he hr hfast hrGrid
  obtain ⟨u, z, A, hu, hz, hleft, hright⟩ :=
    F.exists_globalMarkedNativeFactors_of_outer_lifts b ω hF w W hw g e₀ r₀ E R he hr hfast
  have hzGrid : (fun i => (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] z) i) ∈
      realDenominatorGrid 1 := by
    classical
    choose k hk using hz
    refine ⟨k, ?_⟩
    funext i
    change (k i : ℝ) = (1 : ℕ) * (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] z) i
    rw [Basis.baseChange_repr_tmul (S := ℝ), hk]
    simp only [Rat.smul_def, Rat.cast_intCast, mul_one, Nat.cast_one, one_mul]
  have hzPolynomial := F.polynomialRationalGrid_constant b w 1
    (⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩ : F.realification.Group) hzGrid
  have hzPolynomial' := F.polynomialRationalGrid_of_dvd b w
    (by decide : 0 < 1) (one_dvd l) _ hzPolynomial
  have hrFinal := hproduct
    [F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩, r₀] (by simp)
    (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hzPolynomial'
      · exact hrGrid)
  refine ⟨A, ?_, ?_⟩
  · simpa only [List.prod_cons, List.prod_nil, mul_one, ← hright] using hrFinal
  · intro τ _ v hv hτ γ hγ T hT heSlow
    have huBound : ∀ i, |(b.baseChange ℝ).repr u i| ≤ Real.exp ((p + 2) ^ a) := by
      intro i
      rw [abs_of_nonneg (hu i).1]
      exact (hu i).2.le.trans (Real.one_le_exp (by positivity))
    have huSlow := F.polynomialSlowBound_constant b v T hT (Real.exp_nonneg _)
      (⟨u⟩ : F.realification.Group) huBound
    have heFinal := hslow F b ω hF v hv H p hH hp hι hτ hHp hbracket T hT
      [F.weightedAdaptedRealChartHom w v γ hγ e₀,
        F.realification.adaptedConstantGroupHom v ⟨u⟩] (by simp)
      (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact heSlow
        · exact huSlow)
    rw [hleft, map_mul, F.weightedAdaptedRealChartHom_constant]
    simpa only [List.prod_cons, List.prod_nil, mul_one] using heFinal

end Erdos3.NilpotentLieFiltration

end

end OAI
