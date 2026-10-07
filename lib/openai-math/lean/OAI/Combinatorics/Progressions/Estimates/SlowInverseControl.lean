import OAI.Combinatorics.Progressions.Polynomial.PolynomialGridValues

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_slow_inverse_control (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
        D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) g →
        (∀ (v : σ → ℝ), (∀ i, |v i| ≤ T i) → ∀ i,
          |(D.basis.baseChange ℝ).repr (D.filtration.adaptedPolynomialRealValueHom w v g)⁻¹.coord i| ≤
            Real.exp ((p + 2) ^ C)) ∧
        (∀ (v z : σ → ℝ) (δ : ℝ), 0 ≤ δ →
          (∀ i, |v i| ≤ T i) → (∀ i, |z i| ≤ T i) →
          (∀ i, |v i - z i| ≤ T i * δ) →
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          dist (D.filtration.adaptedPolynomialRealValueHom w v g)⁻¹
            (D.filtration.adaptedPolynomialRealValueHom w z g)⁻¹ ≤
              Real.exp ((p + 2) ^ C) * δ) := by
  obtain ⟨A, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s r
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ T hT g hg
  have hinv := (D.filtration.polynomialSlowBound_inv_iff D.basis w T _ g).mpr hg
  have hsum : (s : ℝ) * (p + 1) + (p + 2) ^ r + (p + A) ^ A ≤ (p + 2) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hcoord : (s : ℝ) * (p + 1) + (p + 2) ^ r ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hdist : (p + A) ^ A ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  constructor
  · intro v hv i
    have hvbound := D.filtration.polynomialSlowBound_value D.basis w hw T hT
      (Real.exp_pos _).le g⁻¹ hinv v hv i
    rw [map_inv] at hvbound
    apply hvbound.trans
    have hn1 : (Fintype.card σ : ℝ) + 1 ≤ Real.exp p := by
      linarith [Real.add_one_le_exp p]
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (Real.add_one_le_exp (s : ℝ))
            (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          (Real.exp_pos _).le
      _ = Real.exp ((s : ℝ) * (p + 1) + (p + 2) ^ r) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hcoord
  · intro v z δ hδ hv hz hvz
    have hm := hmetric D w hw p hp hD hσ T hT g⁻¹ hinv v z δ hδ hv hz hvz
    simp only [map_inv] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hdist) hδ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
