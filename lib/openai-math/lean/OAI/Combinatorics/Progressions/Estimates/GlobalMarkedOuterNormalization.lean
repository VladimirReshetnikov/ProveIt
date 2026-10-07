import OAI.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

structure GlobalMarkedNativeFactors
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w) where
  left : (F.realification.adaptedPolynomialFiltration w).Group
  middle : (F.realification.adaptedPolynomialFiltration w).Group
  right : (F.realification.adaptedPolynomialFiltration w).Group
  markedMiddle : (F.gradedRefiltration W).realification.PolynomialOrbit w
  product : left * middle * right = g
  left_symbol : F.realPolynomialSymbolHom b ω hF w left = E
  right_symbol : F.realPolynomialSymbolHom b ω hF w right = R
  constant_second : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
    F.realification.layer 2
  middle_log : VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
    markedMiddle.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
  (g : (F.realification.adaptedPolynomialFiltration w).Group)
  (E R : F.RealPolynomialSymbolGroup w)

theorem nonempty_globalMarkedNativeFactors [Fintype ι] (hw : ∀ i, 0 < w i)
    (hfast : (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    Nonempty (GlobalMarkedNativeFactors F b ω hF w W g E R) := by
  obtain ⟨a, v, e, middle, r, q, _, _, _, _, hprod, he, hr, hc, hq, _⟩ :=
    F.exists_global_native_factors_of_symbol b ω hF w hw W g E R hfast
  exact ⟨⟨e, middle, r, q, hprod, he, hr, hc, hq⟩⟩

namespace GlobalMarkedNativeFactors
variable {F b ω hF w W g E R}
  (A : GlobalMarkedNativeFactors F b ω hF w W g E R)

theorem middle_values (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t A.markedMiddle) =
        F.adaptedPolynomialRealValueHom w t A.middle :=
  F.native_refiltered_orbit_real_value W w A.markedMiddle _ A.middle_log t

theorem middle_coefficients_mem_first (α : σ →₀ ℕ) :
    coefficients (A.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer W 1 := by
  rw [← A.middle_log, coefficients_map]
  change realificationLieHom (F.gradedRefiltrationSubalgebra W).incl
    (coefficients A.markedMiddle.log α) ∈ _
  apply (F.mem_native_refiltration_layer W 1 _).mp
  rw [(F.gradedRefiltration W).realification.one_eq_top]
  trivial

theorem chart_coefficients_mem_first {τ : Type*} (β : σ → MvPolynomial τ ℝ)
    (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute β
      (A.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α ∈
      F.realGradedRefiltrationLayer W 1 := by
  rw [coefficients_realChartSubstitute]
  apply Submodule.sum_mem
  intro γ _
  exact Submodule.smul_mem _ _ (A.middle_coefficients_mem_first γ)

theorem product_values (t : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w t A.left *
        NilpotentLieBCHGroup.realificationMap
          (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
          ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t A.markedMiddle) *
        F.adaptedPolynomialRealValueHom w t A.right =
      F.adaptedPolynomialRealValueHom w t g := by
  rw [A.middle_values]
  simpa only [map_mul] using congrArg (F.adaptedPolynomialRealValueHom w t) A.product

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem exists_globalMarkedNativeFactors_of_outer_lifts [Fintype ι]
    (hw : ∀ i, 0 < w i)
    (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w)
    (he : F.realPolynomialSymbolHom b ω hF w e₀ = E)
    (hr : F.realPolynomialSymbolHom b ω hF w r₀ = R)
    (hfast : (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L) (A : GlobalMarkedNativeFactors F b ω hF w W g E R),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      A.left = e₀ * F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      A.right = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r₀ := by
  obtain ⟨a, v, e, middle, r, ha, hv, he', hr', hprod, hesym, hp, hrsym, hc⟩ :=
    F.exists_fractional_integral_polynomial_normalization b ω hF w
      e₀ (e₀⁻¹ * g * r₀⁻¹) r₀
  have hprod' : e * middle * r = g := hprod.trans (by group)
  have hpfast : (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) := by
    rw [hp, map_mul, map_mul, map_inv, map_inv, he, hr]
    exact hfast
  rw [F.realPolynomialSymbolHom_coord] at hpfast
  have hfirst := Submodule.baseChange_mono ℝ
    (F.layer_succ_le_gradedRefiltrationLayer W 1) hc
  obtain ⟨q, hq, _⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant W
    b ω hF w hw middle.coord hfirst
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mp hpfast)
  exact ⟨a, v, ⟨e, middle, r, q, hprod', hesym.trans he, hrsym.trans hr, hc, hq⟩,
    ha, hv, he', hr'⟩

theorem exists_controlled_globalMarkedNativeFactors (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ n ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
        (E R : F.RealPolynomialSymbolGroup w),
      F.realPolynomialSymbolHom b ω hF w e₀ = E →
      F.realPolynomialSymbolHom b ω hF w r₀ = R →
      (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) →
      F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) e₀ →
      F.PolynomialRationalGrid b w l r₀ →
      ∃ A : GlobalMarkedNativeFactors F b ω hF w W g E R,
        F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) A.left ∧
        F.PolynomialRationalGrid b w n A.right := by
  obtain ⟨C, hC, hnorm⟩ := exists_controlled_marked_target_normalization s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H l p hH hl hp hι hσ hHp hlp hbracket
  obtain ⟨n, hn, hnp, hln, hnormalize⟩ :=
    hnorm F b ω hF w hw H l p hH hl hp hι hσ hHp hlp hbracket
  refine ⟨n, hn, hnp, hln, ?_⟩
  intro T hT W g e₀ r₀ E R he hr hfast heBound hrGrid
  obtain ⟨u, v, e, middle, r, _, _, _, _, hprod, hesym, hp, hrsym, hc, heb, hrg⟩ :=
    hnormalize T hT e₀ (e₀⁻¹ * g * r₀⁻¹) r₀ heBound hrGrid
  have hprod' : e * middle * r = g := hprod.trans (by group)
  have hpfast : (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) := by
    rw [hp, map_mul, map_mul, map_inv, map_inv, he, hr]
    exact hfast
  rw [F.realPolynomialSymbolHom_coord] at hpfast
  have hfirst := Submodule.baseChange_mono ℝ
    (F.layer_succ_le_gradedRefiltrationLayer W 1) hc
  obtain ⟨q, hq, _⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant W
    b ω hF w hw middle.coord hfirst
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mp hpfast)
  exact ⟨⟨e, middle, r, q, hprod', hesym.trans he, hrsym.trans hr, hc, hq⟩, heb, hrg⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
