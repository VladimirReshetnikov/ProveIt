import OAI.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialSlowBound_filteredRealPolynomialSection [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} (hA : 0 ≤ A)
    (hB : ∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤ B)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T A g) :
    F.PolynomialSlowBound b w T ((Fintype.card κ : ℝ) * B * A)
      (F.filteredRealPolynomialSection G w S hS g) := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients (map ((S.baseChange ℝ).restrictScalars ℚ)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) α) i| ≤ _
  rw [coefficients_map]
  exact (linearMap_abs_repr_le (c.baseChange ℝ) (b.baseChange ℝ) (S.baseChange ℝ)
    (div_nonneg hA (monomialScale_pos T hT α).le) hB _ (hg α) i).trans
    (le_of_eq (by ring))

theorem polynomialSlowBound_filteredRealPolynomialSection_rat [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} (hA : 0 ≤ A)
    (hB : ∀ i j, |(b.repr (S (c j)) i : ℝ)| ≤ B)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T A g) :
    F.PolynomialSlowBound b w T ((Fintype.card κ : ℝ) * B * A)
      (F.filteredRealPolynomialSection G w S hS g) :=
  F.polynomialSlowBound_filteredRealPolynomialSection G b c w S hS T hT hA
    (by simpa only [scalarExtension_basis_coordinates] using hB) g hg

private theorem section_exponential_budget (a : ℕ) {p n : ℝ} (hp : 0 ≤ p)
    (hnp : n ≤ p) :
    n * Real.exp ((p + 2) ^ a) * Real.exp ((p + 2) ^ a) ≤
      Real.exp ((p + 2) ^ (a + 2)) := by
  have hp1 : 1 ≤ p + 2 := by linarith
  have hq1 : 1 ≤ (p + 2) ^ a := one_le_pow₀ hp1
  have hnexp : n ≤ Real.exp p := hnp.trans (by linarith [Real.add_one_le_exp p])
  have hsmall : p + 2 * (p + 2) ^ a ≤ (p + 2) * (p + 2) ^ a := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq1)]
  have hlarge : (p + 2) * (p + 2) ^ a ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add, pow_two]
    nlinarith [mul_nonneg (show 0 ≤ (p + 2) ^ a by positivity)
      (show 0 ≤ (p + 2) * (p + 2) - (p + 2) by nlinarith)]
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ a) * Real.exp ((p + 2) ^ a) := by
      gcongr
    _ = Real.exp (p + 2 * (p + 2) ^ a) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (hsmall.trans hlarge)

theorem polynomialSlowBound_filteredRealPolynomialSection_exp [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (a : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hB : ∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤
      Real.exp ((p + 2) ^ a))
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) g) :
    F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2)))
      (F.filteredRealPolynomialSection G w S hS g) := by
  exact F.polynomialSlowBound_mono b w T hT
    (section_exponential_budget a hp hκ) _
    (F.polynomialSlowBound_filteredRealPolynomialSection G b c w S hS T hT
      (Real.exp_nonneg _) hB g hg)

theorem exists_marked_polynomial_kernel_slow_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j),
      (∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤
        Real.exp ((p + 2) ^ a)) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ (E : (F.realification.adaptedPolynomialFiltration w).Group)
        (EF : (G.realification.adaptedPolynomialFiltration w).Group),
      F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) E →
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
        (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹) ∧
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
        ((F.filteredRealPolynomialSection G w S hS EF)⁻¹ * E) := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s (a + 2) 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c ω hF w hw H p hH hp hι hκ hσ hHp hb
    S hS hB T hT E EF hE hEF
  let V := F.filteredRealPolynomialSection G w S hS EF
  have hV : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2))) V :=
    F.polynomialSlowBound_filteredRealPolynomialSection_exp G b c w S hS T hT a p hp hκ hB EF hEF
  have hVi := (F.polynomialSlowBound_inv_iff b w T _ V).mpr hV
  have hE' : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2))) E :=
    F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by omega : a ≤ a + 2))) E hE
  have hleft := hprod F b ω hF w hw H p hH hp hι hσ hHp hb T hT [E, V⁻¹]
    (by simp) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hE'
      · have heq := List.mem_singleton.mp hr
        simpa only [heq] using hVi)
  have hright := hprod F b ω hF w hw H p hH hp hι hσ hHp hb T hT [V⁻¹, E]
    (by simp) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hVi
      · have heq := List.mem_singleton.mp hr
        simpa only [heq] using hE')
  exact ⟨by simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft,
    by simpa only [List.prod_cons, List.prod_nil, mul_one] using hright⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
