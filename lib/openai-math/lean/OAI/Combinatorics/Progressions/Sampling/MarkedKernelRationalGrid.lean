import OAI.Combinatorics.Progressions.Polynomial.ControlledPolynomialGroupMapBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

theorem exists_marked_kernel_rational_grid_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
        (l : ℕ), 0 < l →
      (by classical exact
        ((matrixDenominator (LinearMap.toMatrix c b S) * l : ℕ) : ℝ)) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (R : (F.realification.adaptedPolynomialFiltration w).Group)
          (RF : (G.realification.adaptedPolynomialFiltration w).Group),
          F.PolynomialRationalGrid b w l R → G.PolynomialRationalGrid c w l RF →
          F.PolynomialRationalGrid b w m
            ((F.filteredRealPolynomialSection G w S hS RF)⁻¹ * R) := by
  classical
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c ω hlayers w hw H p hH hp hι hσ hHp hb S hS l hl hlp
  let q := matrixDenominator (LinearMap.toMatrix c b S) * l
  have hq : 0 < q := Nat.mul_pos (matrixDenominator_pos _) hl
  have hlq : l ∣ q := dvd_mul_left _ _
  obtain ⟨m, hm, hmp, hqm, hmul⟩ :=
    hprod F b ω hlayers w hw H p hH hp hι hσ hHp hb q hq hlp
  refine ⟨m, hm, hmp, hlq.trans hqm, ?_⟩
  intro R RF hR hRF
  have hs := F.filteredRealPolynomialSection_rationalGrid G b c w S hS l RF hRF
  have hi := F.polynomialRationalGrid_inv b w q _ hs
  have hr := F.polynomialRationalGrid_of_dvd b w hl hlq R hR
  have hout := hmul [(F.filteredRealPolynomialSection G w S hS RF)⁻¹, R]
    (by simp) (by intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr';
                  rcases hr' with rfl | rfl; exact hi; exact hr)
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI
