import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_native_slow_left_constant_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (weight : Fin d → ℕ)
      (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weight i}))
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ A : σ → ℝ, (∀ i, 0 < A i) → ∀ a : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
      ∀ e : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp p) e →
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp ((p + C) ^ C))
        (D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a * e) := by
  obtain ⟨c, _, hproduct⟩ := exists_polynomial_slow_product_bound s 1 2
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D weight hF p hp hD hσ A hA a ha e he
  have hbound : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  let cA := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a
  have hcA : D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp p) cA :=
    D.filtration.polynomialSlowBound_constant D.basis (fun _ => 1) A hA (Real.exp_nonneg p) a ha
  have hsmall : Real.exp p ≤ Real.exp ((p + 1 + 2) ^ (1 : ℕ)) :=
    Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)
  have hlist : ∀ r ∈ [cA, e], D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A
      (Real.exp ((p + 1 + 2) ^ (1 : ℕ))) r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA hsmall cA hcA
    · have hr' : r = e := List.mem_singleton.mp hr
      subst r
      exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA hsmall e he
  have hout := hproduct D.filtration D.basis weight hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) ⌈Real.exp p⌉₊ (p + 1) (one_le_ceil_exp p) (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (hσ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) A hA [cA, e]
    (by simp) hlist
  have hslow : D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A
      (Real.exp ((p + 1 + c) ^ c)) (cA * e) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hout
  exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA
    (Real.exp_le_exp.mpr hbound) (cA * e) hslow

end Erdos3

end

end OAI
