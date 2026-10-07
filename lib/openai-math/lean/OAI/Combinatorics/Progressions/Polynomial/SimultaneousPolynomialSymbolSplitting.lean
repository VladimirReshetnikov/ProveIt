import OAI.Combinatorics.Progressions.Estimates.SimultaneousSymbolSplitting

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

@[simp] theorem realPolynomialSymbolLift_log (g : F.RealPolynomialSymbolGroup w) :
    ((F.realPolynomialSymbolLift b ω hlayers w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w g.coord := rfl

theorem exists_realPolynomial_symbol_factorization
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (h : E * P * R = F.realPolynomialSymbolHom b ω hlayers w g) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w E.coord ∧
      (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w R.coord ∧
      F.realPolynomialSymbolHom b ω hlayers w p = P := by
  let e := F.realPolynomialSymbolLift b ω hlayers w E
  let r := F.realPolynomialSymbolLift b ω hlayers w R
  refine ⟨e, e⁻¹ * g * r⁻¹, r, ?_, rfl, rfl, ?_⟩
  · simp [mul_assoc]
  · rw [map_mul, map_mul, map_inv, map_inv, ← h]
    simp [e, r, mul_assoc]

theorem exists_realPolynomial_controlled_symbol_factorization
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (h : E * P * R = F.realPolynomialSymbolHom b ω hlayers w g)
    (hE : F.SymbolSlowBound b ω hlayers w T M E)
    (hR : F.SymbolRationalGrid b ω hlayers w l R) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      F.realPolynomialSymbolHom b ω hlayers w p = P ∧
      (∀ α i, |(b.baseChange ℝ).repr
        (coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
          M / monomialScale T α) ∧
      ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
        (coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
          realDenominatorGrid l) ∧
      coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
      coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
      coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
        coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨e, p, r, hepr, he, hr, hp⟩ :=
    F.exists_realPolynomial_symbol_factorization b ω hlayers w g E P R h
  have he0 : coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
    rw [he]
    exact F.realSymbolRepresentative_constant b ω hlayers w E.coord
  have hr0 : coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
    rw [hr]
    exact F.realSymbolRepresentative_constant b ω hlayers w R.coord
  refine ⟨e, p, r, hepr, hp, ?_, ?_, he0, hr0,
    F.realification.polynomial_factor_middle_constant w g e p r hepr he0 hr0⟩
  · rw [he]
    exact F.realSymbolRepresentative_slow_coefficients b ω hlayers w T hT hM E hE
  · rw [hr]
    exact F.realSymbolRepresentative_rational_coefficients b ω hlayers w l R hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_simultaneous_polynomial_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (F.realPolynomialSymbolHom b ω hlayers w p₀).coord ∈
          realificationLieSubalgebra (⨅ j, U j) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
            realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨C, hC, hsplit⟩ := exists_simultaneous_symbol_splitting s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g E P R hX hP hE hR
  obtain ⟨m, E₀, P₀, R₀, hm, hmp, hlm, hprod, hmid, hslow, hrat⟩ :=
    hsplit F b ω hlayers w hw U v hspan hblock H l p hH hl hp
      hι hσ hκ hη hHp hlp hb hv T hT (F.realPolynomialSymbolHom b ω hlayers w g)
      E P R hX hP hE hR
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨e₀, p₀, r₀, hepr, hp₀, he, hr, he0, hr0, hp0⟩ :=
    F.exists_realPolynomial_controlled_symbol_factorization b ω hlayers w T hTpos
      (Real.exp_nonneg _) m g E₀ P₀ R₀ hprod hslow hrat
  refine ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, ?_, he, hr, he0, hr0, hp0⟩
  rw [hp₀]
  exact hmid

end Erdos3.NilpotentLieFiltration

end

end OAI
