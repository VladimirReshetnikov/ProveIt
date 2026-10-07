import OAI.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization

namespace OAI

section

namespace Erdos3

theorem kernel_normalization_parameter_le {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 2) ^ 4 :=
  le_power_budget hp (by decide)

theorem kernel_inclusion_height_mul_le_exp (n k H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((H ^ (n * k) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hH (n * k)
  rw [← Real.exp_nat_mul] at hpow
  have hprod : ((n * k : ℕ) : ℝ) * p ≤ (p + 2) ^ 3 := by
    rw [Nat.cast_mul, show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two]
    gcongr <;> linarith
  have hlog : ((n * k : ℕ) : ℝ) * p + p ≤ (p + 2) ^ 4 := by
    calc
      _ ≤ 2 * (p + 2) ^ 3 := by
        linarith [le_power_budget hp (by decide : 1 ≤ 3)]
      _ ≤ (p + 2) * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (((n * k : ℕ) : ℝ) * p) * Real.exp p :=
      mul_le_mul hpow hl (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((n * k : ℕ) : ℝ) * p + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem kernel_inclusion_denominator_mul_le_exp (n k H q l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hq : q ≤ H ^ (n * k))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((q * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hql : ((q * l : ℕ) : ℝ) ≤ ((H ^ (n * k) * l : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_right l hq)
  exact hql.trans (kernel_inclusion_height_mul_le_exp n k H l hp hn hk hH hl)

theorem kernel_coordinate_factor_le_exp (k H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hk : (k : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (k : ℝ) * H ≤ Real.exp ((p + 2) ^ 2) := by
  have hkexp : (k : ℝ) ≤ Real.exp p :=
    hk.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * Real.exp p :=
      mul_le_mul hkexp hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (p + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

theorem kernel_coordinate_succ_factor_le_exp (k H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hk : (k : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((k : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 2) := by
  have hkexp : (k : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hk (le_refl (1 : ℝ))).trans (Real.add_one_le_exp p)
  have hHexp : (H : ℝ) + 1 ≤ Real.exp (p + 1) := by
    have hone : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp p * 2 := by linarith
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hkexp hHexp (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 1)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

@[simp] theorem realPolynomialSymbolHom_constant (g : F.realification.Group) :
    F.realPolynomialSymbolHom b ω hF w
      (F.realification.adaptedConstantGroupHom w g) = 1 := by
  apply NilpotentLieBCHGroup.ext
  change F.realPolynomialSymbolMap b ω hF w _ = 0
  rw [F.realPolynomialSymbolMap_eq_zero_iff]
  exact F.realification.polynomialSymbolMap_constant w g.coord

theorem exists_marked_kernel_normalized_factors
    (H : Submodule ℚ L) (hH : F.layer 2 ≤ H)
    (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
    (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
    (hp : realificationLieHom φ
      (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
        (H.map φ.toLinearMap).baseChange ℝ) :
    ∃ (a : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
      (c : LinearMap.ker φ.toLinearMap)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (bk.baseChange ℝ).repr a i ∧ (bk.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, bk.repr c i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w
        ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (c : L)⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
      F.realPolynomialGroupMap G φ hφ w p' = F.realPolynomialGroupMap G φ hφ w p ∧
      F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
      coefficients (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈ H.baseChange ℝ := by
  obtain ⟨a, c, ha, hc, hka, hkc, hmid⟩ :=
    F.exists_kernel_constant_factors G φ H hH bk
      (F.realification.adaptedPolynomialConstantHom w p)
      (by simpa only [F.realification.adaptedPolynomialConstantHom_coord] using hp)
  let ka : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩
  let kc : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (c : L)⟩
  let C := F.realification.adaptedConstantGroupHom w
  let p' := (C ka)⁻¹ * p * (C kc)⁻¹
  have hma : F.realPolynomialGroupMap G φ hφ w (C ka) = 1 := by
    rw [F.realPolynomialGroupMap_constant, hka, map_one]
  have hmc : F.realPolynomialGroupMap G φ hφ w (C kc) = 1 := by
    rw [F.realPolynomialGroupMap_constant, hkc, map_one]
  refine ⟨a, c, e * C ka, p', C kc * r, ha, hc, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · dsimp only [p']; group
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, mul_one]
  · simp only [p', map_mul, map_inv, C, F.realPolynomialSymbolHom_constant,
      inv_one, one_mul, mul_one]
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, one_mul]
  · rw [map_mul, hma, mul_one]
  · simp only [p', map_mul, map_inv, hma, hmc, inv_one, one_mul, mul_one]
  · rw [map_mul, hmc, one_mul]
  · rw [← F.realification.adaptedPolynomialConstantHom_coord]
    simpa only [p', map_mul, map_inv, C,
      F.realification.adaptedPolynomialConstantHom_constant] using hmid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_kernel_normalization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
        (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (S : Submodule ℚ L), F.layer 2 ≤ S →
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) e →
        F.PolynomialRationalGrid b w l r →
        realificationLieHom φ
          (coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
            (S.map φ.toLinearMap).baseChange ℝ →
        ∃ (u : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
          (v : LinearMap.ker φ.toLinearMap)
          (e' middle' r' : (F.realification.adaptedPolynomialFiltration w).Group),
          (∀ i, 0 ≤ (bk.baseChange ℝ).repr u i ∧ (bk.baseChange ℝ).repr u i < 1) ∧
          (∀ i, ∃ z : ℤ, bk.repr v i = z) ∧
          e' = e * F.realification.adaptedConstantGroupHom w
            ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ u⟩ ∧
          r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩ * r ∧
          e' * middle' * r' = e * middle * r ∧
          F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
          F.realPolynomialSymbolHom b ω hF w middle' =
            F.realPolynomialSymbolHom b ω hF w middle ∧
          F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
          F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
          F.realPolynomialGroupMap G φ hφ w middle' =
            F.realPolynomialGroupMap G φ hφ w middle ∧
          F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
          coefficients (middle'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
            S.baseChange ℝ ∧
          F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) e' ∧
          F.PolynomialRationalGrid b w m r' := by
  obtain ⟨ce, _, hslow⟩ := exists_polynomial_slow_product_bound s 1 2
  obtain ⟨cr, _, hrational⟩ := exists_polynomial_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ 4
  let B : Polynomial ℕ := (Q + Polynomial.C ce) ^ ce + (Q + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G φ hφ b ω hF w hw bk H l p hH hl hp
    hι hκ hσ hHp hlp hbracket hkernel
  obtain ⟨q, hq, hqbound, hkb, hkg⟩ := exists_basis_image_bounds_of_height b bk
    (LinearMap.ker φ.toLinearMap).subtype H hkernel
  let P : ℝ := (p + 2) ^ a + (p + 2) ^ 4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hp4 : p ≤ (p + 2) ^ 4 := by
    apply (show p ≤ p + 2 by linarith).trans
    simpa only [pow_one] using
      pow_le_pow_right₀ (show (1 : ℝ) ≤ p + 2 by linarith) (show 1 ≤ 4 by omega)
  have hpP : p ≤ P := hp4.trans (le_add_of_nonneg_left (by positivity))
  have hden : ((q * l : ℕ) : ℝ) ≤ Real.exp P :=
    (kernel_inclusion_denominator_mul_le_exp (Fintype.card ι) (Fintype.card κ)
      H q l hp hι hκ hHp hqbound hlp).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity)))
  have hbudgetP : (P + ce) ^ ce + (P + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, P, Polynomial.eval₂_pow] using hbudget p hp
  have heBudget : (P + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hbudgetP
  have hrBudget : (P + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hbudgetP
  obtain ⟨m, hm, hmp, hqlm, hprod⟩ := hrational F b ω hF w hw H P hH hP
    (hι.trans hpP) (hσ.trans hpP) (hHp.trans (Real.exp_le_exp.mpr hpP)) hbracket
    (q * l) (Nat.mul_pos hq hl) hden
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrBudget),
    (dvd_mul_left l q).trans hqlm, ?_⟩
  intro S hS T hT e middle r he hr hmiddle
  obtain ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hmarkE, hmarkP, hmarkR, hconstant⟩ :=
    F.exists_marked_kernel_normalized_factors G φ hφ b ω hF w S hS bk
      e middle r hmiddle
  refine ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hmarkE, hmarkP, hmarkR, hconstant, ?_, ?_⟩
  · let ku : F.realification.Group :=
      ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ u⟩
    have hku : ∀ i, |(b.baseChange ℝ).repr ku.coord i| ≤ Real.exp (P + 2) := by
      intro i
      have hcoord := scalarExtension_fractional_coordinates_bound b bk
        (LinearMap.ker φ.toLinearMap).subtype H hkb u hu i
      have hfactor := kernel_coordinate_factor_le_exp (Fintype.card κ) H hp hκ hHp
      have h24 : (p + 2) ^ 2 ≤ (p + 2) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by omega)
      exact hcoord.trans (hfactor.trans (Real.exp_le_exp.mpr
        (h24.trans (by dsimp [P]; have := pow_nonneg (by linarith : 0 ≤ p + 2) a; linarith))))
    have hcs := F.polynomialSlowBound_constant b w T hT (Real.exp_nonneg _) ku hku
    have hes := F.polynomialSlowBound_mono b w T hT
      (Real.exp_le_exp.mpr (show (p + 2) ^ a ≤ P + 2 by
        dsimp [P]; have := pow_nonneg (by linarith : 0 ≤ p + 2) 4; linarith)) e he
    have hout := hslow F b ω hF w hw H P hH hP (hι.trans hpP) (hσ.trans hpP)
      (hHp.trans (Real.exp_le_exp.mpr hpP)) hbracket T hT
      [e, F.realification.adaptedConstantGroupHom w ku] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · simpa only [pow_one] using hes
        · simpa only [pow_one] using hcs)
    have hout' : F.PolynomialSlowBound b w T (Real.exp ((P + ce) ^ ce)) e' := by
      simpa only [List.prod_cons, List.prod_nil, mul_one, ← he', ku] using hout
    exact F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr heBudget) e' hout'
  · let kv : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩
    have hkv := integral_basis_image_realDenominatorGrid b bk
      (LinearMap.ker φ.toLinearMap).subtype q hkg v hv
    have hcs := F.polynomialRationalGrid_constant b w q kv hkv
    have hcs' := F.polynomialRationalGrid_of_dvd b w hq (dvd_mul_right q l) _ hcs
    have hrs := F.polynomialRationalGrid_of_dvd b w hl (dvd_mul_left l q) r hr
    have hout := hprod [F.realification.adaptedConstantGroupHom w kv, r] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hcs'
        · exact hrs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← hr', kv] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI
