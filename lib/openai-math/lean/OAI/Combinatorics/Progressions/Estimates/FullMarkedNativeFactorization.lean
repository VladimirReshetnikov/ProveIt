import OAI.Combinatorics.Progressions.Linear.ControlledMarkedKernelNormalization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ξ L M : Type*} [Fintype ξ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include c τ hG hw

theorem exists_marked_refiltered_factors
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
    (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
    (hP : ∀ z : σ → ℝ, eval₂ z (F.realGradedSymbolPolynomial b ω hF w
      (F.realPolynomialSymbolMap b ω hF w p.coord)) ∈ realificationLieSubalgebra U)
    (hconstant : realificationLieHom φ
      (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1) :
    ∃ (a : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
      (v : LinearMap.ker φ.toLinearMap)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      (∀ i, 0 ≤ (bk.baseChange ℝ).repr a i ∧ (bk.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, bk.repr v i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w
        ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
      F.realPolynomialGroupMap G φ hφ w p' = F.realPolynomialGroupMap G φ hφ w p ∧
      F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
          F.adaptedPolynomialRealValueHom w z p' := by
  have hconst : realificationLieHom φ
      (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
        ((F.gradedRefiltrationLayer U 1).map φ.toLinearMap).baseChange ℝ := by
    rw [F.gradedRefiltrationLayer_map G b ω hF c τ hG φ hφ U hU hsurj]
    exact hconstant
  obtain ⟨a, v, e', p', r', ha, hv, he', hr', hprod, hEs, hPs, hRs, heF, hpF, hrF, hp0⟩ :=
    F.exists_marked_kernel_normalized_factors G φ hφ b ω hF w
      (F.gradedRefiltrationLayer U 1) (F.layer_succ_le_gradedRefiltrationLayer U 1)
      bk e p r hconst
  have hP' : ∀ z : σ → ℝ, eval₂ z (F.realGradedSymbolPolynomial b ω hF w
      (F.realPolynomialSymbolMap b ω hF w p'.coord)) ∈ realificationLieSubalgebra U := by
    have hs := congrArg NilpotentLieBCHGroup.coord hPs
    change F.realPolynomialSymbolMap b ω hF w p'.coord =
      F.realPolynomialSymbolMap b ω hF w p.coord at hs
    intro z
    rw [hs]
    exact hP z
  obtain ⟨q, hq, hvalues⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant U
    b ω hF w hw p'.coord hp0 hP'
  exact ⟨a, v, e', p', r', q, ha, hv, he', hr', hprod, hEs, hPs, hRs,
    heF, hpF, hrF, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

theorem exists_fractional_integral_constant_normalization (g : F.realification.Group) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      ((⟨a⟩ : F.realification.Group)⁻¹ * g *
        (⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ : F.realification.Group)⁻¹).coord ∈ F.realification.layer 2 := by
  obtain ⟨a, v, hav, ha, hv⟩ := realification_fractional_integer_split b g.coord
  refine ⟨a, v, ha, hv, ?_⟩
  have h := F.realification.bch_triple_sub_sum_mem_next_layer 1 (-a) g.coord
    (-(1 : ℝ) ⊗ₜ[ℚ] v)
    (by rw [F.realification.one_eq_top]; trivial)
    (by rw [F.realification.one_eq_top]; trivial)
  have hz : -a + g.coord + -(1 : ℝ) ⊗ₜ[ℚ] v = 0 := by rw [hav]; abel
  simpa only [hz, sub_zero, NilpotentLieBCHGroup.coord_mul,
    NilpotentLieBCHGroup.coord_inv] using h

theorem exists_fractional_integral_polynomial_normalization
    (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (e p r : (F.realification.adaptedPolynomialFiltration w).Group) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      coefficients (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈ F.realification.layer 2 := by
  obtain ⟨a, v, ha, hv, hmid⟩ := F.exists_fractional_integral_constant_normalization b
    (F.realification.adaptedPolynomialConstantHom w p)
  let C := F.realification.adaptedConstantGroupHom w
  let ka : F.realification.Group := ⟨a⟩
  let kr : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩
  let p' := (C ka)⁻¹ * p * (C kr)⁻¹
  refine ⟨a, v, e * C ka, p', C kr * r, ha, hv, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p']; group
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, mul_one]
  · simp only [p', map_mul, map_inv, C, F.realPolynomialSymbolHom_constant,
      inv_one, one_mul, mul_one]
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, one_mul]
  · rw [← F.realification.adaptedPolynomialConstantHom_coord]
    simpa only [p', map_mul, map_inv, C,
      F.realification.adaptedPolynomialConstantHom_constant] using hmid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw

theorem exists_prescribed_native_refiltered_factorization
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (hprod : E * P * R = F.realPolynomialSymbolHom b ω hF w g)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U))
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (hleft : ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
      G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))))
    (hright : (G.realPolynomialSymbolHom c τ hG w RF *
      (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))))
    (hconstant : coefficients
      ((EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1) :
    ∃ (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * p * r = g ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w p =
        EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
          F.adaptedPolynomialRealValueHom w z p := by
  let : Fintype (SymbolBasisIndex w τ) :=
    symbolBasisIndexFintype w τ s hw (G.adaptedBasis_weight_le_step c τ hG)
  have himage := F.symbolPointwiseSubalgebra_map G b ω hF c τ hG φ hφ w U hU
  rw [← himage] at hleft hright
  obtain ⟨e, p, r, hepr, hp, heF, hrF, hpF⟩ :=
    F.exists_prescribed_fast_polynomial_factorization G φ hφ w b ω hF c τ hG hsurj
      (F.symbolPointwiseSubalgebra b ω hF w U) g E P R hprod hP EF RF hleft hright
  have hpvalues := (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U
    (F.realPolynomialSymbolHom b ω hF w p).coord).mp hp
  have hpc : realificationLieHom φ
      (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 := by
    have hlog := congrArg (fun z => coefficients
      (z.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0) hpF
    rw [F.realPolynomialGroupMap_log, coefficients_map] at hlog
    change realificationLieHom φ (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) = _ at hlog
    rw [hlog]
    exact hconstant
  obtain ⟨a, v, e', p', r', q, _, _, _, _, hepr', _, _, _, heF', hpF', hrF', hq, hvalues⟩ :=
    F.exists_marked_refiltered_factors G φ hφ b ω hF c τ hG w hw U hU hsurj bk
      e p r hpvalues hpc
  exact ⟨e', p', r', q, hepr'.trans hepr, heF'.trans heF, hrF'.trans hrF,
    hpF'.trans hpF, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_target_normalization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) e →
        F.PolynomialRationalGrid b w l r →
        ∃ (u : ℝ ⊗[ℚ] L) (v : L)
          (e' middle' r' : (F.realification.adaptedPolynomialFiltration w).Group),
          (∀ i, 0 ≤ (b.baseChange ℝ).repr u i ∧ (b.baseChange ℝ).repr u i < 1) ∧
          (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
          e' = e * F.realification.adaptedConstantGroupHom w ⟨u⟩ ∧
          r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r ∧
          e' * middle' * r' = e * middle * r ∧
          F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
          F.realPolynomialSymbolHom b ω hF w middle' =
            F.realPolynomialSymbolHom b ω hF w middle ∧
          F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
          coefficients (middle'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
            F.realification.layer 2 ∧
          F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) e' ∧
          F.PolynomialRationalGrid b w m r' := by
  obtain ⟨ce, _, hslow⟩ := exists_polynomial_slow_product_bound s a 2
  obtain ⟨cr, _, hrational⟩ := exists_polynomial_rational_product_bound s 2
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C ce) ^ ce +
    (Polynomial.X + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H l p hH hl hp hι hσ hHp hlp hbracket
  have hbound : (p + ce) ^ ce + (p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have heBudget : (p + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hbound
  have hrBudget : (p + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hbound
  obtain ⟨m, hm, hmp, hlm, hprod⟩ :=
    hrational F b ω hF w hw H p hH hp hι hσ hHp hbracket l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrBudget), hlm, ?_⟩
  intro T hT e middle r he hr
  obtain ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR, hconstant⟩ :=
    F.exists_fractional_integral_polynomial_normalization b ω hF w e middle r
  refine ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hconstant, ?_, ?_⟩
  · let ku : F.realification.Group := ⟨u⟩
    have hku : ∀ i, |(b.baseChange ℝ).repr ku.coord i| ≤ Real.exp ((p + 2) ^ a) := by
      intro i
      rw [abs_of_nonneg (hu i).1]
      exact (hu i).2.le.trans (Real.one_le_exp (by positivity))
    have hcs := F.polynomialSlowBound_constant b w T hT (Real.exp_nonneg _) ku hku
    have hout := hslow F b ω hF w hw H p hH hp hι hσ hHp hbracket T hT
      [e, F.realification.adaptedConstantGroupHom w ku] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact he
        · exact hcs)
    have hout' : F.PolynomialSlowBound b w T (Real.exp ((p + ce) ^ ce)) e' := by
      simpa only [List.prod_cons, List.prod_nil, mul_one, ← he', ku] using hout
    exact F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr heBudget) e' hout'
  · let kv : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩
    have hkv : (fun i => (b.baseChange ℝ).repr kv.coord i) ∈ realDenominatorGrid 1 := by
      classical
      choose z hz using hv
      refine ⟨z, ?_⟩
      funext i
      change (z i : ℝ) = (1 : ℕ) * (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] v) i
      rw [Basis.baseChange_repr_tmul (S := ℝ), hz]
      simp only [Rat.smul_def, Rat.cast_intCast, mul_one, Nat.cast_one, one_mul]
    have hcs := F.polynomialRationalGrid_constant b w 1 kv hkv
    have hcs' := F.polynomialRationalGrid_of_dvd b w (by decide : 0 < 1) (one_dvd l) _ hcs
    have hout := hprod [F.realification.adaptedConstantGroupHom w kv, r] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hcs'
        · exact hr)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← hr', kv] using hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw

theorem exists_full_marked_native_factorization
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (hprod : E * P * R = F.realPolynomialSymbolHom b ω hF w g)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U))
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (hleft : ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
      G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))))
    (hright : (G.realPolynomialSymbolHom c τ hG w RF *
      (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ)))) :
    ∃ (a : ℝ ⊗[ℚ] M) (v : M)
      (EF' RF' : (G.realification.adaptedPolynomialFiltration w).Group)
      (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      (∀ i, 0 ≤ (c.baseChange ℝ).repr a i ∧ (c.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, c.repr v i = z) ∧
      EF' = EF * G.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      RF' = G.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * RF ∧
      G.realPolynomialSymbolHom c τ hG w EF' = G.realPolynomialSymbolHom c τ hG w EF ∧
      G.realPolynomialSymbolHom c τ hG w RF' = G.realPolynomialSymbolHom c τ hG w RF ∧
      e * p * r = g ∧
      F.realPolynomialGroupMap G φ hφ w e = EF' ∧
      F.realPolynomialGroupMap G φ hφ w r = RF' ∧
      F.realPolynomialGroupMap G φ hφ w p =
        EF'⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF'⁻¹ ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
          F.adaptedPolynomialRealValueHom w z p := by
  let mg := F.realPolynomialGroupMap G φ hφ w g
  obtain ⟨a, v, EF', PH', RF', ha, hv, hEF, hRF, hmarkedProd, hESym, _, hRSym, hsecond⟩ :=
    G.exists_fractional_integral_polynomial_normalization c τ hG w
      EF (EF⁻¹ * mg * RF⁻¹) RF
  have hmarkedProd' : EF' * PH' * RF' = mg := hmarkedProd.trans (by group)
  have hmiddle : PH' = EF'⁻¹ * mg * RF'⁻¹ := by
    calc
      PH' = EF'⁻¹ * (EF' * PH' * RF') * RF'⁻¹ := by group
      _ = _ := by rw [hmarkedProd']
  have hfirst : coefficients (PH'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 :=
    Submodule.baseChange_mono ℝ
      (G.layer_succ_le_gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1) hsecond
  rw [hmiddle] at hfirst
  have hleft' : ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
      G.realPolynomialSymbolHom c τ hG w EF').coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [hESym] using hleft
  have hright' : (G.realPolynomialSymbolHom c τ hG w RF' *
      (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [hRSym] using hright
  obtain ⟨e, p, r, q, hprod', he, hr, hp, hq, hvalues⟩ :=
    F.exists_prescribed_native_refiltered_factorization G φ hφ b ω hF c τ hG w hw
      U hU hsurj bk g E P R hprod hP EF' RF' hleft' hright' hfirst
  exact ⟨a, v, EF', RF', e, p, r, q, ha, hv, hEF, hRF, hESym, hRSym,
    hprod', he, hr, hp, hq, hvalues⟩

theorem exists_fixed_marked_native_factorizations
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
    (X EF RF : (G.realification.adaptedPolynomialFiltration w).Group) :
    ∃ (a : ℝ ⊗[ℚ] M) (v : M)
      (EF' RF' : (G.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (c.baseChange ℝ).repr a i ∧ (c.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, c.repr v i = z) ∧
      EF' = EF * G.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      RF' = G.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * RF ∧
      G.realPolynomialSymbolHom c τ hG w EF' = G.realPolynomialSymbolHom c τ hG w EF ∧
      G.realPolynomialSymbolHom c τ hG w RF' = G.realPolynomialSymbolHom c τ hG w RF ∧
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group),
        F.realPolynomialGroupMap G φ hφ w g = X →
        ∀ (E P R : F.RealPolynomialSymbolGroup w),
          E * P * R = F.realPolynomialSymbolHom b ω hF w g →
          P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
          ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
            G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
              (G.symbolPointwiseSubalgebra c τ hG w
                (U.map (F.associatedGradedMap G φ hφ))) →
          (G.realPolynomialSymbolHom c τ hG w RF *
            (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
              (G.symbolPointwiseSubalgebra c τ hG w
                (U.map (F.associatedGradedMap G φ hφ))) →
          ∃ (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
            (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
            e * p * r = g ∧
            F.realPolynomialGroupMap G φ hφ w e = EF' ∧
            F.realPolynomialGroupMap G φ hφ w r = RF' ∧
            F.realPolynomialGroupMap G φ hφ w p = EF'⁻¹ * X * RF'⁻¹ ∧
            VectorPolynomial.map
              (realLieHomToRat (realificationLieHom
                (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap q.log =
              (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
            ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
              (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
              (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
              ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
                F.adaptedPolynomialRealValueHom w z p := by
  obtain ⟨a, v, EF', PH', RF', ha, hv, hEF, hRF, hmarkedProd, hESym, _, hRSym, hsecond⟩ :=
    G.exists_fractional_integral_polynomial_normalization c τ hG w
      EF (EF⁻¹ * X * RF⁻¹) RF
  have hmarkedProd' : EF' * PH' * RF' = X := hmarkedProd.trans (by group)
  have hmiddle : PH' = EF'⁻¹ * X * RF'⁻¹ := by
    calc
      PH' = EF'⁻¹ * (EF' * PH' * RF') * RF'⁻¹ := by group
      _ = _ := by rw [hmarkedProd']
  have hfirst : coefficients (PH'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 :=
    Submodule.baseChange_mono ℝ
      (G.layer_succ_le_gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1) hsecond
  rw [hmiddle] at hfirst
  refine ⟨a, v, EF', RF', ha, hv, hEF, hRF, hESym, hRSym, ?_⟩
  intro g hg E P R hprod hP hleft hright
  have hleft' : ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
      G.realPolynomialSymbolHom c τ hG w EF').coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [hESym] using hleft
  have hright' : (G.realPolynomialSymbolHom c τ hG w RF' *
      (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [hRSym] using hright
  have hconstant : coefficients
      ((EF'⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF'⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 := by
    simpa only [hg] using hfirst
  obtain ⟨e, p, r, q, hprod', he, hr, hp, hq, hvalues⟩ :=
    F.exists_prescribed_native_refiltered_factorization G φ hφ b ω hF c τ hG w hw
      U hU hsurj bk g E P R hprod hP EF' RF' hleft' hright' hconstant
  exact ⟨e, p, r, q, hprod', he, hr, hp.trans (by rw [hg]), hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
