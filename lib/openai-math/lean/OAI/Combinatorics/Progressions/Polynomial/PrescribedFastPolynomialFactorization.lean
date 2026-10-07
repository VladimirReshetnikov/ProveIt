import OAI.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
import OAI.Combinatorics.Progressions.Estimates.RealImageFactorCorrection
import OAI.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realPolynomialSymbolQuotientLinear :
    F.realification.PolynomialSymbol w →ₗ[ℚ] F.RealPolynomialSymbol w :=
  (F.realification.shiftedAdaptedIdeal w).toSubmodule.liftQ
    (F.realPolynomialSymbolMap b ω hlayers w).toLinearMap (by
      intro p hp
      apply (F.realPolynomialSymbolMap_eq_zero_iff b ω hlayers w p).mpr
      exact (F.realification.polynomialSymbolMap_eq_zero_iff w p).mpr hp)

@[simp] theorem realPolynomialSymbolQuotientLinear_map
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolQuotientLinear b ω hlayers w
      (F.realification.polynomialSymbolMap w p) = F.realPolynomialSymbolMap b ω hlayers w p := rfl

noncomputable def realPolynomialSymbolQuotientHom :
    F.realification.PolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := F.realPolynomialSymbolQuotientLinear b ω hlayers w
  map_lie' {x y} := by
    obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
    obtain ⟨q, rfl⟩ := F.realification.polynomialSymbolMap_surjective w y
    change F.realPolynomialSymbolQuotientLinear b ω hlayers w
      ⁅F.realification.polynomialSymbolMap w p, F.realification.polynomialSymbolMap w q⁆ = _
    rw [← LieHom.map_lie, F.realPolynomialSymbolQuotientLinear_map]
    exact (F.realPolynomialSymbolMap b ω hlayers w).map_lie p q

theorem realPolynomialSymbolQuotientHom_bijective :
    Function.Bijective (F.realPolynomialSymbolQuotientHom b ω hlayers w) := by
  constructor
  · intro x y hxy
    obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
    obtain ⟨q, rfl⟩ := F.realification.polynomialSymbolMap_surjective w y
    apply (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w p q).mp
    exact hxy
  · intro x
    obtain ⟨p, hp⟩ := F.realPolynomialSymbolMap_surjective b ω hlayers w x
    exact ⟨F.realification.polynomialSymbolMap w p, hp⟩

noncomputable def realPolynomialSymbolQuotientEquiv :
    F.realification.PolynomialSymbol w ≃ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieEquiv.ofBijective (F.realPolynomialSymbolQuotientHom b ω hlayers w)
    (F.realPolynomialSymbolQuotientHom_bijective b ω hlayers w)

@[simp] theorem realPolynomialSymbolQuotientEquiv_map
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolQuotientEquiv b ω hlayers w
      (F.realification.polynomialSymbolMap w p) = F.realPolynomialSymbolMap b ω hlayers w p := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_polynomial_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ) (Γ : Subgroup F.Group) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
      ∃ (r γ : F.realification.Group) (q : (F.realification.adaptedPolynomialFiltration w).Group),
        (∀ i, |(b.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom ∧
        F.realification.adaptedConstantGroupHom w r * q *
          F.realification.adaptedConstantGroupHom w γ = g ∧
        coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        F.realPolynomialSymbolHom b ω hlayers w q = F.realPolynomialSymbolHom b ω hlayers w g := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ _ _ F b ω hlayers w Γ l H p hl hinner hb hp hd hH hlp g
  obtain ⟨r, hr, γ, hγ, hconst⟩ := hrep b F.lowerCentralSeries_eq_bot Γ l H p hl hinner hb hp hd hH hlp
    (F.realification.adaptedPolynomialConstantHom w g)
  obtain ⟨q, hfactor, hzero, hsymbol⟩ := F.realification.exists_constant_normalized_polynomial w g r γ hconst
  refine ⟨r, γ, q, hr, hγ, hfactor, hzero, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact congrArg (F.realPolynomialSymbolQuotientEquiv b ω hlayers w)
    (congrArg NilpotentLieBCHGroup.coord hsymbol)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_native_polynomial_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (weight : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weight i}))
      (w : σ → ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
      ∃ (a κ : D.RealGroup) (q : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        κ ∈ D.realLattice ∧
        D.filtration.realification.adaptedConstantGroupHom w a * q *
          D.filtration.realification.adaptedConstantGroupHom w κ = g ∧
        coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        D.filtration.realPolynomialSymbolHom D.basis weight hF w q =
          D.filtration.realPolynomialSymbolHom D.basis weight hF w g := by
  obtain ⟨c, _, hnormalize⟩ := exists_bounded_polynomial_normalization s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D weight hF w p hp hD g
  have hbound : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨a, κ, q, ha, hκ, hfactor, hzero, hsymbol⟩ :=
    hnormalize D.filtration D.basis weight hF w D.lattice D.grid ⌈Real.exp p⌉₊ (p + 1)
      D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) (by linarith)
      (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  exact ⟨a, κ, q, fun i => (ha i).trans (Real.exp_le_exp.mpr hbound), hκ,
    hfactor, hzero, hsymbol⟩

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

theorem realPolynomialSymbolQuotientEquiv_natural
    (x : F.realification.PolynomialSymbol w) :
    G.realPolynomialSymbolQuotientEquiv c τ hG w
      (F.realification.filteredPolynomialSymbolMap G.realification
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ) w x) =
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolQuotientEquiv b ω hF w x) := by
  obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
  exact (F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c τ hG w p).symm

theorem exists_real_polynomial_lift_with_symbol
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (x : F.RealPolynomialSymbol w) (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x =
      G.realPolynomialSymbolMap c τ hG w q) :
    ∃ p : F.realification.adaptedLieSubalgebra w,
      F.realPolynomialSymbolMap b ω hF w p = x ∧
      F.realification.filteredPolynomialMap G.realification
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ) w p = q := by
  let e := F.realPolynomialSymbolQuotientEquiv b ω hF w
  have hc : F.realification.filteredPolynomialSymbolMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w (e.symm x) =
        G.realification.polynomialSymbolMap w q := by
    apply (G.realPolynomialSymbolQuotientEquiv c τ hG w).injective
    calc
      _ = (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
          (e (e.symm x)) :=
        F.realPolynomialSymbolQuotientEquiv_natural G φ hφ b ω hF c τ hG w _
      _ = (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x := by
        rw [e.apply_symm_apply]
      _ = _ := hcompat
  obtain ⟨p, hp, hq⟩ := F.realification.exists_polynomial_lift_with_symbol G.realification
    (realLieHomToRat (realificationLieHom φ)) (F.realificationLieHom_mem_layer G φ hφ) w
    (F.realificationLieHom_layer_surjective G φ hφ hsurj) (e.symm x) q hc
  refine ⟨p, ?_, hq⟩
  have he := congrArg e hp
  exact he.trans (e.apply_symm_apply x)

theorem exists_real_polynomial_group_lift_with_symbol
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (x : F.RealPolynomialSymbolGroup w)
    (q : (G.realification.adaptedPolynomialFiltration w).Group)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x.coord =
      (G.realPolynomialSymbolHom c τ hG w q).coord) :
    ∃ p : (F.realification.adaptedPolynomialFiltration w).Group,
      F.realPolynomialSymbolHom b ω hF w p = x ∧
      F.realPolynomialGroupMap G φ hφ w p = q := by
  obtain ⟨p, hp, hq⟩ := F.exists_real_polynomial_lift_with_symbol G φ hφ b ω hF c τ hG w
    hsurj x.coord q.coord hcompat
  exact ⟨⟨p⟩, NilpotentLieBCHGroup.ext hp, NilpotentLieBCHGroup.ext hq⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

theorem exists_prescribed_marked_polynomial_factorization
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (hprod : E * P * R = F.realPolynomialSymbolHom b ω hF w g)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (hE : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
      (G.realPolynomialSymbolHom c τ hG w EF).coord)
    (hR : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
      (G.realPolynomialSymbolHom c τ hG w RF).coord) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      F.realPolynomialSymbolHom b ω hF w e = E ∧
      F.realPolynomialSymbolHom b ω hF w p = P ∧
      F.realPolynomialSymbolHom b ω hF w r = R ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w p =
        EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ := by
  obtain ⟨e, he, heF⟩ := F.exists_real_polynomial_group_lift_with_symbol G φ hφ
    b ω hF c τ hG w hsurj E EF hE
  obtain ⟨r, hr, hrF⟩ := F.exists_real_polynomial_group_lift_with_symbol G φ hφ
    b ω hF c τ hG w hsurj R RF hR
  refine ⟨e, e⁻¹ * g * r⁻¹, r, by group, he, ?_, hr, heF, hrF, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, he, hr, ← hprod]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, heF, hrF]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

noncomputable def realFilteredSymbolGroupMap :
    F.RealPolynomialSymbolGroup w →* G.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.filteredPolynomialSymbolMap G φ hφ w)

theorem exists_prescribed_fast_polynomial_factorization
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (hprod : E * P * R = F.realPolynomialSymbolHom b ω hF w g)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (hleft : ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
      G.realPolynomialSymbolHom c τ hG w EF).coord ∈
        realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)))
    (hright : (G.realPolynomialSymbolHom c τ hG w RF *
      (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈
        realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w))) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      (F.realPolynomialSymbolHom b ω hF w p).coord ∈ realificationLieSubalgebra U ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w p =
        EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ := by
  obtain ⟨A, D, _, _, hprod', hfast, hEF, hRF⟩ :=
    NilpotentLieBCHGroup.exists_real_prescribed_image_factors
      (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.filteredPolynomialSymbolMap G φ hφ w) U E P R
      (G.realPolynomialSymbolHom c τ hG w EF)
      (G.realPolynomialSymbolHom c τ hG w RF) hP hleft hright
  have hE : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
      (E * A).coord = (G.realPolynomialSymbolHom c τ hG w EF).coord :=
    congrArg NilpotentLieBCHGroup.coord hEF
  have hR : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
      (D * R).coord = (G.realPolynomialSymbolHom c τ hG w RF).coord :=
    congrArg NilpotentLieBCHGroup.coord hRF
  obtain ⟨e, p, r, hepr, _, hp, _, heF, hrF, hpF⟩ :=
    F.exists_prescribed_marked_polynomial_factorization G φ hφ b ω hF c τ hG w
      hsurj g (E * A) (A⁻¹ * P * D⁻¹) (D * R) (hprod'.trans hprod) EF RF hE hR
  refine ⟨e, p, r, hepr, ?_, heF, hrF, hpF⟩
  rw [hp]
  exact hfast

end Erdos3.NilpotentLieFiltration

end

end OAI
