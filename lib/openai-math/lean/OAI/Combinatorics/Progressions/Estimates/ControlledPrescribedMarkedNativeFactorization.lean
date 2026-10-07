import OAI.Combinatorics.Progressions.Dynamics.FastSymbolCorrectionBudget
import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
import OAI.Combinatorics.Progressions.Estimates.ControlledFixedMarkedNativeFactorization
import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct NNReal

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)
  [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]

noncomputable def filteredSymbolMapDenominator : ℕ :=
  matrixDenominator (fun i j => (G.polynomialSymbolBasis c ν hG w).repr
    (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis b ω hF w j)) i)

theorem realFilteredSymbolGroupMap_slow
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hF w T A g) :
    G.SymbolSlowBound c ν hG w T
      (((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * (H + 1) * A)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  classical
  let B := F.polynomialSymbolBasis b ω hF w
  let C := G.polynomialSymbolBasis c ν hG w
  let ψ := (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap
  let D := LinearMap.toMatrix B C ψ
  have hblock : ∀ i j, i.val.1 ≠ j.val.1 → D i j = 0 := by
    intro i j hij
    simpa only [D, B, C, ψ, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using
      F.filteredPolynomialSymbolMap_monomial_blocks G b ω hF c ν hG φ hφ w j i hij
  have hheight : ∀ i j, RationalHeightLE (D i j) H := by
    intro i j
    simpa only [D, B, C, ψ, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using
      F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i
  intro i
  have h := rational_coordinate_map_weighted (B.baseChange ℝ) (C.baseChange ℝ)
    (ψ.baseChange ℝ) D (realified_linear_coordinate_matrix B C ψ)
    (fun j => j.val.1) (fun j => j.val.1) hblock (H : ℝ≥0)
    (fun i j => by exact_mod_cast (hheight i j).1)
    (monomialScale T) (monomialScale_pos T hT) hA g.coord hg i
  exact h

theorem realFilteredSymbolGroupMap_slow_exp
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hF w T A g) :
    G.SymbolSlowBound c ν hG w T (Real.exp ((p + 2) ^ 3) * A)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  have hbound := F.realFilteredSymbolGroupMap_slow G b ω hF c ν hG φ hφ w
    hH hentries T hT hA g hg
  have hfac : ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * (H + 1) ≤
      Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power _ hp hdim 1 (by omega))
    gcongr
    exact hHp.trans (Real.exp_le_exp.mpr (by simp))
  intro i
  exact (hbound i).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfac hA) (monomialScale_pos T hT _).le)

theorem realFilteredSymbolGroupMap_grid (l : ℕ) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w l g) :
    G.SymbolRationalGrid c ν hG w
      (F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w * l)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  classical
  have h := realified_linear_coordinate_grid
    (F.polynomialSymbolBasis b ω hF w) (G.polynomialSymbolBasis c ν hG w)
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap l g.coord hg
  have hm : LinearMap.toMatrix (F.polynomialSymbolBasis b ω hF w)
      (G.polynomialSymbolBasis c ν hG w)
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap =
      fun i j => (G.polynomialSymbolBasis c ν hG w).repr
        (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis b ω hF w j)) i := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [hm] at h
  exact h

theorem filteredSymbolMapDenominator_pos :
    0 < F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w :=
  matrixDenominator_pos _

theorem filteredSymbolMapDenominator_le {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w ≤
      H ^ (Fintype.card (SymbolBasisIndex w ν) * Fintype.card (SymbolBasisIndex w ω)) := by
  apply matrixDenominator_le
  intro i j
  exact F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i

theorem filteredSymbolMapDenominator_le_exp {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    (F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w : ℝ) ≤
      Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power _ hp 1 htarget hsource
  intro i j
  have h := (F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w
    hH hentries j i).2
  exact (Nat.cast_le.mpr h).trans (hHp.trans (Real.exp_le_exp.mpr (by simp)))

theorem exists_realFilteredSymbolGroupMap_grid
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ g : F.RealPolynomialSymbolGroup w,
        F.SymbolRationalGrid b ω hF w l g →
        G.SymbolRationalGrid c ν hG w m (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  let d := F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w
  have hd := F.filteredSymbolMapDenominator_le_exp G b ω hF c ν hG φ hφ w
    hH hentries hp hsource htarget hHp
  refine ⟨d * l, Nat.mul_pos
    (F.filteredSymbolMapDenominator_pos G b ω hF c ν hG φ hφ w) hl, ?_,
    dvd_mul_left _ _, ?_⟩
  · rw [Nat.cast_mul]
    calc
      (d : ℝ) * l ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hd hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + 2) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by omega)
        calc
          (p + 2) ^ 3 + p ≤ 2 * (p + 2) ^ 3 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 3 := by gcongr; linarith
          _ = (p + 2) ^ 4 := by ring
  · exact F.realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ w l

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_controlled_prescribed_fast_symbol_factorization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]
        (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : ξ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.polynomialSymbolBasis b ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w ν) : ℝ) ≤ p →
      ((Fintype.card (SymbolBasisIndex w ω) * Fintype.card ξ : ℕ) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) →
      (∀ j i, RationalHeightLE ((F.polynomialSymbolBasis b ω hF w).repr (v j) i) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.RealPolynomialSymbolGroup w) (EF RF : G.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
        G.SymbolSlowBound c ν hG w T (Real.exp ((p + 2) ^ a)) EF →
        F.SymbolRationalGrid b ω hF w l R → G.SymbolRationalGrid c ν hG w l RF →
        ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ * EF).coord ∈
          realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)) →
        (RF * (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)) →
        ∃ E' P' R' : F.RealPolynomialSymbolGroup w,
          E' * P' * R' = E * P * R ∧
          P'.coord ∈ realificationLieSubalgebra U ∧
          F.realFilteredSymbolGroupMap G φ hφ w E' = EF ∧
          F.realFilteredSymbolGroupMap G φ hφ w R' = RF ∧
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) E' ∧
          F.SymbolRationalGrid b ω hF w m R' := by
  obtain ⟨ceF, hceF, hslowF⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨ceG, hceG, hslowG⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨crF, hcrF, hrationalF⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨crG, hcrG, hrationalG⟩ := exists_symbol_rational_product_bound s 2
  let ce := max ceF ceG
  let cr := max crF crG
  obtain ⟨C, hC, hbudget⟩ := exists_fastSymbolCorrectionBudget a ce cr
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ξ L M _ _ _ _ _ _ _ _ F G b ω hF c ν hG φ hφ w hw _ _
    U v hspan hU H l p hH hl hp hι hκ hσ hrows hcols hHp hlp hb hc hentries hv
  classical
  let p₀ : ℝ := p + (p + 2) ^ a + (p + 2) ^ 4 + 2
  let p₁ : ℝ := p₀ + (p₀ + ce) ^ ce + (p₀ + cr) ^ cr
  let p₂ : ℝ := p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 + 2
  have hbase : 0 ≤ p + 2 := add_nonneg hp (by norm_num)
  have ha0 : 0 ≤ (p + 2) ^ a := pow_nonneg hbase _
  have h40 : 0 ≤ (p + 2) ^ 4 := pow_nonneg hbase _
  have hp₀ : 0 ≤ p₀ := add_nonneg (add_nonneg (add_nonneg hp ha0) h40) (by norm_num)
  have hce0 : 0 ≤ (p₀ + ce) ^ ce := pow_nonneg (add_nonneg hp₀ (Nat.cast_nonneg _)) _
  have hcr0 : 0 ≤ (p₀ + cr) ^ cr := pow_nonneg (add_nonneg hp₀ (Nat.cast_nonneg _)) _
  have hp₁ : 0 ≤ p₁ := add_nonneg (add_nonneg hp₀ hce0) hcr0
  have hsection : 0 ≤ (p₁ + 2) ^ 10 + 2 :=
    add_nonneg (pow_nonneg (add_nonneg hp₁ (by norm_num)) _) (by norm_num)
  have h36 : 0 ≤ ((p₁ + 2) ^ 10 + 2) ^ 36 := pow_nonneg hsection _
  have h18 : 0 ≤ ((p₁ + 2) ^ 10 + 2) ^ 18 := pow_nonneg hsection _
  have hp₂ : 0 ≤ p₂ := add_nonneg (add_nonneg (add_nonneg hp₁ h36) h18) (by norm_num)
  have hpp₀ : p ≤ p₀ :=
    ((le_add_of_nonneg_right ha0).trans (le_add_of_nonneg_right h40)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have h₀₁ : p₀ ≤ p₁ := (le_add_of_nonneg_right hce0).trans (le_add_of_nonneg_right hcr0)
  have h₁₂ : p₁ ≤ p₂ :=
    ((le_add_of_nonneg_right h36).trans (le_add_of_nonneg_right h18)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hpp₁ := hpp₀.trans h₀₁
  have hpp₂ := hpp₁.trans h₁₂
  have hdimF : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p := by
    simp only [Fintype.card_sum, Nat.cast_add] at hrows
    linarith only [hrows, Nat.cast_nonneg (α := ℝ) (Fintype.card (SymbolBasisIndex w ν))]
  have hdimG : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p := by
    simp only [Fintype.card_sum, Nat.cast_add] at hrows
    linarith only [hrows, Nat.cast_nonneg (α := ℝ) (Fintype.card (SymbolBasisIndex w ω))]
  let d := F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w
  have hd : 0 < d := F.filteredSymbolMapDenominator_pos G b ω hF c ν hG φ hφ w
  have hdle := F.filteredSymbolMapDenominator_le G b ω hF c ν hG φ hφ w hH hentries
  have hdl : ((d * l : ℕ) : ℝ) ≤ Real.exp p₀ := by
    apply (kernel_inclusion_denominator_mul_le_exp _ _ H d l hp hdimG hdimF hHp hdle hlp).trans
    apply Real.exp_le_exp.mpr
    exact (le_add_of_nonneg_left (add_nonneg hp ha0)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨l₁, hl₁, hl₁p, hdl₁, hprodG⟩ := hrationalG G c ν hG w hw H p₀ hH hp₀
    (hκ.trans hpp₀) (hσ.trans hpp₀) (hHp.trans (Real.exp_le_exp.mpr hpp₀)) hc
    (d * l) (Nat.mul_pos hd hl) hdl
  have hll₁ : l ∣ l₁ := (dvd_mul_left l d).trans hdl₁
  have hl₁p₁ : (l₁ : ℝ) ≤ Real.exp p₁ := by
    apply (hl₁p.trans (Real.exp_le_exp.mpr
      (shifted_power_self_mono hp₀ (by omega : 1 ≤ crG) (le_max_right crF crG)))).trans
      (Real.exp_le_exp.mpr ?_)
    exact le_add_of_nonneg_left (add_nonneg hp₀ hce0)
  obtain ⟨S, l₂, hl₂, hl₂p, hl₁₂, hsolve, hslowLift, hgridLift⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (G.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.polynomialSymbolBasis b ω hF w) (G.polynomialSymbolBasis c ν hG w)
      (fun z => z.val.1) (fun z => z.val.1) U v hspan hU
      (F.filteredPolynomialSymbolMap G φ hφ w)
      (fun i j hij => F.filteredPolynomialSymbolMap_monomial_blocks G b ω hF c ν hG φ hφ w j i hij)
      hH hl₁ hv
      (fun i j => F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i)
      hp₁ (hrows.trans hpp₁) (hcols.trans hpp₁) (hHp.trans (Real.exp_le_exp.mpr hpp₁)) hl₁p₁
  simp only [Basis.equivFun_apply] at hslowLift hgridLift
  have hl₂p₂ : (l₂ : ℝ) ≤ Real.exp p₂ := by
    apply hl₂p.trans (Real.exp_le_exp.mpr ?_)
    exact ((le_add_of_nonneg_left hp₁).trans (le_add_of_nonneg_right h18)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨m, hm, hmp, hl₂m, hprodF⟩ := hrationalF F b ω hF w hw H p₂ hH hp₂
    (hι.trans hpp₂) (hσ.trans hpp₂) (hHp.trans (Real.exp_le_exp.mpr hpp₂)) hb l₂ hl₂ hl₂p₂
  have hbound : (p₂ + ce) ^ ce + (p₂ + cr) ^ cr ≤ (p + C) ^ C := hbudget p hp
  have hfinalE : (p₂ + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp₂ (Nat.cast_nonneg cr)) cr)).trans hbound
  have hfinalR : (p₂ + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp₂ (Nat.cast_nonneg ce)) ce)).trans hbound
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr
    ((shifted_power_self_mono hp₂ (by omega : 1 ≤ crF) (le_max_left crF crG)).trans hfinalR)), (hll₁.trans hl₁₂).trans hl₂m, ?_⟩
  intro T hT E P R EF RF hP hE hEF hR hRF hleft hright
  let π := F.realFilteredSymbolGroupMap G φ hφ w
  let lift := NilpotentLieBCHGroup.realLinearCoordinateLift
    (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w) S
  let A := lift ((π E)⁻¹ * EF)
  let D := lift (RF * (π R)⁻¹)
  obtain ⟨hA, hAimage⟩ := hsolve ((π E)⁻¹ * EF) hleft
  obtain ⟨hD, hDimage⟩ := hsolve (RF * (π R)⁻¹) hright
  have himageA : π A = (π E)⁻¹ * EF := hAimage
  have himageD : π D = RF * (π R)⁻¹ := hDimage
  have hAfast : A.coord ∈ realificationLieSubalgebra U := hA
  have hDfast : D.coord ∈ realificationLieSubalgebra U := hD
  have hslowπ := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ w
    hH hentries hp hdimF hHp T hT (Real.exp_nonneg _) E hE
  have h34 : (p + 2) ^ 3 ≤ (p + 2) ^ 4 := pow_le_pow_right₀ (by linarith only [hp]) (by omega)
  have hslowπ' : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + 2) ^ (1 : ℕ))) (π E) := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hslowπ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    calc
      _ ≤ (p + 2) ^ 4 + (p + 2) ^ a := add_le_add h34 le_rfl
      _ = (p + 2) ^ a + (p + 2) ^ 4 := add_comm _ _
      _ ≤ p + (p + 2) ^ a + (p + 2) ^ 4 :=
        add_le_add (le_add_of_nonneg_left hp) le_rfl
      _ ≤ p₀ := le_add_of_nonneg_right (by norm_num)
      _ ≤ p₀ + 2 := le_add_of_nonneg_right (by norm_num)
  have hslowEF : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + 2) ^ (1 : ℕ))) EF := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hEF
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    exact (((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h40)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hslowDis : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + ce) ^ ce)) ((π E)⁻¹ * EF) := by
    have hh := hslowG G c ν hG w hw H p₀ hH hp₀ (hκ.trans hpp₀) (hσ.trans hpp₀)
      (hHp.trans (Real.exp_le_exp.mpr hpp₀)) hc T hT [(π E)⁻¹, EF] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact (G.symbolSlowBound_inv_iff c ν hG w T _ _).mpr hslowπ'
        · exact hslowEF)
    have hh' : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + ceG) ^ ceG)) ((π E)⁻¹ * EF) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
    exact G.symbolSlowBound_mono c ν hG w T hT (Real.exp_le_exp.mpr
      (shifted_power_self_mono hp₀ (by omega : 1 ≤ ceG) (le_max_right ceF ceG))) _ hh'
  have hslowDis₁ : G.SymbolSlowBound c ν hG w T (Real.exp p₁) ((π E)⁻¹ * EF) := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hslowDis
    apply Real.exp_le_exp.mpr
    exact (le_add_of_nonneg_left hp₀).trans (le_add_of_nonneg_right hcr0)
  have hslowA : F.SymbolSlowBound b ω hF w T
      (Real.exp (((p₁ + 2) ^ 10 + 2) ^ 18) * Real.exp p₁) A := by
    exact hslowLift (monomialScale T) (monomialScale_pos T hT)
      (Real.exp p₁) (Real.exp_nonneg _) ((π E)⁻¹ * EF) hslowDis₁
  have hslowA₂ : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + 2) ^ (1 : ℕ))) A := by
    apply F.symbolSlowBound_mono b ω hF w T hT _ _ hslowA
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    calc
      _ = p₁ + ((p₁ + 2) ^ 10 + 2) ^ 18 := add_comm _ _
      _ ≤ p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 :=
        add_le_add (le_add_of_nonneg_right h36) le_rfl
      _ ≤ p₂ := le_add_of_nonneg_right (by norm_num)
      _ ≤ p₂ + 2 := le_add_of_nonneg_right (by norm_num)
  have hslowE₂ : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + 2) ^ (1 : ℕ))) E := by
    apply F.symbolSlowBound_mono b ω hF w T hT _ _ hE
    apply Real.exp_le_exp.mpr
    have hh : (p + 2) ^ a ≤ p₀ :=
      ((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h40)).trans
        (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
    simp only [pow_one]
    exact (hh.trans (h₀₁.trans h₁₂)).trans (le_add_of_nonneg_right (by norm_num))
  have hgridπ : G.SymbolRationalGrid c ν hG w (d * l) (π R) :=
    F.realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ w l R hR
  have hgridRF : G.SymbolRationalGrid c ν hG w (d * l) RF :=
    realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l d) hRF
  have hgridDis : G.SymbolRationalGrid c ν hG w l₁ (RF * (π R)⁻¹) := by
    have hh := hprodG [RF, (π R)⁻¹] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hgridRF
      · exact G.symbolRationalGrid_inv c ν hG w (d * l) hgridπ)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
  have hgridD : F.SymbolRationalGrid b ω hF w l₂ D := hgridLift _ hgridDis
  have hgridR₂ : F.SymbolRationalGrid b ω hF w l₂ R :=
    realDenominatorGrid_subset_of_dvd hl (hll₁.trans hl₁₂) hR
  refine ⟨E * A, A⁻¹ * P * D⁻¹, D * R, by
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left], ?_, ?_, ?_, ?_, ?_⟩
  · exact (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).mul_mem
      ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).mul_mem
        ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).inv_mem hAfast) hP)
      ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).inv_mem hDfast)
  · change π (E * A) = EF
    rw [map_mul, himageA, mul_inv_cancel_left]
  · change π (D * R) = RF
    rw [map_mul, himageD, inv_mul_cancel_right]
  · have hh := hslowF F b ω hF w hw H p₂ hH hp₂ (hι.trans hpp₂) (hσ.trans hpp₂)
      (hHp.trans (Real.exp_le_exp.mpr hpp₂)) hb T hT [E, A] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hslowE₂
        · exact hslowA₂)
    have hh' : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + ceF) ^ ceF)) (E * A) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
    exact F.symbolSlowBound_mono b ω hF w T hT (Real.exp_le_exp.mpr
      ((shifted_power_self_mono hp₂ (by omega : 1 ≤ ceF) (le_max_left ceF ceG)).trans hfinalE)) _ hh'
  · have hh := hprodF [D, R] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hgridD
      · exact hgridR₂)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hh

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredSymbolGroupMap_symbol [Fintype σ] [Fintype ι] [Fintype κ] (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realFilteredSymbolGroupMap G φ hφ w (F.realPolynomialSymbolHom b ω hF w g) =
      G.realPolynomialSymbolHom c ν hG w (F.realPolynomialGroupMap G φ hφ w g) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c ν hG w g.coord

variable [Fintype σ] [Fintype ι] [Fintype κ]

theorem exists_common_refiltered_marked_symbol_factors
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (side : σ → ℝ), (∀ i, 0 < side i) →
      ∀ (q : ℝ) (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
      ∃ El Pl Rl : G.RealPolynomialSymbolGroup (fun _ : σ => 1),
        El * Pl * Rl = G.realPolynomialSymbolHom c ν hG (fun _ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ => 1) g) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c ν hG (fun _ => 1)
            (W.map (F.associatedGradedMap G φ hφ))) ∧
        G.SymbolSlowBound c ν hG (fun _ => 1) side
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        G.SymbolRationalGrid c ν hG (fun _ => 1) m Rl := by
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    F.exists_realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ (fun _ : σ => 1)
      hH hentries hp hsource htarget hHp l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro side hside q W g hfactor
  obtain ⟨E, P, R, hprod, hP, hE, hR⟩ :=
    hfactor.symbolFactors F b ω hF side q l W g
  let π := F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1)
  refine ⟨π E, π P, π R, ?_, ?_, ?_, hgrid R hR⟩
  · rw [← map_mul, ← map_mul, hprod]
    exact F.realFilteredSymbolGroupMap_symbol G b ω hF c ν hG φ hφ (fun _ => 1) g
  · exact F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ
      (fun _ => 1) W P.coord hP
  · have hslow := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) hH hentries hp hsource hHp side hside (Real.exp_nonneg q) E hE
    simpa only [Real.exp_add] using hslow

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

def fullMarkedNativeInput (s a C : ℕ) (p : ℝ) : ℝ :=
  (pointwiseFastSectionInput s p + C) ^ C + (p + 2) ^ a + pointwiseFastSectionInput s p

theorem exists_controlled_full_marked_native_factorizations (s a : ℕ) :
    ∃ Cf C₀ C₁ : ℕ, 2 ≤ Cf ∧ 2 ≤ C₀ ∧ 2 ≤ C₁ ∧
    ∀ {σ ι κ ξ μ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (U : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
    ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card μ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fixedMarkedNativeInput 1 C₀ (fullMarkedNativeInput s a Cf p)) + C₁) ^ C₁) ∧
      l ∣ m ∧
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      G.PolynomialRationalGrid c w l RF →
    ∃ (u : ℝ ⊗[ℚ] M) (z : M)
      (EF' RF' : (G.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (c.baseChange ℝ).repr u i ∧ (c.baseChange ℝ).repr u i < 1) ∧
      (∀ i, ∃ n : ℤ, c.repr z i = n) ∧
      EF' = EF * G.realification.adaptedConstantGroupHom w ⟨u⟩ ∧
      RF' = G.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩ * RF ∧
      G.realPolynomialSymbolHom c τ hG w EF' = G.realPolynomialSymbolHom c τ hG w EF ∧
      G.realPolynomialSymbolHom c τ hG w RF' = G.realPolynomialSymbolHom c τ hG w RF ∧
      G.PolynomialSlowBound c w T (Real.exp ((fullMarkedNativeInput s a Cf p + C₀) ^ C₀)) EF' ∧
      G.PolynomialRationalGrid c w m RF' ∧
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group),
      F.realPolynomialGroupMap G φ hφ w g = X →
    ∀ E P R : F.RealPolynomialSymbolGroup w,
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolRationalGrid b ω hF w l R →
      ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
        G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
      (G.realPolynomialSymbolHom c τ hG w RF *
        (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ w e = EF' ∧
      F.realPolynomialGroupMap G φ hφ w r = RF' ∧
      F.realPolynomialGroupMap G φ hφ w middle = EF'⁻¹ * X * RF'⁻¹ ∧
      F.PolynomialSlowBound b w T (Real.exp ((markedNativeLiftInput
        (fixedMarkedNativeInput 1 C₀ (fullMarkedNativeInput s a Cf p)) + C₁) ^ C₁)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w t q) =
          F.adaptedPolynomialRealValueHom w t middle := by
  obtain ⟨Cf, hCf, hfast⟩ := exists_controlled_prescribed_fast_symbol_factorization s a
  obtain ⟨C₀, C₁, hC₀, hC₁, hnative⟩ := exists_controlled_fixed_marked_native_factorizations s 1
  refine ⟨Cf, C₀, C₁, hCf, hC₀, hC₁, ?_⟩
  intro σ ι κ ξ μ L M _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk U v hU hvspan H l p hH hl hp hι hκ hξ hμ hσ hHp hlp hb hc hkernel hentries hv
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w τ) :=
    symbolBasisIndexFintype w τ s hw (G.adaptedBasis_weight_le_step c τ hG)
  let Q := pointwiseFastSectionInput s p
  have hpQ : p ≤ Q := pointwiseFastSectionInput_ge s hp
  have hQ : 0 ≤ Q := hp.trans hpQ
  have hcounts := F.pointwiseSymbolSpanning_section_counts (ξ := μ) G b ω hF c τ hG w hw
    hp hι hκ hμ hσ
  obtain ⟨n, hn, hnp, hln, hcorrect⟩ := hfast F G b ω hF c τ hG φ hφ w hw
    (F.symbolPointwiseSubalgebra b ω hF w U) (F.pointwiseSymbolSpanningFamily b ω hF w v)
    (F.pointwiseSymbolSpanningFamily_span b ω hF w U hU v hvspan)
    (F.symbolPointwiseSubalgebra_blockInvariant b ω hF w U)
    H l Q hH hl hQ (hι.trans hpQ) (hκ.trans hpQ) (hσ.trans hpQ)
    hcounts.2.1 hcounts.2.2 (hHp.trans (Real.exp_le_exp.mpr hpQ))
    (hlp.trans (Real.exp_le_exp.mpr hpQ)) hb hc hentries
    (F.pointwiseSymbolSpanningFamily_height b ω hF w v hH hv)
  let B := fullMarkedNativeInput s a Cf p
  have hslow0 : 0 ≤ (p + 2) ^ a := by positivity
  have hfast0 : 0 ≤ (Q + Cf) ^ Cf := by positivity
  have hQB : Q ≤ B := by
    change Q ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hslow0]
  have hpB : p ≤ B := hpQ.trans hQB
  have hB : 0 ≤ B := hp.trans hpB
  have hfastB : (Q + Cf) ^ Cf ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hslow0, hQ]
  have hslowB : (p + 2) ^ a ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hQ]
  obtain ⟨m, hm, hmp, hnm, hfixed⟩ := hnative F G φ hφ b ω hF c τ hG w hw hsurj
    bk H n B hH hn hB (hι.trans hpB) (hκ.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) (hnp.trans (Real.exp_le_exp.mpr hfastB))
    hb hc hkernel hentries
  refine ⟨m, hm, hmp, hln.trans hnm, ?_⟩
  intro T hT X EF RF hEF hRF
  have hEF' : G.PolynomialSlowBound c w T (Real.exp ((B + 2) ^ 1)) EF :=
    G.polynomialSlowBound_mono c w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hslowB.trans (by linarith only))) EF hEF
  obtain ⟨u, z, EF', RF', hu, hz, hleftFactor, hrightFactor, hESym, hRSym,
    hEFslow, hRFgrid, hsource⟩ := hfixed T hT X EF RF hEF'
      (G.polynomialRationalGrid_of_dvd c w hl hln RF hRF)
  refine ⟨u, z, EF', RF', hu, hz, hleftFactor, hrightFactor, hESym, hRSym,
    hEFslow, hRFgrid, ?_⟩
  intro g hg E P R hprod hP hEslow hRgrid hleft hright
  have hscale : Real.exp ((p + 2) ^ a) ≤ Real.exp ((Q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpQ]) a)
  have himage := F.symbolPointwiseSubalgebra_map G b ω hF c τ hG φ hφ w U hU
  rw [← himage] at hleft hright
  obtain ⟨E', P', R', hprod', hP', hEmark, hRmark, hEbound, hRden⟩ :=
    hcorrect T hT E P R (G.realPolynomialSymbolHom c τ hG w EF)
      (G.realPolynomialSymbolHom c τ hG w RF) hP
      (F.symbolSlowBound_mono b ω hF w T hT hscale E hEslow)
      (G.symbolSlowBound_mono c τ hG w T hT hscale _
        (G.polynomialSlowBound_symbol c τ hG w T _ EF hEF))
      hRgrid (G.polynomialRationalGrid_symbol c τ hG w l RF hRF) hleft hright
  have hEbound' : F.SymbolSlowBound b ω hF w T (Real.exp ((B + 2) ^ 1)) E' :=
    F.symbolSlowBound_mono b ω hF w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hfastB.trans (by linarith only))) E' hEbound
  obtain ⟨e, middle, r, q, hprod'', _, _, _, heF, hrF, hpF, heslow, hrden, hq, hvalues⟩ :=
    hsource U hU g hg E' P' R' (hprod'.trans hprod) hP'
      (congrArg NilpotentLieBCHGroup.coord hEmark)
      (congrArg NilpotentLieBCHGroup.coord hRmark) hEbound' hRden
  exact ⟨e, middle, r, q, hprod'', heF, hrF, hpF, heslow, hrden, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_terminal_discrepancies (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (HMap l : ℕ) (pMap : ℝ), 1 ≤ HMap → 0 < l → 0 ≤ pMap →
      (∀ i j, RationalHeightLE (c.repr (φ (b j)) i) HMap) →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (HMap : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧ l ∣ m ∧
        ∀ (HCompare : ℕ) (pCompare : ℝ), 1 ≤ HCompare → 0 ≤ pCompare →
        (Fintype.card κ : ℝ) ≤ pCompare → (Fintype.card σ : ℝ) ≤ pCompare →
        (Fintype.card χ : ℝ) ≤ pCompare → (HCompare : ℝ) ≤ Real.exp pCompare →
        Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pCompare →
        (∀ i j z, RationalHeightLE (c.repr ⁅c i, c j⁆ z) HCompare) →
        ∀ side : σ → ℝ, (∀ i, Real.exp ((pCompare + C) ^ C) ≤ side i) →
        ∀ q : ℝ, Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pCompare + 2) ^ a) →
        ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
            (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
        (∀ i z, RationalHeightLE
          ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) HCompare) →
        ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
        F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
        ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
          E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ => 1) g ∧
          P.coord ∈ realificationLieSubalgebra
            (F.symbolPointwiseSubalgebra b ω hF (fun _ : σ => 1) W) ∧
          F.SymbolSlowBound b ω hF (fun _ : σ => 1) side (Real.exp q) E ∧
          F.SymbolRationalGrid b ω hF (fun _ : σ => 1) l R ∧
          ∀ E₀ R₀ : G.RealPolynomialSymbolGroup (fun _ : σ => 1),
            (E₀⁻¹ * G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
              (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) * R₀⁻¹).coord ∈
                realificationLieSubalgebra
                  (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                    (W.map (F.associatedGradedMap G φ hφ))) →
            G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
              (Real.exp ((pCompare + 2) ^ a)) E₀ →
            G.SymbolRationalGrid c ν hG (fun _ : σ => 1) m R₀ →
            ((F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1) E)⁻¹ * E₀).coord ∈
              realificationLieSubalgebra
                (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                  (W.map (F.associatedGradedMap G φ hφ))) ∧
            (R₀ * (F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1) R)⁻¹).coord ∈
              realificationLieSubalgebra
                (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                  (W.map (F.associatedGradedMap G φ hφ))) := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_terminal_symbol_comparison s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ χ L M _ _ _ _ _ _ _ _ F G b ω hF c ν hG φ hφ _ _
    HMap l pMap hHMap hl hpMap hentries hsource htarget hHMapExp hlExp
  obtain ⟨m, hm, hmExp, hlm, hmapGrid⟩ :=
    F.exists_realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ (fun _ : σ => 1)
      hHMap hentries hpMap hsource htarget hHMapExp l hl hlExp
  refine ⟨m, hm, hmExp, hlm, ?_⟩
  intro HCompare pCompare hHCompare hpCompare hκ hσ hχ hHCompareExp hgridAbsorb
    hbracket side hside q hslowAbsorb W vg hspan hvg g hnative
  have hsidePos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨E, P, R, hprod, hP, hE, hR⟩ :=
    hnative.symbolFactors F b ω hF side q l W g
  refine ⟨E, P, R, hprod, hP, hE, hR, ?_⟩
  intro E₀ R₀ hterminal hE₀ hR₀
  let π := F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1)
  let U := G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
    (W.map (F.associatedGradedMap G φ hφ))
  let P₀ := E₀⁻¹ * G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
    (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) * R₀⁻¹
  have hmapP : (π P).coord ∈ realificationLieSubalgebra U :=
    F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) W P.coord hP
  have hmapSlow : G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
      (Real.exp ((pCompare + 2) ^ a)) (π E) := by
    have hslow := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) hHMap hentries hpMap hsource hHMapExp side hsidePos
      (Real.exp_nonneg q) E hE
    have hslow' : G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
        (Real.exp ((pMap + 2) ^ 3 + q)) (π E) := by
      simpa only [Real.exp_add] using hslow
    exact G.symbolSlowBound_mono c ν hG (fun _ : σ => 1) side hsidePos hslowAbsorb _ hslow'
  have hmapGridR : G.SymbolRationalGrid c ν hG (fun _ : σ => 1) m (π R) :=
    hmapGrid R hR
  have hcompareProd : π E * π P * π R = E₀ * P₀ * R₀ := by
    calc
      π E * π P * π R = π (F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) g) := by
        rw [← map_mul, ← map_mul, hprod]
      _ = G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) :=
        F.realFilteredSymbolGroupMap_symbol G b ω hF c ν hG φ hφ (fun _ : σ => 1) g
      _ = E₀ * P₀ * R₀ := by
        dsimp only [P₀]
        group
  exact hcompare G c ν hG (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    U vg hspan HCompare m pCompare hHCompare hm hpCompare hκ hσ hχ hHCompareExp
    (hmExp.trans hgridAbsorb) hbracket hvg side hside
    (π E) (π P) (π R) E₀ P₀ R₀ hmapP hterminal hcompareProd hmapSlow hE₀ hmapGridR hR₀

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_prescribed_marked_native_factorizations (s a : ℕ) :
    ∃ Cf Cnative : ℕ, 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (U : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
    ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card μ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf p) + Cnative) ^ Cnative) ∧
      l ∣ m ∧
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      G.PolynomialRationalGrid c w l RF →
      coefficients ((EF⁻¹ * X * RF⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 →
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group),
      F.realPolynomialGroupMap G φ hφ w g = X →
    ∀ E P R : F.RealPolynomialSymbolGroup w,
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolRationalGrid b ω hF w l R →
      ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
        G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
      (G.realPolynomialSymbolHom c τ hG w RF *
        (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w middle = EF⁻¹ * X * RF⁻¹ ∧
      F.PolynomialSlowBound b w T (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf p) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w t q) =
          F.adaptedPolynomialRealValueHom w t middle := by
  obtain ⟨Cf, hCf, hfast⟩ := exists_controlled_prescribed_fast_symbol_factorization s a
  obtain ⟨Cnative, hCnative, hnative⟩ := exists_controlled_marked_native_factorization s 1
  refine ⟨Cf, Cnative, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ L M _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk U v hU hvspan H l p hH hl hp hι hκ hξ hμ hσ hHp hlp hb hc hkernel hentries hv
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w τ) :=
    symbolBasisIndexFintype w τ s hw (G.adaptedBasis_weight_le_step c τ hG)
  let Q := pointwiseFastSectionInput s p
  have hpQ : p ≤ Q := pointwiseFastSectionInput_ge s hp
  have hQ : 0 ≤ Q := hp.trans hpQ
  have hcounts := F.pointwiseSymbolSpanning_section_counts (ξ := μ) G b ω hF c τ hG w hw
    hp hι hκ hμ hσ
  obtain ⟨n, hn, hnp, hln, hcorrect⟩ := hfast F G b ω hF c τ hG φ hφ w hw
    (F.symbolPointwiseSubalgebra b ω hF w U) (F.pointwiseSymbolSpanningFamily b ω hF w v)
    (F.pointwiseSymbolSpanningFamily_span b ω hF w U hU v hvspan)
    (F.symbolPointwiseSubalgebra_blockInvariant b ω hF w U)
    H l Q hH hl hQ (hι.trans hpQ) (hκ.trans hpQ) (hσ.trans hpQ)
    hcounts.2.1 hcounts.2.2 (hHp.trans (Real.exp_le_exp.mpr hpQ))
    (hlp.trans (Real.exp_le_exp.mpr hpQ)) hb hc hentries
    (F.pointwiseSymbolSpanningFamily_height b ω hF w v hH hv)
  let B := fullMarkedNativeInput s a Cf p
  have hslow0 : 0 ≤ (p + 2) ^ a := by positivity
  have hfast0 : 0 ≤ (Q + Cf) ^ Cf := by positivity
  have hQB : Q ≤ B := by
    change Q ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hslow0]
  have hpB : p ≤ B := hpQ.trans hQB
  have hB : 0 ≤ B := hp.trans hpB
  have hfastB : (Q + Cf) ^ Cf ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hslow0, hQ]
  have hslowB : (p + 2) ^ a ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hQ]
  obtain ⟨m, hm, hmp, hnm, hfactor⟩ := hnative F G φ hφ b ω hF c τ hG w hw hsurj
    bk H n B hH hn hB (hι.trans hpB) (hκ.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) (hnp.trans (Real.exp_le_exp.mpr hfastB))
    hb hkernel hentries
  refine ⟨m, hm, hmp, hln.trans hnm, ?_⟩
  intro T hT X EF RF hEF hRF hconstant
  have hEFbound : CoefficientBound (c.baseChange ℝ) T
      (Real.exp ((B + 2) ^ 1)) EF.coord.val :=
    G.polynomialSlowBound_mono c w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hslowB.trans (by linarith only))) EF hEF
  have hRFgrid : CoefficientGrid (c.baseChange ℝ) n RF.coord.val := by
    obtain ⟨z, hz⟩ := G.polynomialRationalGrid_of_dvd c w hl hln RF hRF
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  intro g hg E P R hprod hP hEslow hRgrid hleft hright
  have hscale : Real.exp ((p + 2) ^ a) ≤ Real.exp ((Q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpQ]) a)
  have himage := F.symbolPointwiseSubalgebra_map G b ω hF c τ hG φ hφ w U hU
  rw [← himage] at hleft hright
  obtain ⟨E', P', R', hprod', hP', hEmark, hRmark, hEbound, hRden⟩ :=
    hcorrect T hT E P R (G.realPolynomialSymbolHom c τ hG w EF)
      (G.realPolynomialSymbolHom c τ hG w RF) hP
      (F.symbolSlowBound_mono b ω hF w T hT hscale E hEslow)
      (G.symbolSlowBound_mono c τ hG w T hT hscale _
        (G.polynomialSlowBound_symbol c τ hG w T _ EF hEF))
      hRgrid (G.polynomialRationalGrid_symbol c τ hG w l RF hRF) hleft hright
  have hEbound' : F.SymbolSlowBound b ω hF w T (Real.exp ((B + 2) ^ 1)) E' :=
    F.symbolSlowBound_mono b ω hF w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hfastB.trans (by linarith only))) E' hEbound
  have hfirst : coefficients ((EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 := by
    rw [hg]
    exact hconstant
  obtain ⟨e, middle, r, q, hprod'', _, _, _, heF, hrF, hpF, heslow, hrden, hq, hvalues⟩ :=
    hfactor U hU T hT g E' P' R' (hprod'.trans hprod) hP' EF RF
      (congrArg NilpotentLieBCHGroup.coord hEmark)
      (congrArg NilpotentLieBCHGroup.coord hRmark) hEbound' hEFbound hRden hRFgrid hfirst
  exact ⟨e, middle, r, q, hprod'', heF, hrF, hpF.trans (by rw [hg]), heslow, hrden, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
