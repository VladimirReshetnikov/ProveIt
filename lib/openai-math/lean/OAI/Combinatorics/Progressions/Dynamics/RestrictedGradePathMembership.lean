import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeEvaluation
import OAI.Combinatorics.Progressions.Linear.BasisProjectionRealification

namespace OAI

section

namespace Erdos3

theorem reset_splitting_in_quotient {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (H : Subgroup G) (E P R E₀ R₀ A D : G)
    (hP : P ∈ H) (hA : A ∈ H) (hD : D ∈ H)
    (hAq : φ A = φ (E₀⁻¹ * E)) (hDq : φ D = φ (R * R₀⁻¹)) :
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      A * P * D ∈ H ∧ φ (E * A⁻¹) = φ E₀ ∧ φ (D⁻¹ * R) = φ R₀ := by
  refine ⟨?_, H.mul_mem (H.mul_mem hA hP) hD, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, hAq, map_mul, map_inv]
    group
  · rw [map_mul, map_inv, hDq, map_mul, map_inv]
    group

namespace NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem reset_real_splitting (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (j : ℕ) (E P R E₀ R₀ : F.realification.Group)
    (hP : P.coord ∈ U)
    (hleft : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (E₀⁻¹ * E) ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j)))
    (hright : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (R * R₀⁻¹) ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))) :
    let A := F.truncateRealGrades b w j (E₀⁻¹ * E)
    let D := F.truncateRealGrades b w j (R * R₀⁻¹)
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      (A * P * D).coord ∈ U ∧
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (E * A⁻¹) =
        NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) E₀ ∧
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (D⁻¹ * R) =
        NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) R₀ := by
  exact reset_splitting_in_quotient
    (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))
    (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U) E P R E₀ R₀
    (F.truncateRealGrades b w j (E₀⁻¹ * E)) (F.truncateRealGrades b w j (R * R₀⁻¹)) hP
    (F.truncateRealGrades_mem_of_quotient_mem b w hlayers U hU j _ hleft)
    (F.truncateRealGrades_mem_of_quotient_mem b w hlayers U hU j _ hright)
    (F.truncateRealGrades_quotient b w hlayers j _) (F.truncateRealGrades_quotient b w hlayers j _)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_reset_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ E E₀ R R₀ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
          F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        ∀ j : ℕ,
          let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
          let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
            F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨c₁, _, hslow₁⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨c₂, _, hslow₂⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + (Polynomial.X + Polynomial.C c₁) ^ c₁ +
    (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C c₂) ^ c₂ + (Q + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  let q : ℝ := (p + 2) ^ a + (p + c₁) ^ c₁ + (p + cr) ^ cr + p + 2
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hs0 : 0 ≤ (p + c₁) ^ c₁ := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hsq : (p + c₁) ^ c₁ ≤ q + 2 := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hboth : (q + c₂) ^ c₂ + (q + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hsfinal : (q + c₂) ^ c₂ ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hboth
  have hrfinal : (q + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hboth
  obtain ⟨m₁, hm₁, hm₁p, hlm₁, hproducts₁⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hproducts₂⟩ := hrat F b ω hlayers w hw H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hb m₁ hm₁
    (hm₁p.trans (Real.exp_le_exp.mpr hrq))
  refine ⟨m₂, hm₂, hm₂p.trans (Real.exp_le_exp.mpr hrfinal), hlm₁.trans hm₁m₂, ?_⟩
  intro E E₀ R R₀ hE hE₀ hR hR₀
  have hA : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + c₁) ^ c₁)) (E₀⁻¹ * E) := by
    have hi : ∀ g ∈ [E₀⁻¹, E], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E₀).mpr hE₀
      · exact hE
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow₁ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT [E₀⁻¹, E] (by simp) hi
  have hD : F.SymbolRationalGrid b ω hlayers w m₁ (R * R₀⁻¹) := by
    have hi : ∀ g ∈ [R, R₀⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR₀
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts₁ [R, R₀⁻¹] (by simp) hi
  intro j
  dsimp only
  constructor
  · have hi : ∀ g ∈ [E, (F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E))⁻¹],
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((q + 2) ^ 1)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr (by simpa using haq)) _ hE
      · apply (F.symbolSlowBound_inv_iff b ω hlayers w T _ _).mpr
        exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr (by simpa using hsq)) _
          (F.truncateRealSymbol_slow b ω hlayers w j _ T _ hA)
    have hnew := hslow₂ F b ω hlayers w hw H q hH hq (hι.trans hpq) (hσ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hb T hT
      [E, (F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E))⁻¹] (by simp) hi
    simp only [List.prod_cons, List.prod_nil, mul_one] at hnew
    exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr hsfinal) _ hnew
  · have hi : ∀ g ∈ [(F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹))⁻¹, R],
        F.SymbolRationalGrid b ω hlayers w m₁ g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact F.symbolRationalGrid_inv b ω hlayers w m₁
          (F.truncateRealSymbol_rational b ω hlayers w j _ m₁ hD)
      · exact F.symbolRationalGrid_mono b ω hlayers w hl hlm₁ _ hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts₂ [(F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹))⁻¹, R] (by simp) hi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev RealSymbolGradeQuotientGroup (j : ℕ) :=
  NilpotentLieBCHGroup
    (F.RealPolynomialSymbol w ⧸ (F.polynomialSymbolFiltration w).realification.layerIdeal j) s
    (lie_quotient_lowerCentralSeries_eq_bot
      (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))
      ((F.polynomialSymbolFiltration w).realification.layerIdeal j))

noncomputable def realSymbolGradeQuotientHom (j : ℕ) :
    F.RealPolynomialSymbolGroup w →* F.RealSymbolGradeQuotientGroup w j :=
  NilpotentLieBCHGroup.quotientHom ((F.polynomialSymbolFiltration w).realification.layerIdeal j)

theorem reset_real_symbol_splitting (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (hU : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) U.toSubmodule)
    (j : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hleft : F.realSymbolGradeQuotientHom w j (E₀⁻¹ * E) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j))
    (hright : F.realSymbolGradeQuotientHom w j (R * R₀⁻¹) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j)) :
    let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
    let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      (A * P * D).coord ∈ realificationLieSubalgebra U ∧
      F.realSymbolGradeQuotientHom w j (E * A⁻¹) = F.realSymbolGradeQuotientHom w j E₀ ∧
      F.realSymbolGradeQuotientHom w j (D⁻¹ * R) = F.realSymbolGradeQuotientHom w j R₀ := by
  have hUreal : BasisGradedSubmodule ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) (realificationLieSubalgebra U).toSubmodule :=
    hU.baseChange (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule
  exact (F.polynomialSymbolFiltration w).reset_real_splitting
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) (realificationLieSubalgebra U) hUreal
    j E P R E₀ R₀ hP hleft hright

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ U : LieSubalgebra ℚ (F.PolynomialSymbol w),
        BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule →
        ∀ (j : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        F.realSymbolGradeQuotientHom w j (E₀⁻¹ * E) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j) →
        F.realSymbolGradeQuotientHom w j (R * R₀⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j) →
        let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
        let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
        (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
          (A * P * D).coord ∈ realificationLieSubalgebra U ∧
          F.realSymbolGradeQuotientHom w j (E * A⁻¹) = F.realSymbolGradeQuotientHom w j E₀ ∧
          F.realSymbolGradeQuotientHom w j (D⁻¹ * R) = F.realSymbolGradeQuotientHom w j R₀ ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
          F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨C, hC, hbound⟩ := exists_symbol_reset_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  obtain ⟨m, hm, hmp, hlm, hreset⟩ := hbound F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro U hU j E P R E₀ R₀ hP hE hE₀ hR hR₀ hleft hright
  obtain ⟨hprod, hmid, hEeq, hReq⟩ := F.reset_real_symbol_splitting w b ω hlayers U hU j E P R E₀ R₀ hP hleft hright
  obtain ⟨hslow, hgrid⟩ := hreset E E₀ R R₀ hE hE₀ hR hR₀ j
  exact ⟨hprod, hmid, hEeq, hReq, hslow, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace VectorPolynomial

theorem coefficients_realChartSubstitute_mem_of_range
    {σ τ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    [IsScalarTower ℚ ℝ V] (U : Submodule ℝ V)
    (K : Set (σ → ℝ)) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (p : VectorPolynomial σ ℚ V) (hp : ∀ t ∈ K, eval₂ t p ∈ U) :
    ∀ α, coefficients (realChartSubstitute β p) α ∈ U := by
  apply (eval₂_mem_iff_coefficients U _).mp
  intro u
  rw [eval₂_realChartSubstitute]
  exact hp _ (hβ u)

end VectorPolynomial

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem restricted_grade_path_coefficients
    (w : σ → ℕ) (U : Submodule ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k, F.realSymbolGradeEvaluation b ω hF w j t x ∈ U.baseChange ℝ) :
    ∀ j < k, ∀ α, coefficients (realChartSubstitute β
      (F.realGradedSymbolPolynomial b ω hF w
        (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
          (fun z => ω z.val.2) j x))) α ∈ U.baseChange ℝ := by
  intro j hj
  apply coefficients_realChartSubstitute_mem_of_range (U.baseChange ℝ) K β hβ
  intro t ht
  exact hx t ht j hj

theorem truncateRealSymbol_mem_of_grade_values
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t : σ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x.coord ∈ realificationLieSubalgebra U) :
    (F.truncateRealSymbol b ω hF w k x).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U _).mpr
  intro t
  rw [F.truncateRealSymbol_coord, basisBelowProjection_eq_sum_grades]
  simp only [map_sum]
  apply (realificationLieSubalgebra U).toSubmodule.sum_mem
  intro j hj
  exact hx t j (Finset.mem_range.mp hj)

theorem realSymbolGradeQuotient_mem_of_grade_values
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t : σ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x.coord ∈ realificationLieSubalgebra U) :
    F.realSymbolGradeQuotientHom w k x ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
        (F.symbolPointwiseSubalgebra b ω hF w U)).map (F.realSymbolGradeQuotientHom w k) := by
  apply Subgroup.mem_map.mpr
  refine ⟨F.truncateRealSymbol b ω hF w k x,
    F.truncateRealSymbol_mem_of_grade_values b ω hF w U x k hx, ?_⟩
  exact F.truncateRealSymbol_quotient b ω hF w k x

theorem realSymbolGradeQuotient_mem_of_restricted_path
    (w : σ → ℕ) (v : τ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (y : F.RealPolynomialSymbolGroup v) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x ∈ realificationLieSubalgebra U)
    (hy : ∀ u : τ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF v j u y.coord =
        F.realSymbolGradeEvaluation b ω hF w j
          (fun i => MvPolynomial.eval u (β i)) x) :
    F.realSymbolGradeQuotientHom v k y ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  apply F.realSymbolGradeQuotient_mem_of_grade_values b ω hF v U y k
  intro u j hj
  rw [hy u j hj]
  exact hx _ (hβ u) j hj

end NilpotentLieFiltration
end Erdos3

end

end OAI
