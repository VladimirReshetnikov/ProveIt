import OAI.Combinatorics.Progressions.Estimates.SymbolCommonCorrections

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_reset_from_common_quotient (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
        Submodule.span ℚ (Set.range v) = U.toSubmodule →
        BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule →
        (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
        ∀ k : ℕ, k ≤ s + 1 → ∀ E P R E₀ P₀ R₀ : F.RealPolynomialSymbolGroup w,
        P.coord ∈ realificationLieSubalgebra U →
        F.realSymbolGradeQuotientHom w k P₀ ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) →
        F.realSymbolGradeQuotientHom w k (E₀ * P₀ * R₀) = F.realSymbolGradeQuotientHom w k (E * P * R) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        let A := F.truncateRealSymbol b ω hlayers w k (E₀⁻¹ * E)
        let D := F.truncateRealSymbol b ω hlayers w k (R * R₀⁻¹)
        (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
          (A * P * D).coord ∈ realificationLieSubalgebra U ∧
          F.realSymbolGradeQuotientHom w k (E * A⁻¹) = F.realSymbolGradeQuotientHom w k E₀ ∧
          F.realSymbolGradeQuotientHom w k (D⁻¹ * R) = F.realSymbolGradeQuotientHom w k R₀ ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
          F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨cc, hcc, hcompare⟩ := exists_controlled_symbol_comparison_mod_layer s a
  obtain ⟨cr, hcr, hreset⟩ := exists_controlled_symbol_reset s a
  refine ⟨max cc cr, hcc.trans (le_max_left _ _), ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hκ hHp hlp hb T hT
  have hc : (p + cc) ^ cc ≤ (p + (max cc cr : ℕ)) ^ max cc cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hr : (p + cr) ^ cr ≤ (p + (max cc cr : ℕ)) ^ max cc cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m, hm, hmp, hlm, hresetm⟩ := hreset F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hTpos
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hr), hlm, ?_⟩
  intro U v hspan hU hv k hk E P R E₀ P₀ R₀ hP hP₀ hidentity hE hE₀ hR hR₀
  have hPq : F.realSymbolGradeQuotientHom w k P ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) :=
    Subgroup.mem_map.mpr ⟨P, hP, rfl⟩
  obtain ⟨hleft, hright⟩ := hcompare F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv T
    (fun i => (Real.exp_le_exp.mpr hc).trans (hT i)) k hk E₀ P₀ R₀ E P R hP₀ hPq hidentity hE₀ hE hR₀ hR
  obtain ⟨hprod, hmid, hEq, hRq, hslow, hgrid⟩ := hresetm U hU k E P R E₀ R₀ hP hE hE₀ hR hR₀ hleft hright
  exact ⟨hprod, hmid, hEq, hRq,
    F.symbolSlowBound_mono b ω hlayers w T hTpos (Real.exp_le_exp.mpr hr) _ hslow, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
