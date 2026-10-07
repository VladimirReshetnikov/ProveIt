import OAI.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
import OAI.Combinatorics.Progressions.Dynamics.ResetFromCommonQuotient

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem symbolSlowBound_one (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) :
    F.SymbolSlowBound b ω hlayers w T M 1 := by
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z| ≤ _
  simp only [map_zero, Finsupp.zero_apply, abs_zero]
  exact div_nonneg hM (monomialScale_pos T hT z.val.1).le

theorem symbolRationalGrid_one (l : ℕ) : F.SymbolRationalGrid b ω hlayers w l 1 := by
  change (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z) ∈ realDenominatorGrid l
  have hzero : (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z) =
      (0 : SymbolBasisIndex w ω → ℝ) := by
    funext z
    simp only [map_zero, Finsupp.zero_apply, Pi.zero_apply]
  rw [hzero]
  exact realDenominatorGrid_zero l

theorem realSymbolGradeQuotientHom_first (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w 1 g = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (lieQuotientMap_eq_zero ((F.polynomialSymbolFiltration w).realification.layerIdeal 1) _).mpr
  change g.coord ∈ (F.polynomialSymbolFiltration w).realification.layer 1
  rw [(F.polynomialSymbolFiltration w).realification.one_eq_top]
  exact Submodule.mem_top

theorem realSymbolGradeQuotient_mem_terminal_iff
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w (s + 1) g ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
        (F.realSymbolGradeQuotientHom w (s + 1)) ↔ g.coord ∈ realificationLieSubalgebra U := by
  rw [F.realSymbolGradeQuotient_mem_iff w U (s + 1) g,
    (F.polynomialSymbolFiltration w).realification.terminal, sup_bot_eq]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_terminal_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      P.coord ∈ realificationLieSubalgebra U →
      P'.coord ∈ realificationLieSubalgebra U →
      E * P * R = E' * P' * R' →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R →
      F.SymbolRationalGrid b ω hlayers w l R' →
      (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
        (R' * R⁻¹).coord ∈ realificationLieSubalgebra U := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_symbol_comparison_mod_layer s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp
    hι hσ hκ hHp hlp hb hv T hT E P R E' P' R' hP hP' heq hE hE' hR hR'
  have hresult := hcompare F b ω hlayers w hw U v hspan H l p hH hl hp
    hι hσ hκ hHp hlp hb hv T hT (s + 1) le_rfl E P R E' P' R'
    ((F.realSymbolGradeQuotient_mem_terminal_iff w U P).mpr hP)
    ((F.realSymbolGradeQuotient_mem_terminal_iff w U P').mpr hP')
    (congrArg (F.realSymbolGradeQuotientHom w (s + 1)) heq) hE hE' hR hR'
  exact ⟨(F.realSymbolGradeQuotient_mem_terminal_iff w U (E⁻¹ * E')).mp hresult.1,
    (F.realSymbolGradeQuotient_mem_terminal_iff w U (R' * R⁻¹)).mp hresult.2⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_simultaneous_symbol_extension (s a : ℕ) :
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
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        ∀ k : ℕ, k ≤ s → ∀ (X E₀ R₀ : F.RealPolynomialSymbolGroup w)
          (E P R : η → F.RealPolynomialSymbolGroup w),
        (∀ j, E j * P j * R j = X) →
        (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
        F.SymbolRationalGrid b ω hlayers w l R₀ →
        (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
        (∀ j, F.realSymbolGradeQuotientHom w k (E₀⁻¹ * X * R₀⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U j)).map
            (F.realSymbolGradeQuotientHom w k)) →
        ∃ E₁ R₁ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ C)) E₁ ∧
          F.SymbolRationalGrid b ω hlayers w m R₁ ∧
          F.realSymbolGradeQuotientHom w k E₁ = F.realSymbolGradeQuotientHom w k E₀ ∧
          F.realSymbolGradeQuotientHom w k R₁ = F.realSymbolGradeQuotientHom w k R₀ ∧
          ∀ j, F.realSymbolGradeQuotientHom w (k + 1) (E₁⁻¹ * X * R₁⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U j)).map
              (F.realSymbolGradeQuotientHom w (k + 1)) := by
  obtain ⟨c₀, _, hreset⟩ := exists_symbol_reset_from_common_quotient s a
  obtain ⟨c₁, _, hslowprod⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨c₂, _, hratprod⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨c₃, _, hcommon⟩ := exists_common_symbol_grade_corrections s 1
  obtain ⟨c₄, _, hstep⟩ := exists_controlled_symbol_grade_step s 1
  obtain ⟨C, hC, hbudget⟩ := exists_symbol_extension_budget a c₀ c₁ c₂ c₃ c₄
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT
  let q₁ : ℝ := (p + c₀) ^ c₀ + (p + 2) ^ a + p + 2
  let q₂ : ℝ := (q₁ + c₁) ^ c₁ + (q₁ + c₂) ^ c₂ + q₁ + 2
  let q₃ : ℝ := (q₂ + c₃) ^ c₃ + q₂ + 2
  have h₀ : 0 ≤ (p + c₀) ^ c₀ := by positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq₁ : 0 ≤ q₁ := by dsimp [q₁]; positivity
  have hp₁ : p ≤ q₁ := by dsimp [q₁]; linarith
  have hreset₁ : (p + c₀) ^ c₀ ≤ q₁ := by dsimp [q₁]; linarith
  have ha₁ : (p + 2) ^ a ≤ q₁ := by dsimp [q₁]; linarith
  have hs₁ : 0 ≤ (q₁ + c₁) ^ c₁ := by positivity
  have hr₁ : 0 ≤ (q₁ + c₂) ^ c₂ := by positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have h₁₂ : q₁ ≤ q₂ := by dsimp [q₂]; linarith
  have hs₂ : (q₁ + c₁) ^ c₁ ≤ q₂ := by dsimp [q₂]; linarith
  have hr₂ : (q₁ + c₂) ^ c₂ ≤ q₂ := by dsimp [q₂]; linarith
  have hc₂ : 0 ≤ (q₂ + c₃) ^ c₃ := by positivity
  have hq₃ : 0 ≤ q₃ := by dsimp [q₃]; positivity
  have h₂₃ : q₂ ≤ q₃ := by dsimp [q₃]; linarith
  have hc₃ : (q₂ + c₃) ^ c₃ ≤ q₃ := by dsimp [q₃]; linarith
  have hp₂ : p ≤ q₂ := hp₁.trans h₁₂
  have hp₃ : p ≤ q₃ := hp₂.trans h₂₃
  have hf : 0 ≤ (q₃ + c₄) ^ c₄ := by positivity
  have htotal : (p + c₀) ^ c₀ + (q₂ + c₃) ^ c₃ + (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C := hbudget p hp
  have hcut₀ : (p + c₀) ^ c₀ ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right hc₂).trans ((le_add_of_nonneg_right hf).trans htotal)
  have hcut₃ : (q₂ + c₃) ^ c₃ ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left h₀).trans ((le_add_of_nonneg_right hf).trans htotal)
  have hfinal : (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left (add_nonneg h₀ hc₂)).trans htotal
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  have hgraded (j : η) : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) (U j).toSubmodule := by
    have heq : (fun z : SymbolBasisIndex w ω => ω z.val.2) = (fun z => Finsupp.weight w z.val.1) :=
      funext (fun z => z.property.symm)
    rw [heq]
    exact (hblock j).graded _ _ _ (Finsupp.weight w)
  obtain ⟨m₁, hm₁, hm₁p, hlm₁, hresetm⟩ := hreset F b ω hlayers w hw H l p hH hl hp hι hσ hκ hHp hlp hb
    T (fun i => (Real.exp_le_exp.mpr hcut₀).trans (hT i))
  obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hproductsm⟩ := hratprod F b ω hlayers w hw H q₁ hH hq₁
    (hι.trans hp₁) (hσ.trans hp₁) (hHp.trans (Real.exp_le_exp.mpr hp₁)) hb m₁ hm₁
    (hm₁p.trans (Real.exp_le_exp.mpr hreset₁))
  obtain ⟨m₃, hm₃, hm₃p, hm₂m₃, hcommonm⟩ := hcommon F b ω hlayers w hw U v hspan hblock H m₂ q₂
    hH hm₂ hq₂ (hι.trans hp₂) (hσ.trans hp₂) (hκ.trans hp₂) (hη.trans hp₂)
    (hHp.trans (Real.exp_le_exp.mpr hp₂)) (hm₂p.trans (Real.exp_le_exp.mpr hr₂)) hv
    T (fun i => (Real.exp_le_exp.mpr hcut₃).trans (hT i))
  obtain ⟨m₄, hm₄, hm₄p, hm₃m₄, hstepm⟩ := hstep F b ω hlayers w hw H m₃ q₃ hH hm₃ hq₃
    (hι.trans hp₃) (hσ.trans hp₃) (hHp.trans (Real.exp_le_exp.mpr hp₃))
    (hm₃p.trans (Real.exp_le_exp.mpr hc₃)) hb T hTpos
  have hlm₃ : l ∣ m₃ := hlm₁.trans (hm₁m₂.trans hm₂m₃)
  refine ⟨m₄, hm₄, hm₄p.trans (Real.exp_le_exp.mpr hfinal), hlm₃.trans hm₃m₄, ?_⟩
  intro k hk X E₀ R₀ E P R hX hP hE₀ hE hR₀ hR hY
  let Y := E₀⁻¹ * X * R₀⁻¹
  let A₀ := fun j => F.truncateRealSymbol b ω hlayers w k (E₀⁻¹ * E j)
  let D₀ := fun j => F.truncateRealSymbol b ω hlayers w k (R j * R₀⁻¹)
  let E' := fun j => E j * (A₀ j)⁻¹
  let P' := fun j => A₀ j * P j * D₀ j
  let R' := fun j => (D₀ j)⁻¹ * R j
  have hdata (j : η) : E' j * P' j * R' j = X ∧
      (P' j).coord ∈ realificationLieSubalgebra (U j) ∧
      F.realSymbolGradeQuotientHom w k (E' j) = F.realSymbolGradeQuotientHom w k E₀ ∧
      F.realSymbolGradeQuotientHom w k (R' j) = F.realSymbolGradeQuotientHom w k R₀ ∧
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + c₀) ^ c₀)) (E' j) ∧
      F.SymbolRationalGrid b ω hlayers w m₁ (R' j) := by
    have hprod : E₀ * Y * R₀ = E j * P j * R j := by
      calc
        E₀ * Y * R₀ = X := by dsimp [Y]; group
        _ = E j * P j * R j := (hX j).symm
    obtain ⟨hprod', hmid, hEq, hRq, hslow, hgrid⟩ := hresetm (U j) (v j) (hspan j) (hgraded j) (hv j)
      k (by omega) (E j) (P j) (R j) E₀ Y R₀ (hP j) (hY j)
      (congrArg (F.realSymbolGradeQuotientHom w k) hprod) (hE j) hE₀ (hR j) hR₀
    exact ⟨hprod'.trans (hX j), hmid, hEq, hRq, hslow, hgrid⟩
  let A := fun j => E₀⁻¹ * E' j
  let D := fun j => R' j * R₀⁻¹
  have hAs (j : η) : F.SymbolSlowBound b ω hlayers w T (Real.exp ((q₁ + c₁) ^ c₁)) (A j) := by
    have hi : ∀ g ∈ [E₀⁻¹, E' j], F.SymbolSlowBound b ω hlayers w T (Real.exp ((q₁ + 2) ^ 1)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · apply (F.symbolSlowBound_inv_iff b ω hlayers w T _ _).mpr
        exact F.symbolSlowBound_mono b ω hlayers w T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using ha₁.trans (le_add_of_nonneg_right (by norm_num)))) _ hE₀
      · exact F.symbolSlowBound_mono b ω hlayers w T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using hreset₁.trans (le_add_of_nonneg_right (by norm_num)))) _
          (hdata j).2.2.2.2.1
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hslowprod F b ω hlayers w hw H q₁ hH hq₁
      (hι.trans hp₁) (hσ.trans hp₁) (hHp.trans (Real.exp_le_exp.mpr hp₁)) hb T hTpos [E₀⁻¹, E' j] (by simp) hi
  have hDg (j : η) : F.SymbolRationalGrid b ω hlayers w m₂ (D j) := by
    have hi : ∀ g ∈ [R' j, R₀⁻¹], F.SymbolRationalGrid b ω hlayers w m₁ g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (hdata j).2.2.2.2.2
      · exact F.symbolRationalGrid_inv b ω hlayers w m₁ (F.symbolRationalGrid_mono b ω hlayers w hl hlm₁ _ hR₀)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproductsm [R' j, R₀⁻¹] (by simp) hi
  let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ) (fun z => ω z.val.2) k
  have hlin (j : η) : π Y.coord - π (A j).coord - π (D j).coord ∈ realificationLieSubalgebra (U j) := by
    have h := F.symbol_current_grade_residual_mem b ω hlayers w (U j) (hgraded j) k
      (E' j) (P' j) (R' j) E₀ R₀ (hdata j).2.1 (hdata j).2.2.1.symm (hdata j).2.2.2.1
    change π (E₀⁻¹ * (E' j * P' j * R' j) * R₀⁻¹).coord - π (A j).coord - π (D j).coord ∈ _ at h
    rw [(hdata j).1] at h
    exact h
  obtain ⟨Ac, Dc, hAc, hDc, hAcs, hDcg, hres⟩ := hcommonm k Y.coord A D
    (fun j => F.symbolSlowBound_mono b ω hlayers w T hTpos
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hs₂.trans (le_add_of_nonneg_right (by norm_num)))) _ (hAs j))
    hDg hlin
  obtain ⟨_, hEq, hRq, hnext, hslow, hgrid⟩ := hstepm U hgraded k X E₀ R₀ Ac Dc hY hAc hDc hres
    (F.symbolSlowBound_mono b ω hlayers w T hTpos
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using
        ((ha₁.trans (h₁₂.trans h₂₃)).trans (le_add_of_nonneg_right (by norm_num))))) _ hE₀)
    (F.symbolSlowBound_mono b ω hlayers w T hTpos
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hc₃.trans (le_add_of_nonneg_right (by norm_num)))) _ hAcs)
    (F.symbolRationalGrid_mono b ω hlayers w hl hlm₃ _ hR₀) hDcg
  refine ⟨E₀ * Ac, Dc * R₀, F.symbolSlowBound_mono b ω hlayers w T hTpos
    (Real.exp_le_exp.mpr hfinal) _ hslow, hgrid, hEq, hRq, ?_⟩
  intro j
  have hnorm : (E₀ * Ac)⁻¹ * X * (Dc * R₀)⁻¹ = Ac⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * Dc⁻¹ := by group
  rw [hnorm]
  exact hnext j

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_simultaneous_symbol_splitting (s a : ℕ) :
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
      ∀ (X : F.RealPolynomialSymbolGroup w) (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = X) →
      (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (E₀ P₀ R₀ : F.RealPolynomialSymbolGroup w),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        E₀ * P₀ * R₀ = X ∧
        P₀.coord ∈ realificationLieSubalgebra (⨅ j, U j) ∧
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ C)) E₀ ∧
        F.SymbolRationalGrid b ω hlayers w m R₀ := by
  obtain ⟨K, hK, hextend⟩ := exists_simultaneous_symbol_extension s 1
  let C := max 2 ((a + 4) * budgetDepthExponent K s)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT X E P R hX hP hE hR
  let q₀ : ℝ := (p + 2) ^ a + p
  let Q := iteratedPowerBudget K q₀
  have hq₀ : 0 ≤ q₀ := by dsimp [q₀]; positivity
  have hp₀ : p ≤ q₀ := le_add_of_nonneg_left (by positivity)
  have ha₀ : (p + 2) ^ a ≤ q₀ := le_add_of_nonneg_right hp
  have hK₁ : 1 ≤ K := by omega
  have hQnonneg : ∀ n, 0 ≤ Q n := iteratedPowerBudget_nonneg K hq₀
  have hQmono : Monotone Q := iteratedPowerBudget_monotone hK₁ hq₀
  have hpQ (n : ℕ) : p ≤ Q n := hp₀.trans (iteratedPowerBudget_ge hK₁ hq₀ n)
  have haQ (n : ℕ) : (p + 2) ^ a ≤ Q n := ha₀.trans (iteratedPowerBudget_ge hK₁ hq₀ n)
  have hstart : q₀ ≤ (p + 2) ^ (a + 2) := by
    have hbase : 1 ≤ p + 2 := by linarith
    have hpow : (p + 2) ^ a ≤ (p + 2) ^ (a + 1) := pow_le_pow_right₀ hbase (by omega)
    have hpp : p ≤ (p + 2) ^ (a + 1) := le_power_budget hp (by omega)
    calc
      q₀ ≤ (p + 2) ^ (a + 1) + (p + 2) ^ (a + 1) := add_le_add hpow hpp
      _ = 2 * (p + 2) ^ (a + 1) := by ring
      _ ≤ (p + 2) * (p + 2) ^ (a + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ (a + 2) := (pow_succ' (p + 2) (a + 1)).symm
  have hQfinal : Q s ≤ (p + 2) ^ C := by
    have hbound := polynomial_budget_comp hp hq₀ (a + 2) (budgetDepthExponent K s)
      hstart (iteratedPowerBudget_le_power K hq₀ s)
    apply hbound.trans
    apply pow_le_pow_right₀ (by linarith : 1 ≤ p + 2)
    exact le_max_right _ _
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTstage (n : ℕ) (hn : n < s) : ∀ i, Real.exp ((Q n + 2) ^ K) ≤ T i := by
    intro i
    apply (Real.exp_le_exp.mpr ?_).trans (hT i)
    change Q (n + 1) ≤ (p + 2) ^ C
    exact (hQmono (by omega)).trans hQfinal
  have hind : ∀ n : ℕ, n ≤ s →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (Q n) ∧ l ∣ m ∧
        ∃ E₀ R₀ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp (Q n)) E₀ ∧
          F.SymbolRationalGrid b ω hlayers w m R₀ ∧
          ∀ j, F.realSymbolGradeQuotientHom w (n + 1) (E₀⁻¹ * X * R₀⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U j)).map
              (F.realSymbolGradeQuotientHom w (n + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨l, hl, hlp.trans (Real.exp_le_exp.mpr (hpQ 0)), dvd_refl l, 1, 1,
        F.symbolSlowBound_one b ω hlayers w T hTpos (Real.exp_nonneg _),
        F.symbolRationalGrid_one b ω hlayers w l, ?_⟩
      intro j
      rw [F.realSymbolGradeQuotientHom_first w]
      exact Subgroup.one_mem _
    | succ n ih =>
      intro hn
      obtain ⟨m, hm, hmp, hlm, E₀, R₀, hE₀, hR₀, hY⟩ := ih (by omega)
      obtain ⟨m', hm', hmp', hmm', hstep⟩ := hextend F b ω hlayers w hw U v hspan hblock H m (Q n)
        hH hm (hQnonneg n) (hι.trans (hpQ n)) (hσ.trans (hpQ n)) (hκ.trans (hpQ n)) (hη.trans (hpQ n))
        (hHp.trans (Real.exp_le_exp.mpr (hpQ n))) hmp hb hv T (hTstage n (by omega))
      have hEn : F.SymbolSlowBound b ω hlayers w T (Real.exp ((Q n + 2) ^ 1)) E₀ :=
        F.symbolSlowBound_mono b ω hlayers w T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using
            (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2) : Q n ≤ Q n + 2))) _ hE₀
      have hEi : ∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((Q n + 2) ^ 1)) (E j) := by
        intro j
        apply F.symbolSlowBound_mono b ω hlayers w T hTpos _ _ (hE j)
        apply Real.exp_le_exp.mpr
        simpa only [pow_one] using (haQ n).trans (le_add_of_nonneg_right (by norm_num))
      have hRi : ∀ j, F.SymbolRationalGrid b ω hlayers w m (R j) :=
        fun j => F.symbolRationalGrid_mono b ω hlayers w hl hlm _ (hR j)
      obtain ⟨E₁, R₁, hE₁, hR₁, _, _, hY₁⟩ := hstep (n + 1) hn X E₀ R₀ E P R hX hP hEn hEi hR₀ hRi hY
      exact ⟨m', hm', hmp', hlm.trans hmm', E₁, R₁, hE₁, hR₁, hY₁⟩
  obtain ⟨m, hm, hmp, hlm, E₀, R₀, hE₀, hR₀, hY⟩ := hind s le_rfl
  refine ⟨m, E₀, E₀⁻¹ * X * R₀⁻¹, R₀, hm, hmp.trans (Real.exp_le_exp.mpr hQfinal), hlm,
    by group, ?_, F.symbolSlowBound_mono b ω hlayers w T hTpos (Real.exp_le_exp.mpr hQfinal) _ hE₀, hR₀⟩
  rw [realificationLieSubalgebra_iInf, lieSubalgebra_mem_iInf]
  intro j
  exact (F.realSymbolGradeQuotient_mem_terminal_iff w (U j) _).mp (hY j)

end Erdos3.NilpotentLieFiltration

end

end OAI
