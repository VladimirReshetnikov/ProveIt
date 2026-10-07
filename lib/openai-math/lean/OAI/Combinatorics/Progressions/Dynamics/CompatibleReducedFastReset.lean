import OAI.Combinatorics.Progressions.Estimates.ReducedProjectedComparison
import OAI.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions
import OAI.Combinatorics.Progressions.Estimates.SquareStructureHeight

namespace OAI

section

namespace Erdos3

def reducedResetParameter (a : ℕ) (p : ℝ) : ℝ :=
  ((p + 2) ^ 10 + 2) ^ 36 + (p + 2) ^ a + p + 2

theorem reducedResetParameter_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedResetParameter a p := by
  unfold reducedResetParameter
  positivity

theorem le_reducedResetParameter (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ reducedResetParameter a p := by
  have h₁ : 0 ≤ ((p + 2) ^ 10 + 2) ^ 36 := by positivity
  have h₂ : 0 ≤ (p + 2) ^ a := by positivity
  exact (le_add_of_nonneg_left (add_nonneg h₁ h₂)).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))

theorem reducedResetParameter_controls (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ a ≤ reducedResetParameter a p + 2 ∧
      ((p + 2) ^ 10 + 2) ^ 36 ≤ reducedResetParameter a p ∧
      ((p + 2) ^ 10 + 2) ^ 18 + (p + 2) ^ a ≤ reducedResetParameter a p + 2 := by
  have h₁ : 0 ≤ ((p + 2) ^ 10 + 2) ^ 36 := by positivity
  have h₂ : 0 ≤ (p + 2) ^ a := by positivity
  have hbase : 1 ≤ (p + 2) ^ 10 + 2 := by
    exact (by norm_num : (1 : ℝ) ≤ 2).trans
      (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 2) ^ 10))
  have hpow := pow_le_pow_right₀ hbase (by decide : 18 ≤ 36)
  have hsum : ((p + 2) ^ 10 + 2) ^ 36 + (p + 2) ^ a ≤ reducedResetParameter a p :=
    (le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hplus : reducedResetParameter a p ≤ reducedResetParameter a p + 2 :=
    le_add_of_nonneg_right (by norm_num)
  exact ⟨(le_add_of_nonneg_left h₁).trans (hsum.trans hplus),
    (le_add_of_nonneg_right h₂).trans hsum,
    (add_le_add hpow (le_refl ((p + 2) ^ a))).trans (hsum.trans hplus)⟩

theorem exists_reduced_reset_budget (a cs cr : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (reducedResetParameter a p + cs) ^ cs ≤ (p + C) ^ C ∧
      (reducedResetParameter a p + cr) ^ cr ≤ (p + C) ^ C := by
  let Z : Polynomial ℕ := ((Polynomial.X + 2) ^ 10 + 2) ^ 36 +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let B := (Z + Polynomial.C cs) ^ cs + (Z + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hz := reducedResetParameter_nonneg a hp
  have hs : 0 ≤ (reducedResetParameter a p + cs) ^ cs := by positivity
  have hr : 0 ≤ (reducedResetParameter a p + cr) ^ cr := by positivity
  have hh : (reducedResetParameter a p + cs) ^ cs +
      (reducedResetParameter a p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Z, reducedResetParameter, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨(le_add_of_nonneg_right hr).trans hh, (le_add_of_nonneg_left hs).trans hh⟩

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def ControlledReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
      (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      2 * (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤ p →
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
          (F.reducedSquareRealSymbolHom w R * D⁻¹) →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) =
            A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹ ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

def ReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
          (F.reducedSquareRealSymbolHom w R * D⁻¹) →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) =
            A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹ ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledReducedFastResetSpec s a C := by
  obtain ⟨cs, _, hprodSlow⟩ := exists_symbol_slow_mul_inv_bound s
  obtain ⟨cr, _, hprodRat⟩ := exists_symbol_rational_inv_mul_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_reduced_reset_budget a cs cr
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw _ _ U v hspan hU H l p hH hl hp
    hdim hσ hrows hcols hHp hlp hc hv
  let G := F.squareFiltration.quotientTop
  let b := F.reducedSquareBasis e ω hF
  let ν : ReducedSquareBasisIndex s ω → ℕ := fun i => squareBasisWeight ω i.val
  have hG := F.reducedSquareBasis_layers e ω hF
  have hstruct := F.reducedSquareBasis_structure_height e ω hF hH hc
  have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
    (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
  have hd : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p :=
    (Nat.cast_le.mpr hcard).trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdim)
  let z := reducedResetParameter a p
  have hz : 0 ≤ z := reducedResetParameter_nonneg a hp
  have hpz : p ≤ z := le_reducedResetParameter a hp
  have hinput := (reducedResetParameter_controls a hp).1
  have hden := (reducedResetParameter_controls a hp).2.1
  have hgain := (reducedResetParameter_controls a hp).2.2
  have hlifts := F.exists_controlled_reduced_fast_lift w e ω hF U v hspan hU hH hl hv hp hrows hcols hHp hlp
  obtain ⟨S, n, hn, hnp, hln, hlift, hliftSlow, hliftRat⟩ := hlifts
  have hnz : (n : ℝ) ≤ Real.exp z := hnp.trans (Real.exp_le_exp.mpr hden)
  have hRats := hprodRat G b ν hG w hw H z hH hz
    (hd.trans hpz) (hσ.trans hpz) (hHp.trans (Real.exp_le_exp.mpr hpz)) hstruct n hn hnz
  obtain ⟨m, hmdata⟩ := hRats
  have hm := hmdata.1
  have hmp := hmdata.2.1
  have hnm := hmdata.2.2.1
  have hRat := hmdata.2.2.2
  have hbud := hbudget p hp
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hbud.2), hln.trans hnm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
  let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
  have hc := (hlift _ hleft).1
  have hcq := (hlift _ hleft).2
  have hdmem := (hlift _ hright).1
  have hdq := (hlift _ hright).2
  have hreset := synchronize_splitting_projection (F.reducedSquareRealSymbolHom w)
    (NilpotentLieBCHGroup.realificationSubgroup
      (hnil := G.polynomialSymbol_lowerCentralSeries_eq_bot w) U) E P R c d A D hP hc hdmem hcq hdq
  refine ⟨hreset.1, hreset.2.1, hreset.2.2.1, hreset.2.2.2.1, hreset.2.2.2.2, ?_, ?_⟩
  · have hE' : G.SymbolSlowBound b ν hG w T (Real.exp (z + 2)) E := by
      apply G.symbolSlowBound_mono b ν hG w T hT _ E hE
      exact Real.exp_le_exp.mpr hinput
    have hcSlow := hliftSlow T hT (Real.exp ((p + 2) ^ a)) (Real.exp_nonneg _) _ hLeftSlow
    have hc' : G.SymbolSlowBound b ν hG w T (Real.exp (z + 2)) c := by
      apply G.symbolSlowBound_mono b ν hG w T hT _ c hcSlow
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hgain
    have hproduct := hprodSlow G b ν hG w hw H z hH hz (hd.trans hpz) (hσ.trans hpz)
      (hHp.trans (Real.exp_le_exp.mpr hpz)) hstruct T hT E c hE' hc'
    exact G.symbolSlowBound_mono b ν hG w T hT (Real.exp_le_exp.mpr hbud.1) _ hproduct
  · have hRn : G.SymbolRationalGrid b ν hG w n R :=
      G.symbolRationalGrid_mono b ν hG w hl hln R hR
    have hdn : G.SymbolRationalGrid b ν hG w n d := hliftRat _ hRightRat
    exact hRat d R hdn hRn

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ReducedFastResetSpec s a C := by
  have hresetExists := exists_controlled_reduced_fast_reset s a
  obtain ⟨c, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := 3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) *
    (Polynomial.X + 1) + 2 * Polynomial.X + 2
  let B := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let q := reducedMatrixParameter s p
  have hq : 0 ≤ q := reducedMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_reducedMatrixParameter s hp
  have hdims := F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, reducedMatrixParameter, Polynomial.eval₂_pow] using hbound p hp
  have hrawExists := hreset F e ω hF w hw U v hspan hU H l q hH hl hq
    hdims.1 (hσ.trans hpq) hdims.2.1 hdims.2.2 (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hlp.trans (Real.exp_le_exp.mpr hpq)) hc hv
  obtain ⟨S, m, hm, hmp, hlm, hraw⟩ := hrawExists
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT hinput E hE
  have hLeftSlow' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hT hinput _ hLeftSlow
  have hresult := hraw T hT E P R A D hP hleft hright hE' hR hLeftSlow' hRightRat
  obtain ⟨hprod, hfast, hA, hD, hmid, hslow, hgrid⟩ := hresult
  refine ⟨hprod, hfast, hA, hD, hmid, ?_, hgrid⟩
  exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT
    (Real.exp_le_exp.mpr hfinal) _ hslow

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def CompatibleReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A B D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        B.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        A * B * D = F.reducedSquareRealSymbolHom w (E * P * R) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) A →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l D →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) = B ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

theorem exists_compatible_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CompatibleReducedFastResetSpec s a C := by
  have hcomparisonExists := exists_reduced_projected_comparison s a
  obtain ⟨cc, _, hcomparison⟩ := hcomparisonExists
  have hresetExists := exists_reduced_fast_reset s 1
  obtain ⟨cr, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Q + Polynomial.C cr) ^ cr
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let q := (p + cc) ^ cc + (p + 2) ^ a + p + 2
  have hc0 : 0 ≤ (p + cc) ^ cc := by positivity
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcq : (p + cc) ^ cc ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hsum : (p + cc) ^ cc + (q + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hr0 : 0 ≤ (q + cr) ^ cr := by positivity
  have hcb : (p + cc) ^ cc ≤ (p + C) ^ C := (le_add_of_nonneg_right hr0).trans hsum
  have hrb : (q + cr) ^ cr ≤ (p + C) ^ C := (le_add_of_nonneg_left hc0).trans hsum
  have hcompdata := hcomparison F e ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hc hv
  obtain ⟨n, hn, hnp, hln, hcompare⟩ := hcompdata
  have hresetdata := hreset F e ω hF w hw U v hspan hU H n q hH hn hq
    (hι.trans hpq) (hσ.trans hpq) (hκ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hnp.trans (Real.exp_le_exp.mpr hcq)) hc hv
  obtain ⟨S, m, hm, hmp, hnm, hresetFactors⟩ := hresetdata
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hrb), hln.trans hnm, ?_⟩
  intro T hT E P R A B D hP hB heq hE hR hA hD
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hcomp := hcompare T (fun i => (Real.exp_le_exp.mpr hcb).trans (hT i))
    E P R A B D hP hB heq hE hA hR hD
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hTpos
    (Real.exp_le_exp.mpr haq) E hE
  have hA' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hTpos
    (Real.exp_le_exp.mpr (hcq.trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))) _ hcomp.2.2.1
  have hR' := F.squareFiltration.quotientTop.symbolRationalGrid_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w hl hln R hR
  have hresult := hresetFactors T hTpos E P R A D hP hcomp.1 hcomp.2.1
    (by simpa only [pow_one] using hE') hR' (by simpa only [pow_one] using hA') hcomp.2.2.2
  refine ⟨hresult.1, hresult.2.1, hresult.2.2.1, hresult.2.2.2.1, ?_, ?_, hresult.2.2.2.2.2.2⟩
  · rw [hresult.2.2.2.2.1, ← heq]
    group
  · exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hTpos
      (Real.exp_le_exp.mpr hrb) _ hresult.2.2.2.2.2.1

end Erdos3.NilpotentLieFiltration

end

end OAI
