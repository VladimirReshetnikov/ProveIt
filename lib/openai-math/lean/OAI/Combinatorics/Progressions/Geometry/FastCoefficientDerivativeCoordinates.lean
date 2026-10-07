import OAI.Combinatorics.Progressions.Dynamics.FastCoefficientDimensionBudget
import OAI.Combinatorics.Progressions.Estimates.ControlledRealFastCoefficientAction

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_controlled_real_fast_coefficient_coordinates
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 2958) ∧ l ∣ m ∧
        (∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid m) ∧
        (∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w m (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + 2) ^ 2958) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + 2) ^ 2958) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have hb := F.exists_real_fast_coefficient_unitriangular_basis e ω hF w hw U hU
    v hspan hH hv hp hn hm hq hd hdm hHp
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, _, haction⟩ := hb
  have hDh' : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
      ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954) := by
    have hpow : Real.exp ((p + 2) ^ 420) ≤ Real.exp ((p + 2) ^ 2954) :=
      Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by decide))
    exact fun i j => ⟨(hDh i j).1.trans hpow, (hDh i j).2.trans hpow⟩
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hdim).trans hd
  have hc := controlled_weighted_quotient_coordinates (F.realFirstCoefficientBasis e ω hF w) b
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (fun i => i.val.1) (fun i => (rows i).val.1) D S hD hDS hDb hSb hp hd hd'
    2954 (by decide) hDh' hSh l hl hlp
  obtain ⟨m, hmpos, hmbound, hlm, hgrid, hRgrid, hR, hweighted⟩ := hc
  refine ⟨d, hdim, rows, hinj, b, rationalCoordinateSection (F.realFirstCoefficientBasis e ω hF w) S,
    m, hmpos, hmbound, hlm, hgrid, hRgrid, hR, ?_, ?_, haction⟩
  · intro T hT M hM
    exact hweighted (monomialScale T) (monomialScale_pos T hT) M hM
  · intro i j hij
    have h := congrArg (fun A => A j i) hD
    simpa only [LinearMap.toMatrix_apply, Matrix.map_apply, hDb j i hij, map_zero] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def FastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid m) ∧
        (∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w m (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

theorem exists_fast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ FastCoefficientCoordinateSpec s C := by
  let Q : Polynomial ℕ :=
    3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) * (Polynomial.X + 1) +
    2 * Polynomial.X + 2 +
    (Polynomial.X + Polynomial.C (s + 3)) ^ (s + 3) * (Polynomial.X + 1) + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + 2) ^ 2958
  have hexists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hexists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U hU v hspan H hH hv p hp hι hσ hκ hHp l hl hlp
  classical
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  let q := fastCoefficientMatrixParameter s p
  have hq : 0 ≤ q := fastCoefficientMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_fastCoefficientMatrixParameter s hp
  have hdims := F.fastCoefficient_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + 2) ^ 2958 ≤ (p + C) ^ C := by
    simpa [B, Q, q, fastCoefficientMatrixParameter, reducedMatrixParameter, Polynomial.eval₂_pow]
      using hbound p hp
  have hraw := F.exists_controlled_real_fast_coefficient_coordinates e ω hF w hw U hU
    v hspan hH hv hq hdims.1 (hκ.trans hpq) hdims.2.1 hdims.2.2.1 hdims.2.2.2
    (hHp.trans (Real.exp_le_exp.mpr hpq)) l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, hlm, hgrid, hRgrid, hR, hweighted, hblock, haction⟩ := hraw
  have hdim' : d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) := by
    exact hdim.trans (firstCoefficientIndex_card_le w ω (s + 1) hw
      (F.adaptedBasis_weight_le_step e ω hF))
  have hbudget : Real.exp ((q + 2) ^ 2958) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hfinal
  refine ⟨d, hdim', rows, hinj, b, R, m, hm, hmp.trans hbudget, hlm,
    hgrid, hRgrid, hR, ?_, hblock, haction⟩
  intro T hT M hM
  obtain ⟨hproj, hlift⟩ := hweighted T hT M hM
  constructor
  · intro x hx i
    exact (hproj x hx i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hM) (monomialScale_pos T hT _).le)
  · intro y hy i
    exact (hlift y hy i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hM) (monomialScale_pos T hT _).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_uniform_real_fast_coefficient_coordinates
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ δ : ℕ, 0 < δ ∧ (δ : ℝ) ≤ Real.exp ((p + 2) ^ 2958) ∧
        (∀ l : ℕ, ∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid (δ * l)) ∧
        (∀ l : ℕ, ∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w (δ * l) (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + 2) ^ 2958) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + 2) ^ 2958) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have hOne : ((1 : ℕ) : ℝ) ≤ Real.exp p := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  have hraw := F.exists_controlled_real_fast_coefficient_coordinates e ω hF w hw U hU
      v hspan hH hv hp hn hm hq hd hdm hHp 1 (by decide) hOne
  obtain ⟨d, hdim, rows, hinj, b, R, δ, hδ, hδp, _, hproj, hlift, hright, hweighted, hblock, haction⟩ := hraw
  refine ⟨d, hdim, rows, hinj, b, R, δ, hδ, hδp, ?_, ?_, hright, hweighted, hblock, haction⟩
  · intro l x hx
    exact linearMap_grid_of_integer (F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap
      (b.equivFun.toLinearMap.comp (F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ) δ hproj l x hx
  · intro l y hy
    exact linearMap_grid_of_integer (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      ((F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap.comp R) δ hlift l y hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

variable {σ κ L : Type*} [Fintype σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
    F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))

noncomputable def fastCoefficientDirectionCoordinates
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) : (σ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
  b.equivFun.toLinearMap.comp
    ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ.comp
        (F.realFirstCoefficientDirectionMap B.coord))

theorem fastCoefficientDirectionCoordinates_apply
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ) :
    F.fastCoefficientDirectionCoordinates U b B h =
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
          (F.realFirstCoefficientDirectionMap B.coord h)) := rfl

omit [Fintype σ] in
theorem fastCoefficientAdjoint_coordinates [DecidableEq κ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (x : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
        (F.realFirstCoefficientAdjoint (fun _ => 1) B x)) =
      LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap *ᵥ
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) := by
  have h := LinearMap.toMatrix_mulVec_repr b b
    (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x)
  exact (congrArg b.equivFun (F.realFastCoefficientAdjoint_mk (fun _ => 1) (by simp) U B hB x)).symm.trans
    h.symm

theorem fastCoefficientDerivative_coordinates [DecidableEq κ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (h : σ → ℝ) (S R : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (heq : F.realFirstCoefficientDirectionMap B.coord h -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) :
    F.fastCoefficientDirectionCoordinates U b B h =
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ S) +
      LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap *ᵥ
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ R) := by
  have hq := (Submodule.Quotient.eq
    (F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))).mpr heq
  let q := (F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
  have hadd := (b.equivFun.toLinearMap.comp q).map_add S (F.realFirstCoefficientAdjoint (fun _ => 1) B R)
  have hadj := F.fastCoefficientAdjoint_coordinates U b B hB R
  exact (congrArg b.equivFun hq).trans (hadd.trans (congrArg₂ (· + ·) rfl hadj))

end Erdos3.NilpotentLieFiltration

end

end OAI
