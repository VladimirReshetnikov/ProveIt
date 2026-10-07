import OAI.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
import OAI.Combinatorics.Progressions.Estimates.UniformFastCoefficientSpec

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def FullFastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (_hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val)
        (F.reducedSquareBasis_layers e ω hF))
      (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val) W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ j i, RationalHeightLE
      ((F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val)
        (F.reducedSquareBasis_layers e ω hF)).repr (v j) i) H)
    {p : ℝ} (_hp : 0 ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p),
    let U := F.fastPointwiseSquare e ω hF w W
    let J := F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸ J),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun (J.mkQ x) ∈ realDenominatorGrid (m * l)) ∧
        (∀ l (y : Fin d → ℝ), y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w (m * l) (R y)) ∧
        (∀ y : Fin d → ℝ, J.mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun (J.mkQ x) i| ≤
              Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr (J.mkQ (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

theorem exists_fullFast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ FullFastCoefficientCoordinateSpec s C := by
  have hex := exists_uniform_fast_coefficient_coordinate_bound s
  obtain ⟨c, _, hcoords⟩ := hex
  let Q : Polynomial ℕ := 3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) *
    (Polynomial.X + 1) + 2 * Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw W hW v hspan H hH hv p hp hι hσ hκ hHp U J
  classical
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let bW := F.reducedSquareBasis e ω hF
  let ωW := fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val
  let v' := F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily bW ωW
    (F.reducedSquareBasis_layers e ω hF) w v
  have hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w)
      (fun i => i.val.1) U.toSubmodule :=
    F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_blockInvariant bW ωW
      (F.reducedSquareBasis_layers e ω hF) w W
  have hspan' : Submodule.span ℚ (Set.range v') = U.toSubmodule :=
    F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_span bW ωW
      (F.reducedSquareBasis_layers e ω hF) w W hW v hspan
  have hv' : ∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v' j) i) H :=
    F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_height bW ωW
      (F.reducedSquareBasis_layers e ω hF) w v hH hv
  let q := reducedMatrixParameter s p
  have hq : 0 ≤ q := reducedMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_reducedMatrixParameter s hp
  have hdims := F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hcount : (Fintype.card (ReducedSquareSymbolIndex s w ω × κ) : ℝ) ≤ q := by
    simpa only [Fintype.card_prod] using hdims.2.2
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, q, reducedMatrixParameter, Polynomial.eval₂_pow] using hbudget p hp
  have hraw := hcoords F e ω hF w hw U hU v' hspan' hH hv' hq
    (hι.trans hpq) (hσ.trans hpq) hcount (hHp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, hproj, hlift, hright, hweighted, hblock, haction⟩ := hraw
  have hexp : Real.exp ((q + c) ^ c) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hfinal
  refine ⟨d, hdim, rows, hinj, b, R, m, hm, hmp.trans hexp, hproj, hlift, hright, ?_, hblock, haction⟩
  intro T hT M hM
  obtain ⟨hproj', hlift'⟩ := hweighted T hT M hM
  constructor
  · intro x hx i
    exact (hproj' x hx i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp hM) (monomialScale_pos T hT _).le)
  · intro y hy i
    exact (hlift' y hy i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp hM) (monomialScale_pos T hT _).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
