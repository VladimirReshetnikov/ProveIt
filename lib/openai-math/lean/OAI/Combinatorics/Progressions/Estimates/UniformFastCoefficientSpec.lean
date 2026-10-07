import OAI.Combinatorics.Progressions.Geometry.FastCoefficientDerivativeCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def UniformFastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
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
    (_hHp : (H : ℝ) ≤ Real.exp p),
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid (m * l)) ∧
        (∀ l (y : Fin d → ℝ), y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w (m * l) (R y)) ∧
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

theorem exists_uniform_fast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ UniformFastCoefficientCoordinateSpec s C := by
  obtain ⟨C, hC, hspec⟩ := exists_fast_coefficient_coordinate_bound s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U hU v hspan H hH hv p hp hι hσ hκ hHp
  have hOne : ((1 : ℕ) : ℝ) ≤ Real.exp p := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  have hraw := hspec F e ω hF w hw U hU v hspan hH hv hp hι hσ hκ hHp 1 (by decide) hOne
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, _, hproj, hlift, hright, hweighted, hblock, haction⟩ := hraw
  classical
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  refine ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, ?_, ?_, hright, hweighted, hblock, haction⟩
  · intro l x hx
    exact linearMap_grid_of_integer (F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap
      (b.equivFun.toLinearMap.comp (F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ) m hproj l x hx
  · intro l y hy
    exact linearMap_grid_of_integer (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      ((F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap.comp R) m hlift l y hy

end Erdos3.NilpotentLieFiltration

end

end OAI
