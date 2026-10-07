import OAI.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis κ ℝ (F.RealFastCoefficientModule w hw U))
  (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)

local notation "π" => Submodule.mkQ
  (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U))

variable (hR : ∀ y,
  (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) =
    b.equivFun.symm y)

include hR

theorem fastCoefficientAdjoint_weighted_bound
    (rows : κ → FirstCoefficientIndex w ω) (T : σ → ℝ)
    (Cproj Clift D : ℝ) (hClift : 0 ≤ Clift) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      ∀ i, |b.equivFun (π x) i| ≤ Cproj * M / monomialScale T (rows i).val.1)
    (hlift : ∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (Clift * M) (R y))
    (g : F.realFastDiagonalSubgroup w U)
    (had : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      F.FirstCoefficientSlowBound e ω hF w T (D * M) (F.realFirstCoefficientAdjoint w g.val x))
    {M : ℝ} (hM : 0 ≤ M) (y : F.RealFastCoefficientModule w hw U)
    (hy : ∀ i, |b.equivFun y i| ≤ M / monomialScale T (rows i).val.1) :
    ∀ i, |b.equivFun (F.realFastCoefficientAction w hw U g y) i| ≤
      Cproj * D * Clift * M / monomialScale T (rows i).val.1 := by
  let x := R (b.equivFun y)
  have hx : π x = y := (hR (b.equivFun y)).trans (b.equivFun.symm_apply_apply y)
  have hbound := hproj (D * (Clift * M)) (mul_nonneg hD (mul_nonneg hClift hM))
    (F.realFirstCoefficientAdjoint w g.val x)
    (had (Clift * M) (mul_nonneg hClift hM) x (hlift M hM (b.equivFun y) hy))
  have he : F.realFastCoefficientAction w hw U g y = π (F.realFirstCoefficientAdjoint w g.val x) := by
    calc
      _ = F.realFastCoefficientAction w hw U g (π x) := congrArg _ hx.symm
      _ = _ := F.realFastCoefficientAction_mk w hw U g x
  intro i
  rw [he]
  convert hbound i using 1
  ring

theorem fastCoefficientAdjoint_grid (g : F.realFastDiagonalSubgroup w U) (l m n q : ℕ)
    (hlift : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
    (had : ∀ x, F.FirstCoefficientGrid e ω hF w m x →
      F.FirstCoefficientGrid e ω hF w n (F.realFirstCoefficientAdjoint w g.val x))
    (hproj : ∀ x, F.FirstCoefficientGrid e ω hF w n x → b.equivFun (π x) ∈ realDenominatorGrid q)
    (y : F.RealFastCoefficientModule w hw U) (hy : b.equivFun y ∈ realDenominatorGrid l) :
    b.equivFun (F.realFastCoefficientAction w hw U g y) ∈ realDenominatorGrid q := by
  let x := R (b.equivFun y)
  have hx : π x = y := (hR (b.equivFun y)).trans (b.equivFun.symm_apply_apply y)
  have hout := hproj _ (had x (hlift _ hy))
  have he : F.realFastCoefficientAction w hw U g y = π (F.realFirstCoefficientAdjoint w g.val x) := by
    calc
      _ = F.realFastCoefficientAction w hw U g (π x) := congrArg _ hx.symm
      _ = _ := F.realFastCoefficientAction_mk w hw U g x
  rw [he]
  exact hout

end Erdos3.NilpotentLieFiltration

end

end OAI
