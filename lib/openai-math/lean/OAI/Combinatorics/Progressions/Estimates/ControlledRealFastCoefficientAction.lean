import OAI.Combinatorics.Progressions.Estimates.BlockQuotientTriangular
import OAI.Combinatorics.Progressions.Linear.FastCoefficientRelativeKernel
import OAI.Combinatorics.Progressions.Linear.RealFastCoefficientMatrix
import OAI.Combinatorics.Progressions.Linear.RealFastCoefficientQuotientBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem firstCoefficientIndex_grade_eq_of_monomial_eq {σ ι : Type*}
    (w : σ → ℕ) (ω : ι → ℕ) (i j : FirstCoefficientIndex w ω)
    (h : i.val.1 = j.val.1) : ω i.val.2 = ω j.val.2 :=
  i.property.symm.trans ((congrArg (fun α => Finsupp.weight w α + 1) h).trans j.property)

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
  [Fintype κ] [DecidableEq κ] (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_unitriangular
    (rows : κ → FirstCoefficientIndex w ω)
    (b : Basis κ ℝ (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ =
      D.map (Rat.castHom ℝ))
    (hDS : D * S = 1)
    (hDb : ∀ a i, (rows a).val.1 ≠ i.val.1 → D a i = 0)
    (hSb : ∀ i a, i.val.1 ≠ (rows a).val.1 → S i a = 0)
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (a c : κ) (hac : ω (rows a).val.2 ≤ ω (rows c).val.2) :
    LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
      (1 : Matrix κ κ ℝ) a c := by
  rw [F.realFastCoefficientAdjoint_matrix e ω hF w hw U b D S hD hDS g hg]
  apply block_quotient_unitriangular (fun i : FirstCoefficientIndex w ω => ω i.val.2)
    (fun a => ω (rows a).val.2) _ _ _ ?_ ?_ (real_matrix_right_inverse D S hDS) ?_ a c hac
  · intro a i hai
    change (D a i : ℝ) = 0
    have h := hDb a i (fun he => hai (firstCoefficientIndex_grade_eq_of_monomial_eq w ω _ _ he))
    rw [h, Rat.cast_zero]
  · intro i a hia
    change (S i a : ℝ) = 0
    have h := hSb i a (fun he => hia (firstCoefficientIndex_grade_eq_of_monomial_eq w ω _ _ he))
    rw [h, Rat.cast_zero]
  · intro i j hij
    rw [F.realFirstCoefficientAdjoint_matrix_entry e ω hF w g j i hij]
    simp only [Matrix.one_apply, eq_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_real_fast_coefficient_unitriangular_basis
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
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
          (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ = D.map (Rat.castHom ℝ) ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        (∀ y : Fin d → ℝ, b.equivFun.symm y =
          (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
            ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
              (S.map (Rat.castHom ℝ) *ᵥ y))) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have h := F.exists_real_fast_coefficient_quotient_basis e ω hF w hw U.toSubmodule hU
    v hspan hH hv hp hn hm hq hd hdm hHp
  rw [← F.realFirstCoefficientFastSubmodule_relative w hw U] at h
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, hrep⟩ := h
  refine ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, hrep, ?_⟩
  intro g hg a c hac
  exact F.realFastCoefficientAdjoint_unitriangular e ω hF w hw U rows b D S hD hDS
    hDb hSb g hg a c hac

end Erdos3.NilpotentLieFiltration

end

end OAI
