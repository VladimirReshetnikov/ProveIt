/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
import OAI.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
import OAI.Combinatorics.Progressions.Geometry.ReducedSquareCoefficientCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def realReducedSquareCoefficientMap (w : σ → ℕ) :
    (ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) →ₗ[ℝ]
      F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp
    ((F.reducedSquareCoefficientMap w).baseChange ℝ)

theorem realReducedSquareCoefficientMap_relative (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedSquareCoefficientMap w (F.realReducedRelativeSquareSymbolMap w hw x) =
      F.realNormalizedFirstCoefficientMap w x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    change F.firstCoefficientRealEquiv w
      (r ⊗ₜ[ℚ] F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw x)) =
      F.firstCoefficientRealEquiv w (r ⊗ₜ[ℚ] F.normalizedFirstCoefficientMap w x)
    rw [F.reducedSquareCoefficientMap_relative]

theorem realReducedRelativeCoefficient_eq_map (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.realReducedRelativeCoefficient w hw g =
      F.realReducedSquareCoefficientMap w (F.reducedSquareRealRelativePart w g).coord := by
  obtain ⟨x, hx⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw g
  rw [← hx, F.realReducedSquareCoefficientMap_relative]
  exact (F.realReducedRelativeCoefficient_of_preimage w hw g x hx).symm

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (FirstCoefficientIndex w ω)]

theorem realReducedSquareCoefficientMap_matrix [DecidableEq (ReducedSquareSymbolIndex s w ω)] :
    LinearMap.toMatrix ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
      (F.realFirstCoefficientBasis e ω hF w) (F.realReducedSquareCoefficientMap w) =
      (LinearMap.toMatrix (F.reducedSquareSymbolBasis e ω hF w)
        (F.firstCoefficientBasis e ω hF w) (F.reducedSquareCoefficientMap w)).map
          (Rat.castHom ℝ) := by
  exact scalarExtension_equiv_matrix (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (F.realFirstCoefficientBasis e ω hF w)
    (F.reducedSquareCoefficientMap w) (F.firstCoefficientRealEquiv w)
    (F.firstCoefficientRealEquiv_coordinates e ω hF w)

theorem realReducedSquareCoefficientMap_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T M g) :
    F.FirstCoefficientSlowBound e ω hF w T
      (((Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) + 1) * 2 * M)
      (F.realReducedSquareCoefficientMap w g.coord) := by
  classical
  let D := LinearMap.toMatrix (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (F.reducedSquareCoefficientMap w)
  intro i
  have h := rational_coordinate_map_weighted
    ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
    (F.realFirstCoefficientBasis e ω hF w) (F.realReducedSquareCoefficientMap w)
    D (F.realReducedSquareCoefficientMap_matrix e ω hF w)
    (fun j => j.val.1) (fun j => j.val.1)
    (fun i j hij => by simpa only [D, LinearMap.toMatrix_apply] using
      F.reducedSquareCoefficientMap_monomial_blocks e ω hF w j i hij)
    1 (fun i j => by
      dsimp only [D]
      rw [LinearMap.toMatrix_apply]
      exact_mod_cast (F.reducedSquareCoefficientMap_basis_height e ω hF w j i).1)
    (monomialScale T) (monomialScale_pos T hT) hM g.coord hg i
  simpa only [Basis.equivFun_apply, NNReal.coe_one, one_add_one_eq_two] using h

theorem realReducedSquareCoefficientMap_grid (l : ℕ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l g) :
    F.FirstCoefficientGrid e ω hF w l (F.realReducedSquareCoefficientMap w g.coord) := by
  classical
  let D := LinearMap.toMatrix (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (F.reducedSquareCoefficientMap w)
  have hden : matrixDenominator D = 1 := by
    apply Nat.le_antisymm
    · have hb : ∀ i j, RationalHeightLE (D i j) 1 := by
        intro i j
        simpa only [D, LinearMap.toMatrix_apply] using
          F.reducedSquareCoefficientMap_basis_height e ω hF w j i
      simpa using matrixDenominator_le D hb
    · exact matrixDenominator_pos D
  have h := rational_coordinate_map_grid
    ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
    (F.realFirstCoefficientBasis e ω hF w) (F.realReducedSquareCoefficientMap w)
    D (F.realReducedSquareCoefficientMap_matrix e ω hF w) l g.coord hg
  simpa only [hden, one_mul, FirstCoefficientGrid, Basis.equivFun_apply] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
