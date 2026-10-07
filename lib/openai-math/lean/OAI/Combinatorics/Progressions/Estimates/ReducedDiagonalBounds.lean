import OAI.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
import OAI.Combinatorics.Progressions.Linear.ReducedProjectionBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareDiagonal_basis (a : QuotientTopBasisIndex s ω) :
    F.reducedSquareDiagonal (F.quotientTopBasis e ω hF a) =
      F.reducedSquareBasis e ω hF (reducedSquareDiagonalIndex s ω a) := by
  rw [F.quotientTopBasis_apply, F.reducedSquareDiagonal_mk]
  change _ = F.squareFiltration.quotientTopBasis (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF) _
  rw [F.squareFiltration.quotientTopBasis_apply]
  congr 1
  apply Subtype.ext
  exact (F.adaptedSquareBasis_inl e ω (hF 2) a.val).symm

theorem reducedSquareDiagonal_basis_height
    (a : QuotientTopBasisIndex s ω) (b : ReducedSquareBasisIndex s ω) :
    RationalHeightLE ((F.reducedSquareBasis e ω hF).repr
      (F.reducedSquareDiagonal (F.quotientTopBasis e ω hF a)) b) 1 := by
  rw [F.reducedSquareDiagonal_basis]
  exact basis_repr_height_one (F.reducedSquareBasis e ω hF) _ _

theorem reducedSquareDiagonalSymbolMap_basis_height (w : σ → ℕ)
    (a : QuotientTopSymbolIndex s w ω) (b : ReducedSquareSymbolIndex s w ω) :
    RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr
      (F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolBasis e ω hF w a)) b) 1 :=
  filteredPolynomialSymbolMap_basis_height F.quotientTop F.squareFiltration.quotientTop
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF) F.reducedSquareDiagonal F.reducedSquareDiagonal_mem
    w le_rfl (fun i j => F.reducedSquareDiagonal_basis_height e ω hF j i) a b

theorem reducedSquareDiagonalSymbolMap_monomial_blocks (w : σ → ℕ)
    (a : QuotientTopSymbolIndex s w ω) (b : ReducedSquareSymbolIndex s w ω)
    (hab : b.val.1 ≠ a.val.1) :
    (F.reducedSquareSymbolBasis e ω hF w).repr
      (F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolBasis e ω hF w a)) b = 0 :=
  filteredPolynomialSymbolMap_monomial_blocks F.quotientTop F.squareFiltration.quotientTop
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF) F.reducedSquareDiagonal F.reducedSquareDiagonal_mem
    w a b hab

variable (w : σ → ℕ) [Fintype (QuotientTopSymbolIndex s w ω)]
  [Fintype (ReducedSquareSymbolIndex s w ω)]

theorem reducedSquareRealDiagonalHom_coord
    (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealDiagonalHom w g).coord =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ g.coord := rfl

theorem reducedSquareDiagonalSymbolMap_real_matrix
    [DecidableEq (QuotientTopSymbolIndex s w ω)] :
    LinearMap.toMatrix ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ)
      ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
        ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ) =
      (LinearMap.toMatrix (F.quotientTopSymbolBasis e ω hF w)
        (F.reducedSquareSymbolBasis e ω hF w) (F.reducedSquareDiagonalSymbolMap w).toLinearMap).map
          (Rat.castHom ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, linearMap_baseChange_basis]
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Rat.coe_castHom]

theorem reducedSquareRealDiagonalHom_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T M g) :
    F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
      (((Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) + 1) * 2 * M)
      (F.reducedSquareRealDiagonalHom w g) := by
  classical
  let D := LinearMap.toMatrix (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSymbolBasis e ω hF w) (F.reducedSquareDiagonalSymbolMap w).toLinearMap
  intro i
  have h := rational_coordinate_map_weighted
    ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ)
    ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ)
    ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ)
    D (F.reducedSquareDiagonalSymbolMap_real_matrix e ω hF w)
    (fun j => j.val.1) (fun j => j.val.1)
    (fun i j hij => by
      dsimp only [D]
      rw [LinearMap.toMatrix_apply]
      exact F.reducedSquareDiagonalSymbolMap_monomial_blocks e ω hF w j i hij)
    1 (fun i j => by
      dsimp only [D]
      rw [LinearMap.toMatrix_apply]
      exact_mod_cast (F.reducedSquareDiagonalSymbolMap_basis_height e ω hF w j i).1)
    (monomialScale T) (monomialScale_pos T hT) hM g.coord hg i
  change |((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).repr
    (F.reducedSquareRealDiagonalHom w g).coord i| ≤ _
  rw [F.reducedSquareRealDiagonalHom_coord]
  simpa only [Basis.equivFun_apply, NNReal.coe_one, one_add_one_eq_two] using h

theorem reducedSquareRealDiagonalHom_grid (l : ℕ)
    (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l g) :
    F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l
      (F.reducedSquareRealDiagonalHom w g) := by
  change (fun z => ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).repr
    (F.reducedSquareRealDiagonalHom w g).coord z) ∈
      realDenominatorGrid l
  rw [F.reducedSquareRealDiagonalHom_coord]
  exact scalarExtension_grid_of_height_one (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSymbolBasis e ω hF w) (F.reducedSquareDiagonalSymbolMap w).toLinearMap
    (fun i j => F.reducedSquareDiagonalSymbolMap_basis_height e ω hF w j i) l g.coord hg

end Erdos3.NilpotentLieFiltration

end

end OAI
