import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def reducedSquareDiagonalIndex (s : ℕ) (ω : ι → ℕ)
    (i : QuotientTopBasisIndex s ω) : ReducedSquareBasisIndex s ω :=
  ⟨Sum.inl i.val, i.property⟩

def reducedSquareDiagonalSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ)
    (z : QuotientTopSymbolIndex s w ω) : ReducedSquareSymbolIndex s w ω :=
  ⟨(z.val.1, reducedSquareDiagonalIndex s ω z.val.2), z.property⟩

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareSnd_basis_repr [DecidableEq ι]
    (a : ReducedSquareBasisIndex s ω) (b : QuotientTopBasisIndex s ω) :
    (F.quotientTopBasis e ω hF).repr
      (F.reducedSquareSnd (F.reducedSquareBasis e ω hF a)) b =
      if a = reducedSquareDiagonalIndex s ω b then 1 else 0 := by
  classical
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareSnd_mk,
    F.quotientTopBasis_repr_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i =>
    change e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inl i)).val.2) b.val = _
    rw [F.adaptedSquareBasis_inl]
    simp [reducedSquareDiagonalIndex, Basis.repr_self, Finsupp.single_apply,
      Subtype.ext_iff]
  | inr i =>
    change e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inr i)).val.2) b.val = _
    rw [F.adaptedSquareBasis_inr]
    simp [reducedSquareDiagonalIndex, Subtype.ext_iff]

theorem reducedSquareSndSymbolMap_basis_repr [DecidableEq σ] [DecidableEq ι] (w : σ → ℕ)
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω) :
    (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b =
      if a = reducedSquareDiagonalSymbolIndex s w ω b then 1 else 0 := by
  classical
  change (F.quotientTop.polynomialSymbolBasis _ _ _ w).repr
    (F.squareFiltration.quotientTop.filteredPolynomialSymbolMap F.quotientTop
      F.reducedSquareSnd F.reducedSquareSnd_mem w
      (F.squareFiltration.quotientTop.polynomialSymbolBasis _ _ _ w a)) b = _
  rw [filteredPolynomialSymbolMap_basis_repr, F.reducedSquareSnd_basis_repr e ω hF]
  simp [reducedSquareDiagonalSymbolIndex, Subtype.ext_iff, Prod.ext_iff, ite_and]

theorem reducedSquareSndSymbolMap_repr (w : σ → ℕ)
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (b : QuotientTopSymbolIndex s w ω) :
    (F.quotientTopSymbolBasis e ω hF w).repr (F.reducedSquareSndSymbolMap w x) b =
      (F.reducedSquareSymbolBasis e ω hF w).repr x
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
  classical
  have h : ((F.quotientTopSymbolBasis e ω hF w).coord b).comp
      (F.reducedSquareSndSymbolMap w).toLinearMap =
      (F.reducedSquareSymbolBasis e ω hF w).coord
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
    apply (F.reducedSquareSymbolBasis e ω hF w).ext
    intro a
    change (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b = _
    rw [F.reducedSquareSndSymbolMap_basis_repr e ω hF]
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  exact DFunLike.congr_fun h x

theorem reducedSquareRealSymbolHom_repr (w : σ → ℕ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (b : QuotientTopSymbolIndex s w ω) :
    ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
        (F.reducedSquareRealSymbolHom w g).coord b =
      ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).repr g.coord
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
  classical
  have h : (((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).coord b).comp
      ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) =
      ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).coord
        (reducedSquareDiagonalSymbolIndex s w ω b) := by
    apply ((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ).ext
    intro a
    change ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
      ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
        (((F.reducedSquareSymbolBasis e ω hF w).baseChange ℝ) a)) b = _
    rw [linearMap_baseChange_basis]
    change ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b : ℝ) = _
    rw [F.reducedSquareSndSymbolMap_basis_repr e ω hF]
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num
  exact DFunLike.congr_fun h g.coord

theorem reducedSquareRealSymbolHom_slow (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T M g) :
    F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T M
      (F.reducedSquareRealSymbolHom w g) := by
  intro b
  change |((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
    (F.reducedSquareRealSymbolHom w g).coord b| ≤ _
  rw [F.reducedSquareRealSymbolHom_repr e ω hF]
  exact hg (reducedSquareDiagonalSymbolIndex s w ω b)

theorem reducedSquareRealSymbolHom_grid (w : σ → ℕ) (l : ℕ)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l g) :
    F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
      (F.reducedSquareRealSymbolHom w g) := by
  obtain ⟨z, hz⟩ := hg
  refine ⟨fun b => z (reducedSquareDiagonalSymbolIndex s w ω b), ?_⟩
  funext b
  change (z (reducedSquareDiagonalSymbolIndex s w ω b) : ℝ) =
    (l : ℝ) * ((F.quotientTopSymbolBasis e ω hF w).baseChange ℝ).repr
      (F.reducedSquareRealSymbolHom w g).coord b
  rw [F.reducedSquareRealSymbolHom_repr e ω hF]
  exact congrFun hz (reducedSquareDiagonalSymbolIndex s w ω b)

end Erdos3.NilpotentLieFiltration

end

end OAI
