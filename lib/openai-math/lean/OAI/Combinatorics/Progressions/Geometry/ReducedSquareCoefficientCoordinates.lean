/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FastCoefficientImage

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareDifference_basis_height (a : ReducedSquareBasisIndex s ω) (i : ι) :
    RationalHeightLE (e.repr (F.reducedSquareDifference (F.reducedSquareBasis e ω hF a)) i) 1 := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareDifference_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl j =>
    rw [F.adaptedSquareBasis_inl, sub_self, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  | inr j =>
    rw [F.adaptedSquareBasis_inr, sub_zero]
    exact basis_repr_height_one e j.val i

theorem reducedSquareCoefficientMap_repr_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (i : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) i =
      e.repr (F.reducedSquareDifference (coefficients p.val i.val.1)) i.val.2 := by
  rw [F.reducedSquareCoefficientMap_symbol]
  change (F.firstCoefficientBasis e ω hF w).repr
    (F.firstCoefficientMap w ⟨(F.reducedSquareDifferenceRelative w p).val, _⟩) i = _
  rw [F.firstCoefficientBasis_repr_map, F.reducedSquareDifferenceRelative_coefficient]

theorem reducedSquareCoefficientMap_basis_repr [DecidableEq σ]
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i =
      if a.val.1 = i.val.1 then
        e.repr (F.reducedSquareDifference (F.reducedSquareBasis e ω hF a.val.2)) i.val.2 else 0 := by
  change (F.firstCoefficientBasis e ω hF w).repr
    (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolBasis (F.reducedSquareBasis e ω hF)
        (fun j => squareBasisWeight ω j.val) (F.reducedSquareBasis_layers e ω hF) w a)) i = _
  rw [F.squareFiltration.quotientTop.polynomialSymbolBasis_apply,
    F.reducedSquareCoefficientMap_repr_symbol, F.squareFiltration.quotientTop.adaptedMonomialBasis_coe,
    coefficients_monomial]
  by_cases hai : a.val.1 = i.val.1
  · simp only [hai, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hai), map_zero, map_zero,
      Finsupp.zero_apply, ite_eq_right hai]

theorem reducedSquareCoefficientMap_basis_height
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) :
    RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i) 1 := by
  classical
  rw [F.reducedSquareCoefficientMap_basis_repr]
  split_ifs
  · exact F.reducedSquareDifference_basis_height e ω hF a.val.2 i.val.2
  · exact rationalHeightLE_zero le_rfl

theorem reducedSquareCoefficientMap_monomial_blocks
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) (hai : i.val.1 ≠ a.val.1) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i = 0 := by
  classical
  rw [F.reducedSquareCoefficientMap_basis_repr, ite_eq_right (Ne.symm hai)]

end Erdos3.NilpotentLieFiltration

end

end OAI
