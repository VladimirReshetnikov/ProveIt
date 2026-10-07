import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial MvPolynomial
open scoped TensorProduct

variable {σ ι L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis J ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (k : ℕ) (x : F.RealPolynomialSymbol w) (j : J)

theorem realSymbolGradeQuotientPolynomial_coordinate_homogeneous :
    (coordinate (eQ.coord j).toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF w U k x)).IsWeightedHomogeneous w k := by
  intro α hα
  by_contra hweight
  apply hα
  rw [coeff_coordinate,
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k x α hweight,
    map_zero]

theorem realSymbolGradeQuotientPolynomial_coordinate_component :
    weightedHomogeneousComponent w k
      (coordinate (eQ.coord j).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k x)) =
      coordinate (eQ.coord j).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) :=
  weightedHomogeneousComponent_eq_self
    (F.realSymbolGradeQuotientPolynomial_coordinate_homogeneous b ω hF w U eQ k x j)

theorem realSymbolGradeQuotientPolynomial_coordinate_weightedSupportLE :
    coordinate (eQ.coord j).toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) ∈ weightedSupportLE w k := by
  intro α hα
  exact (F.realSymbolGradeQuotientPolynomial_coordinate_homogeneous b ω hF w U eQ k x j
    (mem_support_iff.mp hα)).le

end Erdos3.NilpotentLieFiltration

end

end OAI
