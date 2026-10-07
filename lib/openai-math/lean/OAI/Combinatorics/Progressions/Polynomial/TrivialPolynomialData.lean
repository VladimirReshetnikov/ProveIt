import OAI.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_one (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) : F.PolynomialSlowBound b w T M 1 := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ _
  simp only [map_zero, Finsupp.zero_apply, abs_zero]
  exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialRationalGrid_one (q : ℕ) : F.PolynomialRationalGrid b w q 1 := by
  refine ⟨fun _ => 0, ?_⟩
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_zero]
  change (0 : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
    (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  simp only [map_zero, Finsupp.zero_apply, mul_zero]

theorem piRealOrbit_one {κ : Type*} [Fintype κ] {L : κ → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {σ : Type*} (w : σ → ℕ) :
    piRealOrbit F (fun _ => (1 : (F _).realification.PolynomialOrbit w)) = 1 := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
    (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L i))) = 0
  simp only [map_zero, Finset.sum_const_zero]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem const_zero_complexity_of {T : D.Niltest w} {p : ℝ} (hT : T.ComplexityLE p) :
    (const D w 0).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
  exact (Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ 2 + T.normBound + T.lipBound by
      linarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg])).trans hT.2

theorem const_zero_unit_interval (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) :
    (const D w 0).UnitIntervalValued := by
  intro x
  simp only [const, Complex.zero_im, Complex.zero_re, le_refl, zero_le_one, and_self]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
