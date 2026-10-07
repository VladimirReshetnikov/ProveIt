import OAI.Combinatorics.Progressions.Estimates.AllocatedFiberCap
import OAI.Combinatorics.Progressions.Estimates.OneSiteCoefficientFactorization

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientResidualFunctional {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : CoefficientArray (K := K) U →ₗ[ℝ] ℝ :=
  (coefficientArrayFunctional U frequency).comp (coefficientResidualArray U t)

theorem coefficientResidualFunctional_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    ∃ n : ℤ, coefficientResidualFunctional U t frequency x = n :=
  coefficientArrayFunctional_integral U frequency _
    (coefficientResidualArray_preserves_lattice U t x hx)

theorem coefficientTorusCharacter_fiber {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (coefficientFiberMap U t y x) =
      coefficientTorusCharacter U frequency (constantCoefficientTorusMap U y) *
        quotientLinearCharacter (coefficientIntegerLattice U) (coefficientResidualFunctional U t frequency)
          (coefficientResidualFunctional_integral U t frequency) x := by
  unfold coefficientFiberMap
  change quotientLinearCharacter _ _ _ (_ + _) = _
  rw [quotientLinearCharacter_add]
  congr 1
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientEvaluationTorus_mk, constantCoefficientTorusMap_mk, ← map_sub]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
