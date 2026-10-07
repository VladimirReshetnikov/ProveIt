import OAI.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

theorem scalarFunctionalDenominator_pos (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) :
    0 < matrixDenominator (fun (_ : Unit) i => θ (b i)) :=
  matrixDenominator_pos _

theorem scalarFunctionalDenominator_le (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hθ : ∀ i, RationalHeightLE (θ (b i)) H) :
    matrixDenominator (fun (_ : Unit) i => θ (b i)) ≤ H ^ Fintype.card ι := by
  simpa using matrixDenominator_le (fun (_ : Unit) i => θ (b i)) (fun _ i => hθ i)

theorem realifyFunctional_denominator_grid (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ)
    (m : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid m) :
    ∃ z : ℤ,
      ((matrixDenominator (fun (_ : Unit) i => θ (b i)) * m : ℕ) : ℝ) *
        realifyFunctional θ x = (z : ℝ) := by
  let ℓ : V →ₗ[ℚ] (Unit → ℚ) := LinearMap.pi (fun _ => θ)
  obtain ⟨z, hz⟩ := realifyCoordinateMap_grid b ℓ m x hx
  refine ⟨z (), ?_⟩
  exact (congrFun hz ()).symm

end Erdos3

end

end OAI
