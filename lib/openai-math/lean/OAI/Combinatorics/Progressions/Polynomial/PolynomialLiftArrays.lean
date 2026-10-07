import OAI.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace VectorPolynomial

noncomputable def assembleFamily {σ κ R V : Type*} [Fintype κ] [CommRing R]
    [AddCommGroup V] [Module R V] (P : κ → VectorPolynomial σ R V) :
    VectorPolynomial σ R (κ → V) := by
  classical
  exact ∑ k, map (LinearMap.single R (fun _ : κ => V) k) (P k)

@[simp] theorem coefficients_assembleFamily {σ κ R V : Type*} [Fintype κ] [CommRing R]
    [AddCommGroup V] [Module R V] (P : κ → VectorPolynomial σ R V) (α : σ →₀ ℕ) (k : κ) :
    coefficients (assembleFamily P) α k = coefficients (P k) α := by
  classical
  simp [assembleFamily, LinearMap.single_apply, Pi.single_apply]

end VectorPolynomial

open VectorPolynomial

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

noncomputable def liftQuotientArray (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) : VectorPolynomial σ ℚ (κ × ι → ℝ) :=
  assembleFamily (fun bi : κ × ι => map
    (((LinearMap.proj bi.2).comp (realQuotientCoordinateMap f)).restrictScalars ℚ) (S bi.1))

@[simp] theorem coefficients_liftQuotientArray (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) (bi : κ × ι) :
    coefficients (liftQuotientArray f S) α bi = realQuotientCoordinateMap f (coefficients (S bi.1) α) bi.2 := by
  rw [liftQuotientArray, coefficients_assembleFamily, coefficients_map]
  rfl

theorem liftQuotientArray_coefficient_eq_zero (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ)
    (hS : ∀ t, coefficients (S t) α = 0) : coefficients (liftQuotientArray f S) α = 0 := by
  funext bi
  rw [coefficients_liftQuotientArray, hS, map_zero]
  rfl

theorem bracket_system_matches_lift_array (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (A : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (h : map ((realBracketSystem f k).restrictScalars ℚ) A = liftQuotientArray f S) :
    ∀ t α, coefficients (S t - ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ := by
  intro t α
  apply (realQuotientCoordinateMap_eq_zero_iff f _).mp
  funext i
  have hi := congrArg (fun P : VectorPolynomial σ ℚ (κ × ι → ℝ) => coefficients P α (t, i)) h
  simp only [coefficients_map, LinearMap.restrictScalars_apply,
    coefficients_liftQuotientArray, realBracketSystem_apply] at hi
  rw [map_sub, Finsupp.sub_apply, coefficients_lie_constant, map_sub, Pi.sub_apply]
  exact sub_eq_zero.mpr hi.symm

end Erdos3

end

end OAI
