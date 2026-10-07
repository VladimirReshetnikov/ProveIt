/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.StdBasis
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial

@[simp] theorem coefficients_ofCoordinates_pi_apply {X K : Type*} [Fintype K]
    (p : K → MvPolynomial X ℝ) (α : X →₀ ℕ) (i : K) :
    coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ K) p) α i =
      (p i).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial X ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := ℝ) (Pi.basisFun ℝ K) p i)
  rw [coeff_coordinate] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
