/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def realSquarefreePolynomialEquiv :
    (ℝ ⊗[ℚ] SquarefreePolynomial ι L) ≃ₗ[ℝ] (SquarefreeIndex ι → ℝ ⊗[ℚ] L) := by
  classical
  exact ((squarefreePolynomialEquiv (ι := ι) (L := L)).baseChange ℚ ℝ _ _).trans
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : SquarefreeIndex ι => L))

theorem realSquarefreePolynomialEquiv_tmul (r : ℝ) (x : SquarefreePolynomial ι L)
    (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (r ⊗ₜ[ℚ] x) c = r ⊗ₜ[ℚ] squarefreePolynomialEquiv x c := rfl

theorem realSquarefreeMonomial_self (a : SquarefreeIndex ι) (x : ℝ ⊗[ℚ] L) :
    realSquarefreePolynomialEquiv ((squarefreeMonomial a).baseChange ℝ x) a = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      squarefreePolynomialEquiv_monomial_self]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realSquarefreeMonomial_ne (a c : SquarefreeIndex ι) (hac : a ≠ c) (x : ℝ ⊗[ℚ] L) :
    realSquarefreePolynomialEquiv ((squarefreeMonomial a).baseChange ℝ x) c = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      squarefreePolynomialEquiv_monomial_ne a c hac, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]

end Erdos3

end

end OAI
