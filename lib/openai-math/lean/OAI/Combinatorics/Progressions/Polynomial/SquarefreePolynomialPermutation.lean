import Mathlib.LinearAlgebra.Pi
import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount

namespace OAI

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreePermute (e : ι ≃ κ) :
    SquarefreePolynomial ι L ≃ₗ[ℚ] SquarefreePolynomial κ L :=
  squarefreePolynomialEquiv.trans
    ((LinearEquiv.funCongrLeft ℚ L (SquarefreeIndex.permute e).symm).trans
      squarefreePolynomialEquiv.symm)

theorem squarefreePermute_coefficient (e : ι ≃ κ) (x : SquarefreePolynomial ι L)
    (a : SquarefreeIndex κ) :
    squarefreePolynomialEquiv (squarefreePermute e x) a =
      squarefreePolynomialEquiv x ((SquarefreeIndex.permute e).symm a) := by
  change squarefreePolynomialEquiv (squarefreePolynomialEquiv.symm _) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem squarefreePermute_monomial (e : ι ≃ κ) (a : SquarefreeIndex ι) (v : L) :
    squarefreePermute e (squarefreeMonomial a v) =
      squarefreeMonomial (SquarefreeIndex.permute e a) v := by
  apply squarefreePolynomialEquiv.injective
  ext b
  obtain ⟨b, rfl⟩ := (SquarefreeIndex.permute e).surjective b
  rw [squarefreePermute_coefficient, Equiv.symm_apply_apply]
  by_cases h : a = b
  · subst b
    rw [squarefreePolynomialEquiv_monomial_self, squarefreePolynomialEquiv_monomial_self]
  · rw [squarefreePolynomialEquiv_monomial_ne a b h,
      squarefreePolynomialEquiv_monomial_ne _ _
        (fun he => h ((SquarefreeIndex.permute e).injective he))]

theorem squarefreePermute_symm_apply (e : ι ≃ κ) (x : SquarefreePolynomial ι L) :
    squarefreePermute e.symm (squarefreePermute e x) = x := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient, squarefreePermute_coefficient]
  change squarefreePolynomialEquiv x
    ((SquarefreeIndex.permute e).symm (SquarefreeIndex.permute e a)) = _
  rw [Equiv.symm_apply_apply]

end Erdos3

end

end OAI
