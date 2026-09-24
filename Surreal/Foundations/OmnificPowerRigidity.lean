import Surreal.Foundations.OmnificPolynomialRoots

/-!
# Ordinary positive powers force ordinary omnific bases

The univariate step in `odg:rem:powers` (also labeled `odg:cor:powers`).
Use the established polynomial-root theorem with X^n-a, retaining n > 0.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- An actual omnific integer whose positive power is ordinary is itself ordinary. -/
theorem omnific_eq_intConstant_of_pow (x : OmnificInteger.{u}) (n : ℕ) (hn : 0 < n)
    (a : ℤ) (h : x ^ n = omnificIntCast a) :
    x = omnificIntCast (omnificConstantCoeff x) := by
  have hp : (Polynomial.X ^ n - Polynomial.C a : Polynomial ℤ).eval₂ omnificIntCast x = 0 := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, h, sub_self]
  obtain ⟨b, hb, _⟩ := (omnific_int_polynomial_root_iff _
    (Polynomial.X_pow_sub_C_ne_zero hn a) x).mp hp
  rw [hb, omnificConstantCoeff_intCast]

end
end Surreal.Foundations.SignSequence
