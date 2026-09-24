import Diophantine.Paper1982.ShortQuadratic

/-!
# Positive solutions of the explicit quadratic system

The input is separate from the 58 positive natural witnesses. This interface
is shared by the substitutions in both directions and by the conversion to
the ordinary `Fin 59` polynomial representation.
-/

namespace Jones1982.ShortQuadraticExpr

/- Explicit operator lemmas let the simplifier interpret notation without
unfolding the ring-homomorphism implementation of polynomial evaluation. -/

theorem toPolynomial_add (p q : ShortQuadraticExpr) :
    (p + q).toPolynomial = p.toPolynomial + q.toPolynomial := rfl

theorem toPolynomial_sub (p q : ShortQuadraticExpr) :
    (p - q).toPolynomial = p.toPolynomial - q.toPolynomial := rfl

theorem toPolynomial_mul (p q : ShortQuadraticExpr) :
    (p * q).toPolynomial = p.toPolynomial * q.toPolynomial := rfl

theorem toPolynomial_pow (p : ShortQuadraticExpr) (n : ℕ) :
    (p ^ n).toPolynomial = p.toPolynomial ^ n := rfl

theorem toPolynomial_ofNat (n : ℕ) :
    (@OfNat.ofNat ShortQuadraticExpr n (instOfNat n)).toPolynomial =
      MvPolynomial.C (n : ℤ) := rfl

end Jones1982.ShortQuadraticExpr

namespace Jones1982.ShortQuadratic

/-- Evaluate the input at `x` and the named witnesses at `v`. -/
def assignment (x : ℕ) (v : ShortQuadraticVar → ℕ) :
    Option ShortQuadraticVar → ℤ
  | none => x
  | some idx => v idx

/-- A positive natural solution of all 46 explicit quadratic equations. -/
structure PositiveWitnesses (x z u y L : ℕ) where
  val : ShortQuadraticVar → ℕ
  pos : ∀ idx, 0 < val idx
  equations : ∀ i : ShortQuadraticEquation,
    MvPolynomial.eval (assignment x val) (residual z u y L i) = 0

end Jones1982.ShortQuadratic
