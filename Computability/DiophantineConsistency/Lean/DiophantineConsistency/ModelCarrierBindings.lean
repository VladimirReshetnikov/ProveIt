import DiophantineConsistency.ModelCarrierSyntax
import DiophantineConsistency.CarrierNormalizedProduct106
/-! # The iPRA carrier syntax denotes the accepted polynomials

`ModelCarrierCurrent` states its endpoints for the literal `Expr` syntax of
`ModelCarrierSyntax`. Here that syntax is identified with the accepted integer
polynomials of the external packets, so each endpoint is about exactly the
published equation. This module must not import Foundation: the packets reach
Mathlib's `Matrix.map`, which collides with Foundation's. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelCarrierBindings
open ModelCarrierCurrent

/-- The syntax denotes exactly the accepted 67/106 polynomial. -/
theorem polynomial_expressionAt106 (p : Fin 4 → ℤ) :
    (expressionAt106 p).toPolynomial = CarrierNormalizedProduct106.polynomial p := by
  rw [← Expr.evalRing_X, evalRing_expressionAt106]
  rfl

/-- The syntax denotes exactly the accepted 66/118 polynomial. -/
theorem polynomial_expressionAt118 (p : Fin 4 → ℤ) :
    (expressionAt118 p).toPolynomial = CarrierScaledAuxiliary118.polynomial p := by
  rw [← Expr.evalRing_X, evalRing_expressionAt118]
  rfl

theorem current106 : (expressionAt106 CurrentWindowCarry2011.ports).toPolynomial =
    CarrierNormalizedProduct106.currentPolynomial :=
  polynomial_expressionAt106 _

theorem current118 : (expressionAt118 CurrentWindowCarry2011.ports).toPolynomial =
    CarrierScaledAuxiliary118.currentPolynomial :=
  polynomial_expressionAt118 _

end DiophantineConsistency.ModelCarrierBindings
