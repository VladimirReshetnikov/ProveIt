import DiophantineConsistency.Sign14Positive74DegreeTranslation
import DiophantineConsistency.Sign14Positive74DegreeIdentity
import DiophantineConsistency.Sign14Optimized86Degree

/-! SOURCE ONLY: exact total degree of the current Lean positive74 expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74DegreeExact
open Sign14Positive74DegreeTranslation

def expression : Expr (Fin 14) :=
  Sign14Positive74.expression CurrentWindowCarry2011.ports

theorem totalDegree_eq : expression.toPolynomial.totalDegree = 124 := by
  have hp : translate expression.toPolynomial = Sign14Optimized86Current.expression.toPolynomial := by
    simpa only [expression, translate, plusOne, Sign14Optimized86Current.expression] using
      Sign14Positive74DegreeIdentity.shifted_polynomial CurrentWindowCarry2011.ports
  calc
    expression.toPolynomial.totalDegree = (translate expression.toPolynomial).totalDegree :=
      (translate_degree _).symm
    _ = 124 := by rw [hp]; exact Sign14Optimized86Current.totalDegree_eq
end DiophantineConsistency.Sign14Positive74DegreeExact
#print axioms DiophantineConsistency.Sign14Positive74DegreeExact.totalDegree_eq
