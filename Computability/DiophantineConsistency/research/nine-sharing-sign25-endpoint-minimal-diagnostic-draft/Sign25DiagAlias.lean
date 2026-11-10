import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY diagnostic: the typed alias without irreducibility attributes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25EndpointDiagnosticMinimal
open AdaptiveEquationSyntax2011
def expression : Expr (Fin 25) := Sign25CurrentExpression.expression
end DiophantineConsistency.Sign25EndpointDiagnosticMinimal
