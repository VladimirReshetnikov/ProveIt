import DiophantineConsistency.Sign25DiagImport

/-! SOURCE-ONLY diagnostic: add only the endpoint expression alias. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25EndpointDiagnostic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression SharingSeed25Octic.seed CurrentWindowCarry2011.ports

def expression : Expr (Fin 25) := Sign25CurrentExpression.expression
end DiophantineConsistency.Sign25EndpointDiagnostic
