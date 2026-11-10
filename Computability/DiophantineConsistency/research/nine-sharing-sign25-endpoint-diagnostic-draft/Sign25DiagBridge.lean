import DiophantineConsistency.Sign25DiagExpression

/-! SOURCE-ONLY diagnostic: add the candidate named expression bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25EndpointDiagnostic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression SharingSeed25Octic.seed CurrentWindowCarry2011.ports

theorem expression_bridge : HAExpressionAssembly.PolynomialBridge expression :=
  Sign25DirectIPRA.polynomialBridge
end DiophantineConsistency.Sign25EndpointDiagnostic
