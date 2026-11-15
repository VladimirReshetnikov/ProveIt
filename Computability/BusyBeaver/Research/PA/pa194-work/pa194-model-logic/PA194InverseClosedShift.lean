import PA194InverseClosedAt
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194InverseClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)

theorem closedInverseSeparation_shift : closedInverseSeparation.shift = closedInverseSeparation := by
  simp only [closedInverseSeparation,inverseClosedSeparation,closeParameter,inverseProperty,separationFormula]
  inverseSyntax
#print axioms closedInverseSeparation_shift
end PA194InverseClosedTemplate
