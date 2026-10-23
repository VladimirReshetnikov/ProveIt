import DiophantineConsistency.GraphSizeBounds

open DiophantineConsistency

namespace DiophantineConsistency.RepresentationSizeChecks

def quadratic : NatExpr (Fin 2) := (.var 0 + .constant 3) * (.var 1 + .constant 5)

example : quadratic.graphRep.witnessCount = 6 := by
  have h := NatExpr.graphRep_witnessCount quadratic
  change quadratic.graphRep.witnessCount + 1 = 7 at h
  omega

example : quadratic.graphRep.depth ≤ 13 := by
  exact NatExpr.graphRep_depth_le quadratic

example : Expr.splitSize (Expr.var (0 : Fin 1) * Expr.var 0) = 14 := rfl

#print axioms Expr.splitSize_eq
#print axioms NatExpr.count_le_pow_depth
#print axioms Expr.splitNatural_depth_le
#print axioms Expr.splitSize_le_pow_depth
#print axioms Rep.allFin_depth_le
#print axioms Rep.compacted_variables_le
#print axioms Rep.rawQuarticVariables_le
#print axioms NatExpr.graphRep_witnessCount
#print axioms NatExpr.graphRep_depth_le
#print axioms Rep.compose_depth_le
#print axioms GraphRep.composeDirect_depth_le
#print axioms GraphRep.compose_depth_le
#print axioms GraphRep.thin_composeDirect
#print axioms GraphRep.thin_compose
#print axioms GraphRep.thin_add
#print axioms ScaledNatural.depth_cantorPair

end DiophantineConsistency.RepresentationSizeChecks
