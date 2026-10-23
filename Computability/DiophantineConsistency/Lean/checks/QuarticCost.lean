import DiophantineConsistency.QuarticCost

open DiophantineConsistency

example : ((Expr.var (0 : Fin 1) + Expr.var 0) * Expr.var 0).binaryOps = 2 := rfl

#print axioms Expr.binaryOps_rename
#print axioms Expr.binaryOps_subst_atoms
#print axioms QuarticCost.gate_residual_binaryOps
#print axioms QuarticCost.residual_binaryOps
#print axioms QuarticCost.sumExpressions_binaryOps_le
#print axioms QuarticCost.expression_binaryOps_le
