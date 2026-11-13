import DiophantineConsistency.NineFreshJones

/-! SOURCE-ONLY staged sign19 residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed19Degree44
def row08 (p : Fin 4 → ℤ) : Expr (Fin 20) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 15) * ((Expr.var 15) + (Expr.constant (2 : ℤ))))) * (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 15) * ((Expr.var 15) + (Expr.constant (2 : ℤ)))))) * (Expr.var 19))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed19Degree44
