import DiophantineConsistency.NineFreshJones

/-! SOURCE-ONLY staged sign19 residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed19Degree44
def row06 (p : Fin 4 → ℤ) : Expr (Fin 20) :=
  ((Expr.var 18) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 17)) - (((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))
end DiophantineConsistency.SharingSeed19Degree44
