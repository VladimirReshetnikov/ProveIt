import DiophantineConsistency.Sign28FirstCuts00

/-! UNCOMPILED: removed cut and affected surviving residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28FirstCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldc2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 23) - (((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_c2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 7).head? = some (oldc2 p) := by rfl

theorem old_c2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    InternalZero (oldc2 p) (lift beta v) := by
  rw [internalZero_iff]
  simp [oldc2, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

def oldDc2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 24) - ((Expr.var 21) * (Expr.var 23)))

def newDc2 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 22) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

theorem old_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 8).head? = some (oldDc2 p) := by rfl

theorem new_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 6).head? = some (newDc2 p) := by rfl

theorem Dc2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldDc2 p).evalRing (fun j => ι (lift beta v j)) = (newDc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldDc2, newDc2, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

end DiophantineConsistency.Sign28FirstCuts

#print axioms DiophantineConsistency.Sign28FirstCuts.old_c2_row
#print axioms DiophantineConsistency.Sign28FirstCuts.old_c2_zero
#print axioms DiophantineConsistency.Sign28FirstCuts.old_Dc2_row
#print axioms DiophantineConsistency.Sign28FirstCuts.new_Dc2_row
#print axioms DiophantineConsistency.Sign28FirstCuts.Dc2_eval
