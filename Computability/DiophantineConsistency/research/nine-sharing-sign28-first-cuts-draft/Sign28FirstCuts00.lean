import DiophantineConsistency.SharingSign28Squares
import DiophantineConsistency.SharingSign31Squares

/-! UNCOMPILED: removed cut and affected surviving residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28FirstCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 29 → S) : Fin 32 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, (v 9 + 1) * (beta * (v 1 + 1) + 1), v 16, v 17, v 18, v 19, v 20, v 21, (v 18 + (v 11 + 1)) ^ 2, v 22, v 23, v 24, v 25, v 26, v 27, (v 27) ^ 2, v 28]

def oldX (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 16) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

theorem old_X_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 0).head? = some (oldX p) := by rfl

theorem old_X_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (oldX p) (lift beta v) := by
  rw [internalZero_iff]
  simp [oldX, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two, hp0]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 18) - ((Expr.var 16) * (Expr.var 17)))

def newE (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

theorem old_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 2).head? = some (oldE p) := by rfl

theorem new_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 1).head? = some (newE p) := by rfl

theorem E_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldE p).evalRing (fun j => ι (lift beta v j)) = (newE p).evalRing (fun j => ι (v j)) := by
  simp [oldE, newE, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two, hp0]

def oldmainRoot (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 22) - (((Expr.var 16) + (((Expr.var 18) + (Expr.var 17)) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ))))))

def newmainRoot (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 21) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))

theorem old_mainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 6).head? = some (oldmainRoot p) := by rfl

theorem new_mainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 5).head? = some (newmainRoot p) := by rfl

theorem mainRoot_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldmainRoot p).evalRing (fun j => ι (lift beta v j)) = (newmainRoot p).evalRing (fun j => ι (v j)) := by
  simp [oldmainRoot, newmainRoot, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two, hp0]

end DiophantineConsistency.Sign28FirstCuts

#print axioms DiophantineConsistency.Sign28FirstCuts.old_X_row
#print axioms DiophantineConsistency.Sign28FirstCuts.old_X_zero
#print axioms DiophantineConsistency.Sign28FirstCuts.old_E_row
#print axioms DiophantineConsistency.Sign28FirstCuts.new_E_row
#print axioms DiophantineConsistency.Sign28FirstCuts.E_eval
#print axioms DiophantineConsistency.Sign28FirstCuts.old_mainRoot_row
#print axioms DiophantineConsistency.Sign28FirstCuts.new_mainRoot_row
#print axioms DiophantineConsistency.Sign28FirstCuts.mainRoot_eval
