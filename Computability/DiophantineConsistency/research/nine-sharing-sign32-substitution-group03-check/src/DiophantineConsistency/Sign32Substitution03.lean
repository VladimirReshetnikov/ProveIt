import DiophantineConsistency.Sign32Substitution02

/-! UNCOMPILED: three more remaining substitution identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution03
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldmainRoot (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 23) - (((Expr.var 17) + (((Expr.var 19) + (Expr.var 18)) * ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 19) + (Expr.var 18))) + (Expr.constant (3 : ℤ))))))

def newmainRoot (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 22) - (((Expr.var 16) + (((Expr.var 18) + (Expr.var 17)) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ))))))

theorem old_mainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 7).head? = some (oldmainRoot p) := by rfl

theorem new_mainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 6).head? = some (newmainRoot p) := by rfl

theorem mainRoot_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldmainRoot p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newmainRoot p).evalRing (fun j => ι (v j)) := by
  simp [oldmainRoot, newmainRoot, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldc2 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 24) - (((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newc2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 23) - (((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_c2_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 8).head? = some (oldc2 p) := by rfl

theorem new_c2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 7).head? = some (newc2 p) := by rfl

theorem c2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldc2 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldc2, newc2, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldDc2 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 25) - ((Expr.var 22) * (Expr.var 24)))

def newDc2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 24) - ((Expr.var 21) * (Expr.var 23)))

theorem old_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 9).head? = some (oldDc2 p) := by rfl

theorem new_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 8).head? = some (newDc2 p) := by rfl

theorem Dc2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldDc2 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newDc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldDc2, newDc2, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign32Substitution03

#print axioms DiophantineConsistency.Sign32Substitution03.old_mainRoot_row
#print axioms DiophantineConsistency.Sign32Substitution03.new_mainRoot_row
#print axioms DiophantineConsistency.Sign32Substitution03.mainRoot_eval
#print axioms DiophantineConsistency.Sign32Substitution03.old_c2_row
#print axioms DiophantineConsistency.Sign32Substitution03.new_c2_row
#print axioms DiophantineConsistency.Sign32Substitution03.c2_eval
#print axioms DiophantineConsistency.Sign32Substitution03.old_Dc2_row
#print axioms DiophantineConsistency.Sign32Substitution03.new_Dc2_row
#print axioms DiophantineConsistency.Sign32Substitution03.Dc2_eval
