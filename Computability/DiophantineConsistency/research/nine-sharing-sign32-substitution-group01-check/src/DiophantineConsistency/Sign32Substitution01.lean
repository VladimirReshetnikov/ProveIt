import DiophantineConsistency.Sign32Substitution00

/-! UNCOMPILED: first three remaining substitution identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution01
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldX (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 17) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

def newX (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 16) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

theorem old_X_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 1).head? = some (oldX p) := by rfl

theorem new_X_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 0).head? = some (newX p) := by rfl

theorem X_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldX p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newX p).evalRing (fun j => ι (v j)) := by
  simp [oldX, newX, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldY (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 18) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 16)))

def newY (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 17) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

theorem old_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 2).head? = some (oldY p) := by rfl

theorem new_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 1).head? = some (newY p) := by rfl

theorem Y_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldY p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newY p).evalRing (fun j => ι (v j)) := by
  simp [oldY, newY, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

def newE (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 18) - ((Expr.var 16) * (Expr.var 17)))

theorem old_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 3).head? = some (oldE p) := by rfl

theorem new_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 2).head? = some (newE p) := by rfl

theorem E_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldE p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newE p).evalRing (fun j => ι (v j)) := by
  simp [oldE, newE, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign32Substitution01

#print axioms DiophantineConsistency.Sign32Substitution01.old_X_row
#print axioms DiophantineConsistency.Sign32Substitution01.new_X_row
#print axioms DiophantineConsistency.Sign32Substitution01.X_eval
#print axioms DiophantineConsistency.Sign32Substitution01.old_Y_row
#print axioms DiophantineConsistency.Sign32Substitution01.new_Y_row
#print axioms DiophantineConsistency.Sign32Substitution01.Y_eval
#print axioms DiophantineConsistency.Sign32Substitution01.old_E_row
#print axioms DiophantineConsistency.Sign32Substitution01.new_E_row
#print axioms DiophantineConsistency.Sign32Substitution01.E_eval
