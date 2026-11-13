import DiophantineConsistency.Sign32Substitution04

/-! UNCOMPILED: three more remaining substitution identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution05
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldN0 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((((Expr.var 27) * (Expr.var 27)) - ((Expr.var 21) * ((Expr.var 21) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newN0 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((Expr.var 26) * (Expr.var 26)) - ((Expr.var 20) * ((Expr.var 20) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 13).head? = some (oldN0 p) := by rfl

theorem new_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 12).head? = some (newN0 p) := by rfl

theorem N0_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldN0 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newN0 p).evalRing (fun j => ι (v j)) := by
  simp [oldN0, newN0, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldNt (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newNt (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 14).head? = some (oldNt p) := by rfl

theorem new_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 13).head? = some (newNt p) := by rfl

theorem Nt_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldNt p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newNt p).evalRing (fun j => ι (v j)) := by
  simp [oldNt, newNt, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldf2 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 28) - (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))))

def newf2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 27) - (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))))

theorem old_f2_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 15).head? = some (oldf2 p) := by rfl

theorem new_f2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 14).head? = some (newf2 p) := by rfl

theorem f2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldf2 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newf2 p).evalRing (fun j => ι (v j)) := by
  simp [oldf2, newf2, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign32Substitution05

#print axioms DiophantineConsistency.Sign32Substitution05.old_N0_row
#print axioms DiophantineConsistency.Sign32Substitution05.new_N0_row
#print axioms DiophantineConsistency.Sign32Substitution05.N0_eval
#print axioms DiophantineConsistency.Sign32Substitution05.old_Nt_row
#print axioms DiophantineConsistency.Sign32Substitution05.new_Nt_row
#print axioms DiophantineConsistency.Sign32Substitution05.Nt_eval
#print axioms DiophantineConsistency.Sign32Substitution05.old_f2_row
#print axioms DiophantineConsistency.Sign32Substitution05.new_f2_row
#print axioms DiophantineConsistency.Sign32Substitution05.f2_eval
