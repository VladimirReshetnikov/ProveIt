import DiophantineConsistency.Sign32Substitution03

/-! UNCOMPILED: N1/gap/tau substitution; tau uses the reconstructed q². -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution04
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldN1 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((((Expr.var 23) * (Expr.var 23)) - (Expr.var 25)) - (Expr.constant (1 : ℤ)))

def newN1 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((Expr.var 22) * (Expr.var 22)) - (Expr.var 24)) - (Expr.constant (1 : ℤ)))

theorem old_N1_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 10).head? = some (oldN1 p) := by rfl

theorem new_N1_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 9).head? = some (newN1 p) := by rfl

theorem N1_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldN1 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newN1 p).evalRing (fun j => ι (v j)) := by
  simp [oldN1, newN1, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldgap (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 26) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

def newgap (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 25) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

theorem old_gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 11).head? = some (oldgap p) := by rfl

theorem new_gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 10).head? = some (newgap p) := by rfl

theorem gap_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldgap p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newgap p).evalRing (fun j => ι (v j)) := by
  simp [oldgap, newgap, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldtau (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 27) - (((((Expr.var 19) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 26)) - (((Expr.var 26) * (Expr.var 15)) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newtau (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 26) - (((((Expr.var 18) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 12).head? = some (oldtau p) := by rfl

theorem new_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 11).head? = some (newtau p) := by rfl

theorem tau_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldtau p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newtau p).evalRing (fun j => ι (v j)) := by
  simp [oldtau, newtau, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, hp0, map_add, map_mul, pow_two]

end DiophantineConsistency.Sign32Substitution04

#print axioms DiophantineConsistency.Sign32Substitution04.old_N1_row
#print axioms DiophantineConsistency.Sign32Substitution04.new_N1_row
#print axioms DiophantineConsistency.Sign32Substitution04.N1_eval
#print axioms DiophantineConsistency.Sign32Substitution04.old_gap_row
#print axioms DiophantineConsistency.Sign32Substitution04.new_gap_row
#print axioms DiophantineConsistency.Sign32Substitution04.gap_eval
#print axioms DiophantineConsistency.Sign32Substitution04.old_tau_row
#print axioms DiophantineConsistency.Sign32Substitution04.new_tau_row
#print axioms DiophantineConsistency.Sign32Substitution04.tau_eval
