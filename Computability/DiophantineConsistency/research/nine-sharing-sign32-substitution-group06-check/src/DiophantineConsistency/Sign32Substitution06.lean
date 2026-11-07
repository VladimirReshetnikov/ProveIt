import DiophantineConsistency.Sign32Substitution05

/-! UNCOMPILED: cTminusR/V/normalizedS substitution; cTminusR uses q². -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution06
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldcTminusR (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 29) - (((((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 26)) - (((Expr.var 26) * (Expr.var 15)) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newcTminusR (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 28) - (((((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 16).head? = some (oldcTminusR p) := by rfl

theorem new_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 15).head? = some (newcTminusR p) := by rfl

theorem cTminusR_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldcTminusR p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newcTminusR p).evalRing (fun j => ι (v j)) := by
  simp [oldcTminusR, newcTminusR, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, hp0, map_add, map_mul, pow_two]

def oldV (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 30) - (((Expr.var 28) * (Expr.var 29)) - ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newV (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 29) - (((Expr.var 27) * (Expr.var 28)) - ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 17).head? = some (oldV p) := by rfl

theorem new_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 16).head? = some (newV p) := by rfl

theorem V_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldV p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newV p).evalRing (fun j => ι (v j)) := by
  simp [oldV, newV, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldnormalizedS (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 31) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 25)))

def newnormalizedS (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 30) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 24)))

theorem old_normalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 18).head? = some (oldnormalizedS p) := by rfl

theorem new_normalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 17).head? = some (newnormalizedS p) := by rfl

theorem normalizedS_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldnormalizedS p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newnormalizedS p).evalRing (fun j => ι (v j)) := by
  simp [oldnormalizedS, newnormalizedS, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign32Substitution06

#print axioms DiophantineConsistency.Sign32Substitution06.old_cTminusR_row
#print axioms DiophantineConsistency.Sign32Substitution06.new_cTminusR_row
#print axioms DiophantineConsistency.Sign32Substitution06.cTminusR_eval
#print axioms DiophantineConsistency.Sign32Substitution06.old_V_row
#print axioms DiophantineConsistency.Sign32Substitution06.new_V_row
#print axioms DiophantineConsistency.Sign32Substitution06.V_eval
#print axioms DiophantineConsistency.Sign32Substitution06.old_normalizedS_row
#print axioms DiophantineConsistency.Sign32Substitution06.new_normalizedS_row
#print axioms DiophantineConsistency.Sign32Substitution06.normalizedS_eval
