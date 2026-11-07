import DiophantineConsistency.Sign32Substitution06

/-! UNCOMPILED: final remaining substitution identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution07
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldnormalizedS2 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 32) - ((Expr.var 31) * (Expr.var 31)))

def newnormalizedS2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 31) - ((Expr.var 30) * (Expr.var 30)))

theorem old_normalizedS2_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 19).head? = some (oldnormalizedS2 p) := by rfl

theorem new_normalizedS2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 18).head? = some (newnormalizedS2 p) := by rfl

theorem normalizedS2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldnormalizedS2 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newnormalizedS2 p).evalRing (fun j => ι (v j)) := by
  simp [oldnormalizedS2, newnormalizedS2, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 33) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 30) * (Expr.var 30))))

def newV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 32) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 29) * (Expr.var 29))))

theorem old_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 20).head? = some (oldV2minusY2 p) := by rfl

theorem new_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 19).head? = some (newV2minusY2 p) := by rfl

theorem V2minusY2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldV2minusY2 p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newV2minusY2 p).evalRing (fun j => ι (v j)) := by
  simp [oldV2minusY2, newV2minusY2, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldNa (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 32) * (Expr.var 33))) - (Expr.constant (1 : ℤ)))

def newNa (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 31) * (Expr.var 32))) - (Expr.constant (1 : ℤ)))

theorem old_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 21).head? = some (oldNa p) := by rfl

theorem new_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 20).head? = some (newNa p) := by rfl

theorem Na_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldNa p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newNa p).evalRing (fun j => ι (v j)) := by
  simp [oldNa, newNa, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldscaledNs (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((((Expr.var 22) * (Expr.var 28)) - (Expr.var 32)) - (Expr.var 22))

def newscaledNs (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((Expr.var 21) * (Expr.var 27)) - (Expr.var 31)) - (Expr.var 21))

theorem old_scaledNs_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 22).head? = some (oldscaledNs p) := by rfl

theorem new_scaledNs_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 21).head? = some (newscaledNs p) := by rfl

theorem scaledNs_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldscaledNs p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newscaledNs p).evalRing (fun j => ι (v j)) := by
  simp [oldscaledNs, newscaledNs, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign32Substitution07

#print axioms DiophantineConsistency.Sign32Substitution07.old_normalizedS2_row
#print axioms DiophantineConsistency.Sign32Substitution07.new_normalizedS2_row
#print axioms DiophantineConsistency.Sign32Substitution07.normalizedS2_eval
#print axioms DiophantineConsistency.Sign32Substitution07.old_V2minusY2_row
#print axioms DiophantineConsistency.Sign32Substitution07.new_V2minusY2_row
#print axioms DiophantineConsistency.Sign32Substitution07.V2minusY2_eval
#print axioms DiophantineConsistency.Sign32Substitution07.old_Na_row
#print axioms DiophantineConsistency.Sign32Substitution07.new_Na_row
#print axioms DiophantineConsistency.Sign32Substitution07.Na_eval
#print axioms DiophantineConsistency.Sign32Substitution07.old_scaledNs_row
#print axioms DiophantineConsistency.Sign32Substitution07.new_scaledNs_row
#print axioms DiophantineConsistency.Sign32Substitution07.scaledNs_eval
