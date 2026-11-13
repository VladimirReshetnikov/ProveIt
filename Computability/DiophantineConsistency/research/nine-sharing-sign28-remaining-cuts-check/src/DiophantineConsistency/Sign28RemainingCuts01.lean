import DiophantineConsistency.Sign28RemainingCuts00

/-! UNCOMPILED bounded reindexing identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldtau (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 26) - (((((Expr.var 18) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newtau (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 24) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 23)) - (((Expr.var 23) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 11).head? = some (oldtau p) := by rfl

theorem new_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 9).head? = some (newtau p) := by rfl

theorem tau_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldtau p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newtau p).evalRing (fun j => ι (v j)) := by
  simp [oldtau, newtau, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldN0 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((Expr.var 26) * (Expr.var 26)) - ((Expr.var 20) * ((Expr.var 20) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newN0 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((Expr.var 24) * (Expr.var 24)) - ((Expr.var 19) * ((Expr.var 19) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 12).head? = some (oldN0 p) := by rfl

theorem new_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 10).head? = some (newN0 p) := by rfl

theorem N0_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldN0 p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newN0 p).evalRing (fun j => ι (v j)) := by
  simp [oldN0, newN0, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldNt (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newNt (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 13).head? = some (oldNt p) := by rfl

theorem new_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 11).head? = some (newNt p) := by rfl

theorem Nt_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldNt p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newNt p).evalRing (fun j => ι (v j)) := by
  simp [oldNt, newNt, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldcTminusR (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 27) - (((((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newcTminusR (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 25) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 23)) - (((Expr.var 23) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 14).head? = some (oldcTminusR p) := by rfl

theorem new_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 12).head? = some (newcTminusR p) := by rfl

theorem cTminusR_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldcTminusR p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newcTminusR p).evalRing (fun j => ι (v j)) := by
  simp [oldcTminusR, newcTminusR, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldV (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 28) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 27)) - ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newV (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 26) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 25)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 15).head? = some (oldV p) := by rfl

theorem new_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 13).head? = some (newV p) := by rfl

theorem V_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldV p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newV p).evalRing (fun j => ι (v j)) := by
  simp [oldV, newV, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldnormalizedS (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 29) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 24)))

def newnormalizedS (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 27) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 22)))

theorem old_normalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 16).head? = some (oldnormalizedS p) := by rfl

theorem new_normalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 14).head? = some (newnormalizedS p) := by rfl

theorem normalizedS_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldnormalizedS p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newnormalizedS p).evalRing (fun j => ι (v j)) := by
  simp [oldnormalizedS, newnormalizedS, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 31) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 28) * (Expr.var 28))))

def newV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 28) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 26) * (Expr.var 26))))

theorem old_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 18).head? = some (oldV2minusY2 p) := by rfl

theorem new_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 15).head? = some (newV2minusY2 p) := by rfl

theorem V2minusY2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldV2minusY2 p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newV2minusY2 p).evalRing (fun j => ι (v j)) := by
  simp [oldV2minusY2, newV2minusY2, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign28RemainingCuts

#print axioms DiophantineConsistency.Sign28RemainingCuts.tau_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.N0_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.Nt_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.cTminusR_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.V_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.normalizedS_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.V2minusY2_eval
