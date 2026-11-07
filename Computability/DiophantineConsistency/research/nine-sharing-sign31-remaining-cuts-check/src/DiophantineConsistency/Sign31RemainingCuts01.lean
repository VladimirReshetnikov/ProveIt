import DiophantineConsistency.Sign31RemainingCuts00

/-! UNCOMPILED bounded reindexing identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldN1 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((Expr.var 22) * (Expr.var 22)) - (Expr.var 24)) - (Expr.constant (1 : ℤ)))

def newN1 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((Expr.var 22) * (Expr.var 22)) - (Expr.var 24)) - (Expr.constant (1 : ℤ)))

theorem old_N1_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 9).head? = some (oldN1 p) := by rfl

theorem new_N1_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 9).head? = some (newN1 p) := by rfl

theorem N1_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldN1 p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newN1 p).evalRing (fun j => ι (v j)) := by
  simp [oldN1, newN1, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldgap (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 25) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

def newgap (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 25) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

theorem old_gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 10).head? = some (oldgap p) := by rfl

theorem new_gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 10).head? = some (newgap p) := by rfl

theorem gap_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldgap p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newgap p).evalRing (fun j => ι (v j)) := by
  simp [oldgap, newgap, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldtau (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 26) - (((((Expr.var 18) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newtau (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 26) - (((((Expr.var 18) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 11).head? = some (oldtau p) := by rfl

theorem new_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 11).head? = some (newtau p) := by rfl

theorem tau_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldtau p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newtau p).evalRing (fun j => ι (v j)) := by
  simp [oldtau, newtau, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldN0 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((Expr.var 26) * (Expr.var 26)) - ((Expr.var 20) * ((Expr.var 20) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newN0 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((Expr.var 26) * (Expr.var 26)) - ((Expr.var 20) * ((Expr.var 20) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 12).head? = some (oldN0 p) := by rfl

theorem new_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 12).head? = some (newN0 p) := by rfl

theorem N0_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldN0 p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newN0 p).evalRing (fun j => ι (v j)) := by
  simp [oldN0, newN0, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldNt (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newNt (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 13).head? = some (oldNt p) := by rfl

theorem new_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 13).head? = some (newNt p) := by rfl

theorem Nt_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldNt p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newNt p).evalRing (fun j => ι (v j)) := by
  simp [oldNt, newNt, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldcTminusR (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 28) - (((((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newcTminusR (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 27) - (((((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 25)) - (((Expr.var 25) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 15).head? = some (oldcTminusR p) := by rfl

theorem new_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 14).head? = some (newcTminusR p) := by rfl

theorem cTminusR_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldcTminusR p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newcTminusR p).evalRing (fun j => ι (v j)) := by
  simp [oldcTminusR, newcTminusR, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldnormalizedS (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 30) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 24)))

def newnormalizedS (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 29) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 24)))

theorem old_normalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 17).head? = some (oldnormalizedS p) := by rfl

theorem new_normalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 16).head? = some (newnormalizedS p) := by rfl

theorem normalizedS_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldnormalizedS p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newnormalizedS p).evalRing (fun j => ι (v j)) := by
  simp [oldnormalizedS, newnormalizedS, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldnormalizedS2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 31) - ((Expr.var 30) * (Expr.var 30)))

def newnormalizedS2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 30) - ((Expr.var 29) * (Expr.var 29)))

theorem old_normalizedS2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 18).head? = some (oldnormalizedS2 p) := by rfl

theorem new_normalizedS2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 17).head? = some (newnormalizedS2 p) := by rfl

theorem normalizedS2_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldnormalizedS2 p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newnormalizedS2 p).evalRing (fun j => ι (v j)) := by
  simp [oldnormalizedS2, newnormalizedS2, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 32) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 29) * (Expr.var 29))))

def newV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 31) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 28) * (Expr.var 28))))

theorem old_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 19).head? = some (oldV2minusY2 p) := by rfl

theorem new_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 18).head? = some (newV2minusY2 p) := by rfl

theorem V2minusY2_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldV2minusY2 p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newV2minusY2 p).evalRing (fun j => ι (v j)) := by
  simp [oldV2minusY2, newV2minusY2, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldNa (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 31) * (Expr.var 32))) - (Expr.constant (1 : ℤ)))

def newNa (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 30) * (Expr.var 31))) - (Expr.constant (1 : ℤ)))

theorem old_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 20).head? = some (oldNa p) := by rfl

theorem new_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 19).head? = some (newNa p) := by rfl

theorem Na_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldNa p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newNa p).evalRing (fun j => ι (v j)) := by
  simp [oldNa, newNa, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign31RemainingCuts

#print axioms DiophantineConsistency.Sign31RemainingCuts.N1_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.gap_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.tau_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.N0_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.Nt_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.cTminusR_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.normalizedS_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.normalizedS2_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.V2minusY2_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.Na_eval
