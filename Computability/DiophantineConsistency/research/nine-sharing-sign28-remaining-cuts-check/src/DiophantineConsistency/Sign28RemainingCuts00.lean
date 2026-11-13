import DiophantineConsistency.Sign28FirstCuts02

/-! UNCOMPILED bounded reindexing identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q3_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (SharingSeed31Sextic.firstResidual p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) =
      (SharingSeed28Sextic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [SharingSeed31Sextic.firstResidual, SharingSeed28Sextic.firstResidual,
    Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant]

def oldY (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 17) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

def newY (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

theorem old_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 1).head? = some (oldY p) := by rfl

theorem new_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 0).head? = some (newY p) := by rfl

theorem Y_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldY p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newY p).evalRing (fun j => ι (v j)) := by
  simp [oldY, newY, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldkY (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 19) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 17)))

def newkY (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

theorem old_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 3).head? = some (oldkY p) := by rfl

theorem new_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 2).head? = some (newkY p) := by rfl

theorem kY_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldkY p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newkY p).evalRing (fun j => ι (v j)) := by
  simp [oldkY, newkY, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldell (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 20) - ((Expr.var 18) * (Expr.var 19)))

def newell (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

theorem old_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 4).head? = some (oldell p) := by rfl

theorem new_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 3).head? = some (newell p) := by rfl

theorem ell_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldell p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newell p).evalRing (fun j => ι (v j)) := by
  simp [oldell, newell, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldDelta (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 21) - ((((Expr.var 18) + (Expr.var 17)) * ((Expr.var 18) + (Expr.var 17))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ)))))

def newDelta (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))

theorem old_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 5).head? = some (oldDelta p) := by rfl

theorem new_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 4).head? = some (newDelta p) := by rfl

theorem Delta_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldDelta p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newDelta p).evalRing (fun j => ι (v j)) := by
  simp [oldDelta, newDelta, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldN1 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((Expr.var 22) * (Expr.var 22)) - (Expr.var 24)) - (Expr.constant (1 : ℤ)))

def newN1 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((Expr.var 21) * (Expr.var 21)) - (Expr.var 22)) - (Expr.constant (1 : ℤ)))

theorem old_N1_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 9).head? = some (oldN1 p) := by rfl

theorem new_N1_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 7).head? = some (newN1 p) := by rfl

theorem N1_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldN1 p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newN1 p).evalRing (fun j => ι (v j)) := by
  simp [oldN1, newN1, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldgap (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 25) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

def newgap (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 23) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

theorem old_gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 10).head? = some (oldgap p) := by rfl

theorem new_gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 8).head? = some (newgap p) := by rfl

theorem gap_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldgap p).evalRing (fun j => ι (Sign28FirstCuts.lift beta v j)) = (newgap p).evalRing (fun j => ι (v j)) := by
  simp [oldgap, newgap, Sign28FirstCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign28RemainingCuts

#print axioms DiophantineConsistency.Sign28RemainingCuts.q3_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.Y_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.kY_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.ell_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.Delta_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.N1_eval
#print axioms DiophantineConsistency.Sign28RemainingCuts.gap_eval
