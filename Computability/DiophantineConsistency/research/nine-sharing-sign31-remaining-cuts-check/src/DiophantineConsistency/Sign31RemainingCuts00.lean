import DiophantineConsistency.Sign31FirstCut

/-! UNCOMPILED bounded reindexing identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q3_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (SharingSeed32Sextic.firstResidual p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) =
      (SharingSeed31Sextic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [SharingSeed32Sextic.firstResidual, SharingSeed31Sextic.firstResidual,
    Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant]

def oldX (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 16) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

def newX (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 16) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

theorem old_X_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 0).head? = some (oldX p) := by rfl

theorem new_X_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 0).head? = some (newX p) := by rfl

theorem X_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldX p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newX p).evalRing (fun j => ι (v j)) := by
  simp [oldX, newX, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldY (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 17) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

def newY (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 17) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

theorem old_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 1).head? = some (oldY p) := by rfl

theorem new_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 1).head? = some (newY p) := by rfl

theorem Y_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldY p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newY p).evalRing (fun j => ι (v j)) := by
  simp [oldY, newY, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 18) - ((Expr.var 16) * (Expr.var 17)))

def newE (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 18) - ((Expr.var 16) * (Expr.var 17)))

theorem old_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 2).head? = some (oldE p) := by rfl

theorem new_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 2).head? = some (newE p) := by rfl

theorem E_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldE p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newE p).evalRing (fun j => ι (v j)) := by
  simp [oldE, newE, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldkY (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 19) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 17)))

def newkY (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 19) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 17)))

theorem old_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 3).head? = some (oldkY p) := by rfl

theorem new_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 3).head? = some (newkY p) := by rfl

theorem kY_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldkY p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newkY p).evalRing (fun j => ι (v j)) := by
  simp [oldkY, newkY, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldell (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 20) - ((Expr.var 18) * (Expr.var 19)))

def newell (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 20) - ((Expr.var 18) * (Expr.var 19)))

theorem old_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 4).head? = some (oldell p) := by rfl

theorem new_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 4).head? = some (newell p) := by rfl

theorem ell_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldell p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newell p).evalRing (fun j => ι (v j)) := by
  simp [oldell, newell, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldDelta (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 21) - ((((Expr.var 18) + (Expr.var 17)) * ((Expr.var 18) + (Expr.var 17))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ)))))

def newDelta (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 21) - ((((Expr.var 18) + (Expr.var 17)) * ((Expr.var 18) + (Expr.var 17))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ)))))

theorem old_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 5).head? = some (oldDelta p) := by rfl

theorem new_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 5).head? = some (newDelta p) := by rfl

theorem Delta_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldDelta p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newDelta p).evalRing (fun j => ι (v j)) := by
  simp [oldDelta, newDelta, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldmainRoot (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 22) - (((Expr.var 16) + (((Expr.var 18) + (Expr.var 17)) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ))))))

def newmainRoot (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 22) - (((Expr.var 16) + (((Expr.var 18) + (Expr.var 17)) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ))))))

theorem old_mainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 6).head? = some (oldmainRoot p) := by rfl

theorem new_mainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 6).head? = some (newmainRoot p) := by rfl

theorem mainRoot_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldmainRoot p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newmainRoot p).evalRing (fun j => ι (v j)) := by
  simp [oldmainRoot, newmainRoot, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldc2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 23) - (((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newc2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 23) - (((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_c2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 7).head? = some (oldc2 p) := by rfl

theorem new_c2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 7).head? = some (newc2 p) := by rfl

theorem c2_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldc2 p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldc2, newc2, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldDc2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 24) - ((Expr.var 21) * (Expr.var 23)))

def newDc2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 24) - ((Expr.var 21) * (Expr.var 23)))

theorem old_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 8).head? = some (oldDc2 p) := by rfl

theorem new_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 8).head? = some (newDc2 p) := by rfl

theorem Dc2_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldDc2 p).evalRing (fun j => ι (Sign31FirstCut.lift v j)) = (newDc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldDc2, newDc2, Sign31FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign31RemainingCuts

#print axioms DiophantineConsistency.Sign31RemainingCuts.q3_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.X_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.Y_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.E_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.kY_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.ell_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.Delta_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.mainRoot_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.c2_eval
#print axioms DiophantineConsistency.Sign31RemainingCuts.Dc2_eval
