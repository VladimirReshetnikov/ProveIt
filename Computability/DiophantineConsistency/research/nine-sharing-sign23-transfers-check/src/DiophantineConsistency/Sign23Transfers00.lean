import DiophantineConsistency.Sign23Coordinate

/-! SOURCE-ONLY: Delta substitution transfers; no Lean compilation claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldY (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 15) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))))

def newY (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 15) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))))

theorem old_Y_row (p : Fin 4 → ℤ) :
    SharingSeed24Octic.firstResidual p = oldY p := by rfl

theorem new_Y_row (p : Fin 4 → ℤ) :
    SharingSeed23Octic.firstResidual p = newY p := by rfl

theorem Y_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldY p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newY p).evalRing (fun j => ι (v j)) := by
  simp [oldY, newY, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 16) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

def newE (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 16) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

theorem old_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 0).head? = some (oldE p) := by rfl

theorem new_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 0).head? = some (newE p) := by rfl

theorem E_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldE p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newE p).evalRing (fun j => ι (v j)) := by
  simp [oldE, newE, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

def oldkY (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 17) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

def newkY (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 17) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

theorem old_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 1).head? = some (oldkY p) := by rfl

theorem new_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 1).head? = some (newkY p) := by rfl

theorem kY_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldkY p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newkY p).evalRing (fun j => ι (v j)) := by
  simp [oldkY, newkY, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

def oldmain_root (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  (((Expr.var 19) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 16) + (Expr.var 15)) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ))))))

def newmain_root (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  (((Expr.var 18) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 16) + (Expr.var 15)) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ))))))

theorem old_main_root_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 3).head? = some (oldmain_root p) := by rfl

theorem new_main_root_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 2).head? = some (newmain_root p) := by rfl

theorem main_root_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldmain_root p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newmain_root p).evalRing (fun j => ι (v j)) := by
  simp [oldmain_root, newmain_root, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

def oldDc2 (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  (((Expr.var 19) * ((Expr.var 19) + (Expr.constant (2 : ℤ)))) - ((Expr.var 18) * (((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

def newDc2 (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  (((Expr.var 18) * ((Expr.var 18) + (Expr.constant (2 : ℤ)))) - (((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))) * (((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

theorem old_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 4).head? = some (oldDc2 p) := by rfl

theorem new_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 3).head? = some (newDc2 p) := by rfl

theorem Dc2_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldDc2 p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newDc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldDc2, newDc2, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

def oldtau (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 20) - (((((Expr.var 16) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newtau (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 19) - (((((Expr.var 16) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 5).head? = some (oldtau p) := by rfl

theorem new_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 4).head? = some (newtau p) := by rfl

theorem tau_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldtau p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newtau p).evalRing (fun j => ι (v j)) := by
  simp [oldtau, newtau, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

def oldN0 (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((((Expr.var 20) * (Expr.var 20)) - (((Expr.var 16) * (Expr.var 17)) * (((Expr.var 16) * (Expr.var 17)) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newN0 (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((((Expr.var 19) * (Expr.var 19)) - (((Expr.var 16) * (Expr.var 17)) * (((Expr.var 16) * (Expr.var 17)) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 6).head? = some (oldN0 p) := by rfl

theorem new_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 5).head? = some (newN0 p) := by rfl

theorem N0_eval (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    (oldN0 p).evalRing (fun j => ι (Sign23Coordinate.lift v j)) =
      (newN0 p).evalRing (fun j => ι (v j)) := by
  simp [oldN0, newN0, Sign23Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

end DiophantineConsistency.Sign23Transfers
#print axioms DiophantineConsistency.Sign23Transfers.Y_eval
#print axioms DiophantineConsistency.Sign23Transfers.E_eval
#print axioms DiophantineConsistency.Sign23Transfers.kY_eval
#print axioms DiophantineConsistency.Sign23Transfers.main_root_eval
#print axioms DiophantineConsistency.Sign23Transfers.Dc2_eval
#print axioms DiophantineConsistency.Sign23Transfers.tau_eval
#print axioms DiophantineConsistency.Sign23Transfers.N0_eval
