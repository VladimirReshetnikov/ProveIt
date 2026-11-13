import DiophantineConsistency.Sign22Coordinate

/-! SOURCE-ONLY: kY substitution transfers; no Lean compilation claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldY (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 15) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))))

def newY (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  ((Expr.var 15) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))))

theorem old_Y_row (p : Fin 4 → ℤ) :
    SharingSeed23Octic.firstResidual p = oldY p := by rfl

theorem new_Y_row (p : Fin 4 → ℤ) :
    SharingSeed22Dodecic.firstResidual p = newY p := by rfl

theorem Y_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldY p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newY p).evalRing (fun j => ι (v j)) := by
  simp [oldY, newY, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 16) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

def newE (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  ((Expr.var 16) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

theorem old_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 0).head? = some (oldE p) := by rfl

theorem new_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 0).head? = some (newE p) := by rfl

theorem E_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldE p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newE p).evalRing (fun j => ι (v j)) := by
  simp [oldE, newE, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

def oldmain_root (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  (((Expr.var 18) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 16) + (Expr.var 15)) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ))))))

def newmain_root (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  (((Expr.var 17) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 16) + (Expr.var 15)) * (((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ))))))

theorem old_main_root_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 2).head? = some (oldmain_root p) := by rfl

theorem new_main_root_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 1).head? = some (newmain_root p) := by rfl

theorem main_root_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldmain_root p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newmain_root p).evalRing (fun j => ι (v j)) := by
  simp [oldmain_root, newmain_root, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

def oldDc2 (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  (((Expr.var 18) * ((Expr.var 18) + (Expr.constant (2 : ℤ)))) - (((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))) * (((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

def newDc2 (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  (((Expr.var 17) * ((Expr.var 17) + (Expr.constant (2 : ℤ)))) - (((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))) * ((((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * (((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

theorem old_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 3).head? = some (oldDc2 p) := by rfl

theorem new_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 2).head? = some (newDc2 p) := by rfl

theorem Dc2_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldDc2 p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newDc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldDc2, newDc2, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

def oldtau (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 19) - (((((Expr.var 16) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newtau (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  ((Expr.var 18) - (((((Expr.var 16) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 4).head? = some (oldtau p) := by rfl

theorem new_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 3).head? = some (newtau p) := by rfl

theorem tau_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldtau p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newtau p).evalRing (fun j => ι (v j)) := by
  simp [oldtau, newtau, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

def oldN0 (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((((Expr.var 19) * (Expr.var 19)) - (((Expr.var 16) * (Expr.var 17)) * (((Expr.var 16) * (Expr.var 17)) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newN0 (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  ((((Expr.var 18) * (Expr.var 18)) - (((Expr.var 16) * ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15))) * (((Expr.var 16) * ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 5).head? = some (oldN0 p) := by rfl

theorem new_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 4).head? = some (newN0 p) := by rfl

theorem N0_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldN0 p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newN0 p).evalRing (fun j => ι (v j)) := by
  simp [oldN0, newN0, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

def oldNt (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newNt (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 6).head? = some (oldNt p) := by rfl

theorem new_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 5).head? = some (newNt p) := by rfl

theorem Nt_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    (oldNt p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =
      (newNt p).evalRing (fun j => ι (v j)) := by
  simp [oldNt, newNt, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

end DiophantineConsistency.Sign22Transfers
#print axioms DiophantineConsistency.Sign22Transfers.Y_eval
#print axioms DiophantineConsistency.Sign22Transfers.E_eval
#print axioms DiophantineConsistency.Sign22Transfers.main_root_eval
#print axioms DiophantineConsistency.Sign22Transfers.Dc2_eval
#print axioms DiophantineConsistency.Sign22Transfers.tau_eval
#print axioms DiophantineConsistency.Sign22Transfers.N0_eval
#print axioms DiophantineConsistency.Sign22Transfers.Nt_eval
