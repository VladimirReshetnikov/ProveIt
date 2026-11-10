import DiophantineConsistency.Sign24Coordinate

/-! SOURCE-ONLY: q3 substitution transfers; no Lean compilation claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldY (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

def newY (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 15) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))))

theorem old_Y_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 0).head? = some (oldY p) := by rfl

theorem new_Y_row (p : Fin 4 → ℤ) :
    SharingSeed24Octic.firstResidual p = newY p := by rfl

theorem Y_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldY p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newY p).evalRing (fun j => ι (v j)) := by
  simp [oldY, newY, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

def newE (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 16) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

theorem old_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 1).head? = some (oldE p) := by rfl

theorem new_E_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 0).head? = some (newE p) := by rfl

theorem E_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldE p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newE p).evalRing (fun j => ι (v j)) := by
  simp [oldE, newE, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldkY (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

def newkY (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 17) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

theorem old_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 2).head? = some (oldkY p) := by rfl

theorem new_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 1).head? = some (newkY p) := by rfl

theorem kY_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldkY p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newkY p).evalRing (fun j => ι (v j)) := by
  simp [oldkY, newkY, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldDelta (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 19) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))

def newDelta (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 18) - ((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))))

theorem old_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 3).head? = some (oldDelta p) := by rfl

theorem new_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 2).head? = some (newDelta p) := by rfl

theorem Delta_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldDelta p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newDelta p).evalRing (fun j => ι (v j)) := by
  simp [oldDelta, newDelta, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldmain_root (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  (((Expr.var 20) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))

def newmain_root (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  (((Expr.var 19) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 16) + (Expr.var 15)) * ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ))))))

theorem old_main_root_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 4).head? = some (oldmain_root p) := by rfl

theorem new_main_root_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 3).head? = some (newmain_root p) := by rfl

theorem main_root_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldmain_root p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newmain_root p).evalRing (fun j => ι (v j)) := by
  simp [oldmain_root, newmain_root, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

end DiophantineConsistency.Sign24Transfers
#print axioms DiophantineConsistency.Sign24Transfers.Y_eval
#print axioms DiophantineConsistency.Sign24Transfers.E_eval
#print axioms DiophantineConsistency.Sign24Transfers.kY_eval
#print axioms DiophantineConsistency.Sign24Transfers.Delta_eval
#print axioms DiophantineConsistency.Sign24Transfers.main_root_eval
