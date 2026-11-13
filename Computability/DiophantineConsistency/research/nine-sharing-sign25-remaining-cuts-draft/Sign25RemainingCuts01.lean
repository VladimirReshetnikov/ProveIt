import DiophantineConsistency.Sign25RemainingCuts00

/-! SOURCE-ONLY: unchanged residual transfers; no zero bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldR10 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))
def newR10 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))
theorem old_R10_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 9).head? = some (oldR10 p) := by rfl
theorem new_R10_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 8).head? = some (newR10 p) := by rfl
theorem R10_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR10 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR10 p).evalRing (fun j => ι (v j)) := by
  simp [oldR10, newR10, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR11 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 23) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))
def newR11 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 22) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))
theorem old_R11_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 10).head? = some (oldR11 p) := by rfl
theorem new_R11_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 9).head? = some (newR11 p) := by rfl
theorem R11_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR11 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR11 p).evalRing (fun j => ι (v j)) := by
  simp [oldR11, newR11, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR12 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 24) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 23)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))
def newR12 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 23) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 22)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))
theorem old_R12_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 11).head? = some (oldR12 p) := by rfl
theorem new_R12_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 10).head? = some (newR12 p) := by rfl
theorem R12_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR12 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR12 p).evalRing (fun j => ι (v j)) := by
  simp [oldR12, newR12, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR13 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 25) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 21) * ((Expr.var 21) + (Expr.constant (2 : ℤ))))))
def newR13 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 24) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 20) * ((Expr.var 20) + (Expr.constant (2 : ℤ))))))
theorem old_R13_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 12).head? = some (oldR13 p) := by rfl
theorem new_R13_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 11).head? = some (newR13 p) := by rfl
theorem R13_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR13 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR13 p).evalRing (fun j => ι (v j)) := by
  simp [oldR13, newR13, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR14 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 26) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 24) * (Expr.var 24))))
def newR14 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 25) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 23) * (Expr.var 23))))
theorem old_R14_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 13).head? = some (oldR14 p) := by rfl
theorem new_R14_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 12).head? = some (newR14 p) := by rfl
theorem R14_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR14 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR14 p).evalRing (fun j => ι (v j)) := by
  simp [oldR14, newR14, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR15 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 25) * (Expr.var 25)) * (Expr.var 26))) - (Expr.constant (1 : ℤ)))
def newR15 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 24) * (Expr.var 24)) * (Expr.var 25))) - (Expr.constant (1 : ℤ)))
theorem old_R15_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 14).head? = some (oldR15 p) := by rfl
theorem new_R15_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 13).head? = some (newR15 p) := by rfl
theorem R15_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR15 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR15 p).evalRing (fun j => ι (v j)) := by
  simp [oldR15, newR15, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR16 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((((Expr.var 20) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 25) * (Expr.var 25))) - (Expr.var 20))
def newR16 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((((Expr.var 19) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 24) * (Expr.var 24))) - (Expr.var 19))
theorem old_R16_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 15).head? = some (oldR16 p) := by rfl
theorem new_R16_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 14).head? = some (newR16 p) := by rfl
theorem R16_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR16 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR16 p).evalRing (fun j => ι (v j)) := by
  simp [oldR16, newR16, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]
end DiophantineConsistency.Sign25RemainingCuts
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R10_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R10_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R10_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R11_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R11_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R11_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R12_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R12_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R12_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R13_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R13_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R13_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R14_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R14_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R14_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R15_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R15_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R15_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R16_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R16_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R16_eval
