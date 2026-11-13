import DiophantineConsistency.Sign25FirstCut

/-! SOURCE-ONLY: unchanged residual transfers; no zero bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (SharingSeed26Sextic.firstResidual p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (SharingSeed25Octic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [SharingSeed26Sextic.firstResidual, SharingSeed25Octic.firstResidual,
    Sign25FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant]

def oldR01 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))
def newR01 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))
theorem old_R01_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 0).head? = some (oldR01 p) := by rfl
theorem new_R01_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 0).head? = some (newR01 p) := by rfl
theorem R01_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR01 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR01 p).evalRing (fun j => ι (v j)) := by
  simp [oldR01, newR01, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR02 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))
def newR02 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))
theorem old_R02_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 1).head? = some (oldR02 p) := by rfl
theorem new_R02_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 1).head? = some (newR02 p) := by rfl
theorem R02_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR02 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR02 p).evalRing (fun j => ι (v j)) := by
  simp [oldR02, newR02, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR03 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))
def newR03 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))
theorem old_R03_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 2).head? = some (oldR03 p) := by rfl
theorem new_R03_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 2).head? = some (newR03 p) := by rfl
theorem R03_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR03 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR03 p).evalRing (fun j => ι (v j)) := by
  simp [oldR03, newR03, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR05 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))
def newR05 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 19) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))
theorem old_R05_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 4).head? = some (oldR05 p) := by rfl
theorem new_R05_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 3).head? = some (newR05 p) := by rfl
theorem R05_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR05 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR05 p).evalRing (fun j => ι (v j)) := by
  simp [oldR05, newR05, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR06 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  (((Expr.var 21) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))
def newR06 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  (((Expr.var 20) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))
theorem old_R06_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 5).head? = some (oldR06 p) := by rfl
theorem new_R06_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 4).head? = some (newR06 p) := by rfl
theorem R06_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR06 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR06 p).evalRing (fun j => ι (v j)) := by
  simp [oldR06, newR06, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR07 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  (((Expr.var 21) * ((Expr.var 21) + (Expr.constant (2 : ℤ)))) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))
def newR07 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  (((Expr.var 20) * ((Expr.var 20) + (Expr.constant (2 : ℤ)))) - ((Expr.var 19) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))
theorem old_R07_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 6).head? = some (oldR07 p) := by rfl
theorem new_R07_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 5).head? = some (newR07 p) := by rfl
theorem R07_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR07 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR07 p).evalRing (fun j => ι (v j)) := by
  simp [oldR07, newR07, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldR08 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 22) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))
def newR08 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 21) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))
theorem old_R08_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 7).head? = some (oldR08 p) := by rfl
theorem new_R08_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 6).head? = some (newR08 p) := by rfl
theorem R08_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldR08 p).evalRing (fun j => ι (Sign25FirstCut.lift v j)) =
      (newR08 p).evalRing (fun j => ι (v j)) := by
  simp [oldR08, newR08, Sign25FirstCut.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]
end DiophantineConsistency.Sign25RemainingCuts
#print axioms DiophantineConsistency.Sign25RemainingCuts.first_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R01_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R01_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R01_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R02_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R02_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R02_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R03_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R03_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R03_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R05_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R05_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R05_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R06_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R06_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R06_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R07_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R07_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R07_eval
#print axioms DiophantineConsistency.Sign25RemainingCuts.old_R08_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.new_R08_row
#print axioms DiophantineConsistency.Sign25RemainingCuts.R08_eval
