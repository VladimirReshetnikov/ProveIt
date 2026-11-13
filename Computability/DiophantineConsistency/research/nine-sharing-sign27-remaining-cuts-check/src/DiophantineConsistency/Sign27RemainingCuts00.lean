import DiophantineConsistency.Sign27FirstCut

/-! SOURCE-ONLY: bounded unaffected residual reindexing. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldR01 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

def newR01 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

theorem old_R01_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 0).head? = some (oldR01 p) := by rfl

theorem new_R01_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 0).head? = some (newR01 p) := by rfl

theorem R01_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR01 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR01 p).evalRing (fun j => ι (v j)) := by
  simp [oldR01, newR01, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR02 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

def newR02 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

theorem old_R02_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 1).head? = some (oldR02 p) := by rfl

theorem new_R02_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 1).head? = some (newR02 p) := by rfl

theorem R02_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR02 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR02 p).evalRing (fun j => ι (v j)) := by
  simp [oldR02, newR02, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR03 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

def newR03 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

theorem old_R03_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 2).head? = some (oldR03 p) := by rfl

theorem new_R03_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 2).head? = some (newR03 p) := by rfl

theorem R03_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR03 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR03 p).evalRing (fun j => ι (v j)) := by
  simp [oldR03, newR03, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR04 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

def newR04 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

theorem old_R04_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 3).head? = some (oldR04 p) := by rfl

theorem new_R04_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 3).head? = some (newR04 p) := by rfl

theorem R04_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR04 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR04 p).evalRing (fun j => ι (v j)) := by
  simp [oldR04, newR04, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR05 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))

def newR05 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))

theorem old_R05_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 4).head? = some (oldR05 p) := by rfl

theorem new_R05_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 4).head? = some (newR05 p) := by rfl

theorem R05_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR05 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR05 p).evalRing (fun j => ι (v j)) := by
  simp [oldR05, newR05, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR09 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 23) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

def newR09 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 22) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

theorem old_R09_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 8).head? = some (oldR09 p) := by rfl

theorem new_R09_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 7).head? = some (newR09 p) := by rfl

theorem R09_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR09 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR09 p).evalRing (fun j => ι (v j)) := by
  simp [oldR09, newR09, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR10 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 24) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 23)) - (((Expr.var 23) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newR10 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 23) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 22)) - (((Expr.var 22) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_R10_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 9).head? = some (oldR10 p) := by rfl

theorem new_R10_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 8).head? = some (newR10 p) := by rfl

theorem R10_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR10 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR10 p).evalRing (fun j => ι (v j)) := by
  simp [oldR10, newR10, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign27RemainingCuts
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R01_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R01_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R01_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R02_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R02_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R02_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R03_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R03_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R03_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R04_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R04_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R04_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R05_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R05_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R05_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R09_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R09_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R09_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R10_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R10_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R10_eval
