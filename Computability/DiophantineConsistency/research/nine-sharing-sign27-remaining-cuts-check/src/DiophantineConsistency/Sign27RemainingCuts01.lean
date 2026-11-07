import DiophantineConsistency.Sign27RemainingCuts00

/-! SOURCE-ONLY: bounded unaffected residual reindexing. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldR11 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((Expr.var 24) * (Expr.var 24)) - ((Expr.var 19) * ((Expr.var 19) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newR11 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((((Expr.var 23) * (Expr.var 23)) - ((Expr.var 19) * ((Expr.var 19) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_R11_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 10).head? = some (oldR11 p) := by rfl

theorem new_R11_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 9).head? = some (newR11 p) := by rfl

theorem R11_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR11 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR11 p).evalRing (fun j => ι (v j)) := by
  simp [oldR11, newR11, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR12 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newR12 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_R12_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 11).head? = some (oldR12 p) := by rfl

theorem new_R12_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 10).head? = some (newR12 p) := by rfl

theorem R12_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR12 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR12 p).evalRing (fun j => ι (v j)) := by
  simp [oldR12, newR12, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR13 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 25) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 23)) - (((Expr.var 23) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newR13 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 24) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 22)) - (((Expr.var 22) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_R13_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 12).head? = some (oldR13 p) := by rfl

theorem new_R13_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 11).head? = some (newR13 p) := by rfl

theorem R13_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR13 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR13 p).evalRing (fun j => ι (v j)) := by
  simp [oldR13, newR13, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR14 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 26) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 25)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newR14 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 25) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 24)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_R14_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 13).head? = some (oldR14 p) := by rfl

theorem new_R14_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 12).head? = some (newR14 p) := by rfl

theorem R14_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR14 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR14 p).evalRing (fun j => ι (v j)) := by
  simp [oldR14, newR14, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR16 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 28) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 26) * (Expr.var 26))))

def newR16 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 27) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 25) * (Expr.var 25))))

theorem old_R16_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 15).head? = some (oldR16 p) := by rfl

theorem new_R16_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 14).head? = some (newR16 p) := by rfl

theorem R16_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR16 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR16 p).evalRing (fun j => ι (v j)) := by
  simp [oldR16, newR16, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR17 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 27) * (Expr.var 27)) * (Expr.var 28))) - (Expr.constant (1 : ℤ)))

def newR17 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 26) * (Expr.var 26)) * (Expr.var 27))) - (Expr.constant (1 : ℤ)))

theorem old_R17_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 16).head? = some (oldR17 p) := by rfl

theorem new_R17_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 15).head? = some (newR17 p) := by rfl

theorem R17_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR17 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR17 p).evalRing (fun j => ι (v j)) := by
  simp [oldR17, newR17, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR18 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((Expr.var 20) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 27) * (Expr.var 27))) - (Expr.var 20))

def newR18 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((((Expr.var 20) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 26) * (Expr.var 26))) - (Expr.var 20))

theorem old_R18_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 17).head? = some (oldR18 p) := by rfl

theorem new_R18_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 16).head? = some (newR18 p) := by rfl

theorem R18_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldR18 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newR18 p).evalRing (fun j => ι (v j)) := by
  simp [oldR18, newR18, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign27RemainingCuts
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R11_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R11_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R11_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R12_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R12_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R12_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R13_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R13_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R13_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R14_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R14_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R14_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R16_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R16_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R16_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R17_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R17_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R17_eval
#print axioms DiophantineConsistency.Sign27RemainingCuts.old_R18_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.new_R18_row
#print axioms DiophantineConsistency.Sign27RemainingCuts.R18_eval
